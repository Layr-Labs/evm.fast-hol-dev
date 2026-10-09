import hashlib
import io
import json
from pathlib import Path
import tempfile
import shutil
import unittest
import subprocess
from unittest.mock import patch
import verify

class BoundaryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.candidate = Path(self.tmp.name)
        (self.candidate/'claim.json').write_text('{"K":"infinity"}')
        (self.candidate/'rom.bin').write_bytes(bytes([0xff, 0, 1]))
        (self.candidate/'certificate.art').write_text('untrusted proof bytes')

    def test_arbitrary_bytes_pass_only_preflight(self):
        self.assertEqual(verify.preflight(self.candidate)['rom_bytes'], 3)
        with patch.object(verify, 'check_trusted'), patch('builtins.print') as output:
            self.assertEqual(verify.main([str(self.candidate)]), 2)
        self.assertEqual(json.loads(output.call_args.args[0])['status'], 'incomplete')

    def test_extra_code_is_rejected(self):
        (self.candidate/'evil.sml').write_text('raise Fail "must never execute"')
        with self.assertRaises(verify.Rejected): verify.preflight(self.candidate)

    def test_symlink_rom_rejected(self):
        (self.candidate/'rom.bin').unlink()
        (self.candidate/'rom.bin').symlink_to('/etc/passwd')
        with self.assertRaises(OSError): verify.preflight(self.candidate)

    def test_boolean_score_rejected(self):
        (self.candidate/'claim.json').write_text('{"K":true}')
        with self.assertRaises(verify.Rejected): verify.preflight(self.candidate)

    def test_duplicate_score_rejected(self):
        (self.candidate/'claim.json').write_text('{"K":0,"K":"infinity"}')
        with self.assertRaises(verify.Rejected): verify.preflight(self.candidate)

    def test_negative_score_rejected(self):
        (self.candidate/'claim.json').write_text('{"K":-1}')
        with self.assertRaises(verify.Rejected): verify.preflight(self.candidate)

    def test_oversize_rom_rejected(self):
        with patch.object(verify, 'ROM_LIMIT', 2):
            with self.assertRaises(verify.Rejected): verify.preflight(self.candidate)

    def test_directory_in_place_of_proof_rejected(self):
        (self.candidate/'certificate.art').unlink()
        (self.candidate/'certificate.art').mkdir()
        with self.assertRaises((OSError, verify.Rejected)): verify.preflight(self.candidate)

    def test_frozen_literals_survive_candidate_replacement(self):
        frozen = verify.freeze(self.candidate)
        (self.candidate/'rom.bin').write_bytes(b'changed')
        (self.candidate/'claim.json').write_text('{"K":123}')
        (self.candidate/'certificate.art').write_bytes(b'changed proof')
        stream = io.StringIO()
        frozen.write_literals(stream)
        self.assertIn('255w;0w;1w', stream.getvalue())
        self.assertIn('submittedScore = initParams$Infinity', stream.getvalue())
        self.assertEqual(frozen.proof, b'untrusted proof bytes')
        self.assertEqual(frozen.report()['rom_sha256'], hashlib.sha256(bytes([255,0,1])).hexdigest())

    def test_score_is_regenerated_as_literal(self):
        (self.candidate/'claim.json').write_text(' { "K" : 123 } ')
        stream = io.StringIO()
        verify.freeze(self.candidate).write_literals(stream)
        self.assertIn('submittedScore = initParams$Finite 123', stream.getvalue())

    def test_score_syntax_injection_rejected(self):
        (self.candidate/'claim.json').write_text(json.dumps({'K':'0; new_axiom "oops"'}))
        with self.assertRaises(verify.Rejected): verify.freeze(self.candidate)

    def test_every_byte_is_literal_data(self):
        (self.candidate/'rom.bin').write_bytes(bytes(range(256)))
        stream = io.StringIO()
        verify.freeze(self.candidate).write_literals(stream)
        body = stream.getvalue().split('= [', 1)[1].split(']', 1)[0]
        self.assertEqual([int(x.strip()[:-1]) for x in body.split(';')], list(range(256)))

    def test_prepared_snapshot_copies_only_frozen_values(self):
        frozen = verify.freeze(self.candidate)
        (self.candidate/'rom.bin').write_bytes(b'replacement')
        destination = self.candidate/'prepared'
        verify.prepare_snapshot(frozen, destination)
        self.assertEqual((destination/'rom.bin').read_bytes(), frozen.rom)
        self.assertEqual((destination/'certificate.art').read_bytes(), frozen.proof)
        self.assertEqual(json.loads((destination/'claim.json').read_text()), {'K':'infinity'})
        self.assertIn('255w;0w;1w', (destination/'submissionLiteralsScript.sml').read_text())
        self.assertEqual(destination.stat().st_mode & 0o777, 0o700)
        with self.assertRaises(FileExistsError): verify.prepare_snapshot(frozen, destination)

    def trusted_tree(self):
        root = self.candidate/'trusted'
        (root/'verifier').mkdir(parents=True)
        (root/'challenge').mkdir()
        (root/'challenge/fixed.sml').write_text('fixed challenge')
        digest = hashlib.sha256(b'fixed challenge').hexdigest()
        (root/'verifier/trusted-files.json').write_text(json.dumps({'challenge/fixed.sml':digest}))
        (root/'provenance.json').write_text('{"cakeml":"pinned"}')
        return root

    def test_modified_challenge_rejected(self):
        root = self.trusted_tree()
        (root/'challenge/fixed.sml').write_text('participant replacement')
        with patch.object(verify, 'ROOT', root):
            with self.assertRaisesRegex(verify.Rejected, 'modified trusted'):
                verify.check_trusted()

    def test_injected_challenge_module_rejected(self):
        root = self.trusted_tree()
        (root/'challenge/extraScript.sml').write_text('untrusted code')
        with patch.object(verify, 'ROOT', root):
            with self.assertRaisesRegex(verify.Rejected, 'unexpected trusted file set'):
                verify.check_trusted()

    def test_wrong_dependency_pin_rejected(self):
        root = self.trusted_tree()
        with patch.object(verify, 'ROOT', root), patch('subprocess.check_output', return_value='wrong'):
            with self.assertRaisesRegex(verify.Rejected, 'pin differs'):
                verify.check_trusted()

class ReplayProcessTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.candidate = self.root/'candidate'
        self.candidate.mkdir()
        (self.candidate/'claim.json').write_text('{"K":"infinity"}')
        (self.candidate/'rom.bin').write_bytes(b'\0')
        (self.candidate/'certificate.art').write_bytes(b'untrusted')
        self.frozen = verify.freeze(self.candidate)
        build = self.root/'.build'
        build.mkdir()
        (build/'verifier.heap').write_bytes(b'mocked heap')
        (self.root/'verifier').mkdir()
        manifest = self.root/'verifier/trusted-files.json'
        manifest.write_text('{}')
        (self.root/'provenance.json').write_text('{"tested_hol":"pinned"}')
        (build/'verifier.json').write_text(json.dumps({
            'hol': str(self.root/'HOL'), 'hol_revision': 'pinned',
            'heap_sha256': verify.file_digest(build/'verifier.heap'),
            'manifest_sha256': verify.file_digest(manifest)}))
        self.work = self.root/'work'

    def run_replay(self, returncode=0, marker=None, timed_out=False):
        def child(command, **kwargs):
            if marker is not None:
                snapshot = Path(kwargs['env']['HOL_INIT_E_SNAPSHOT'])
                (snapshot/'verified').write_bytes(marker)
            if timed_out:
                raise subprocess.TimeoutExpired(command, kwargs['timeout'])
            return subprocess.CompletedProcess(command, returncode)
        with patch.object(verify.subprocess, 'run', side_effect=child):
            verify.replay_frozen(self.frozen, trusted=self.root, work=self.work)

    def report(self):
        return json.loads((self.work/'replay-process.json').read_text())

    def test_killed_child_rejected_even_with_exact_marker(self):
        with self.assertRaisesRegex(verify.Rejected, 'terminated by SIGTERM'):
            self.run_replay(returncode=-15, marker=b'VERIFIED\n')
        self.assertEqual(self.report()['returncode'], -15)
        self.assertEqual(self.report()['signal'], 'SIGTERM')
        self.assertFalse(self.report()['timed_out'])

    def test_nonzero_exit_rejected_even_with_exact_marker(self):
        with self.assertRaisesRegex(verify.Rejected, 'exited with status 7'):
            self.run_replay(returncode=7, marker=b'VERIFIED\n')
        self.assertEqual(self.report()['returncode'], 7)
        self.assertIsNone(self.report()['signal'])

    def test_zero_exit_requires_marker(self):
        with self.assertRaisesRegex(verify.Rejected, 'completion marker missing'):
            self.run_replay()
        self.assertEqual(self.report()['returncode'], 0)

    def test_zero_exit_requires_exact_marker_bytes(self):
        with self.assertRaisesRegex(verify.Rejected, 'incorrect completion marker'):
            self.run_replay(marker=b'VERIFIED\nextra')
        self.assertEqual(self.report()['returncode'], 0)

    def test_zero_exit_and_exact_marker_accept(self):
        self.run_replay(marker=b'VERIFIED\n')
        self.assertEqual(self.report()['returncode'], 0)
        self.assertFalse(self.report()['timed_out'])
        self.assertIsNone(self.report()['signal'])
        self.assertGreaterEqual(self.report()['wall_seconds'], 0)

    def test_timeout_rejected_even_with_exact_marker(self):
        with self.assertRaisesRegex(verify.Rejected, 'exceeded the time limit'):
            self.run_replay(marker=b'VERIFIED\n', timed_out=True)
        self.assertTrue(self.report()['timed_out'])
        self.assertIsNone(self.report()['returncode'])
        self.assertIsNone(self.report()['signal'])


class CommandTests(unittest.TestCase):
    setUp = BoundaryTests.setUp
    def test_local_replays_by_default(self):
        with patch.object(verify, 'check_trusted'), patch.object(verify, 'replay_frozen') as replay, patch('sys.stdout', new_callable=io.StringIO) as output:
            self.assertEqual(verify.main(['--local', str(self.candidate)]), 0)
            self.assertEqual(json.loads(output.getvalue())['status'], 'verified')
            self.assertEqual(replay.call_args.args[0].rom, bytes([255,0,1]))

    def test_structural_only_never_replays(self):
        with patch.object(verify, 'check_trusted'), patch.object(verify, 'replay_frozen') as replay, patch('sys.stdout', new_callable=io.StringIO) as output:
            self.assertEqual(verify.main(['--local', str(self.candidate), '--structural-only']), 0)
            self.assertEqual(json.loads(output.getvalue())['status'], 'structural_pass')
            replay.assert_not_called()

    def test_missing_heap_prepared_without_rereading_candidate(self):
        first = True
        def replay(frozen, *args, **kwargs):
            nonlocal first
            if first:
                first = False
                (self.candidate/'rom.bin').write_bytes(b'replaced')
                raise verify.ReplayUnavailable('missing')
            self.assertEqual(frozen.rom, bytes([255,0,1]))
        with patch.object(verify, 'check_trusted'), patch.object(verify, 'replay_frozen', side_effect=replay), patch('subprocess.run') as prepare, patch('sys.stdout', new_callable=io.StringIO):
            self.assertEqual(verify.main(['--local', str(self.candidate), '--hol', '/operator/HOL']), 0)
            self.assertEqual(prepare.call_args.args[0][-2:], ['--hol','/operator/HOL'])

    def test_failed_proof_does_not_trigger_preparation(self):
        with patch.object(verify, 'check_trusted'), patch.object(verify, 'replay_frozen', side_effect=verify.Rejected('wrong statement')), patch('subprocess.run') as prepare, patch('sys.stdout', new_callable=io.StringIO):
            self.assertEqual(verify.main(['--local', str(self.candidate)]), 1)
            prepare.assert_not_called()

class CompatibilityTests(unittest.TestCase):
    setUp = BoundaryTests.setUp

    def test_explicit_trusted_root_is_used_without_changing_default(self):
        original = verify.ROOT
        selected = self.candidate/'operator-root'
        with patch.object(verify, 'check_trusted') as check, patch.object(verify, 'replay_frozen') as replay, patch('sys.stdout', new_callable=io.StringIO):
            self.assertEqual(verify.main(['--local', str(self.candidate), '--trusted', str(selected)]), 0)
        check.assert_called_once_with(selected.resolve())
        self.assertEqual(replay.call_args.kwargs['trusted'], selected.resolve())
        self.assertEqual(verify.ROOT, original)

    def test_structural_work_retains_frozen_literals_and_is_private(self):
        work = self.candidate.parent/(self.candidate.name+'-work')
        self.addCleanup(lambda: shutil.rmtree(work, ignore_errors=True))
        with patch.object(verify, 'check_trusted'), patch('sys.stdout', new_callable=io.StringIO):
            self.assertEqual(verify.main(['--local', str(self.candidate), '--structural-only', '--work', str(work)]), 0)
        self.assertEqual(work.stat().st_mode & 0o777, 0o700)
        self.assertEqual((work/'input/rom.bin').read_bytes(), bytes([255,0,1]))
        self.assertIn('255w;0w;1w', (work/'input/submissionLiteralsScript.sml').read_text())
        with patch.object(verify, 'check_trusted'), patch('sys.stdout', new_callable=io.StringIO):
            self.assertEqual(verify.main(['--local', str(self.candidate), '--structural-only', '--work', str(work)]), 1)
        self.assertEqual((work/'input/rom.bin').read_bytes(), bytes([255,0,1]))

    def test_missing_heap_retry_keeps_work_and_hide_options(self):
        work = self.candidate.parent/(self.candidate.name+'-replay')
        hidden = self.candidate
        captured = []
        def replay(frozen, *args, **kwargs):
            captured.append((frozen, kwargs))
            if len(captured) == 1:
                (self.candidate/'rom.bin').write_bytes(b'replacement')
                raise verify.ReplayUnavailable('missing')
        with patch.object(verify, 'check_trusted'), patch.object(verify, 'replay_frozen', side_effect=replay), patch('subprocess.run'), patch('sys.stdout', new_callable=io.StringIO):
            self.assertEqual(verify.main(['--local', str(self.candidate), '--work', str(work), '--hide', str(hidden)]), 0)
        self.assertIs(captured[0][0], captured[1][0])
        self.assertEqual(captured[1][0].rom, bytes([255,0,1]))
        self.assertEqual(captured[1][1]['work'], work)
        self.assertEqual(captured[1][1]['hide'], [hidden])

    def test_hide_cannot_mask_replay_inputs(self):
        with patch.object(verify.shutil, 'which', return_value='/usr/bin/bwrap'):
            with self.assertRaisesRegex(verify.Rejected, 'required verifier path'):
                verify.hidden_replay_command(['/bin/true'], [self.candidate], self.candidate/'work', [])

    def test_hide_missing_sandbox_is_rejected(self):
        with patch.object(verify.shutil, 'which', return_value=None):
            with self.assertRaisesRegex(verify.Rejected, 'requires bubblewrap'):
                verify.hidden_replay_command(['/bin/true'], [self.candidate], self.candidate.parent/'work', [])

if __name__ == '__main__': unittest.main()
