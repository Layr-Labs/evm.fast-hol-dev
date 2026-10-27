"""Boundary tests for the sole source-based participant envelope."""
from pathlib import Path
import tempfile
import unittest
from verify_source import (author_sandbox_command, frozen_source_submission,
                           install_author_data, install_author_helpers)


class SourceSubmissionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='hol-init-source-test-')
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)
        self.candidate = self.base/'candidate'
        self.candidate.mkdir()
        (self.candidate/'rom.bin').write_bytes(b'\x13\x00\x00\x00')
        (self.candidate/'claim.json').write_text('{"K":"infinity"}\n')
        (self.candidate/'experiments').mkdir()
        (self.candidate/'experiments'/'initProofScript.sml').write_text(
            'Theorem candidate_proof: T\nProof simp[] QED\n')
        (self.candidate/'experiments'/'original-allocation.term').write_text(
            'S\nBs\nLn\n0\n')
        self.snapshot = self.base/'snapshot'
        self.snapshot.mkdir()

    def test_valid_source_is_frozen_without_article(self):
        score = frozen_source_submission(self.candidate, self.snapshot)
        self.assertEqual(score, 'infinity')
        self.assertEqual((self.snapshot/'rom.bin').read_bytes(), b'\x13\x00\x00\x00')
        self.assertEqual((self.snapshot/'claim.json').read_text(), '{"K":"infinity"}\n')
        self.assertEqual((self.snapshot/'experiments'/'initProofScript.sml').read_text(),
                         (self.candidate/'experiments'/'initProofScript.sml').read_text())
        self.assertEqual((self.snapshot/'experiments'/'original-allocation.term').read_text(),
                         'S\nBs\nLn\n0\n')
        self.assertNotIn('certificate.art', {p.name for p in self.snapshot.iterdir()})

    def test_article_file_is_not_a_source_envelope(self):
        (self.candidate/'certificate.art').write_bytes(b'article')
        with self.assertRaisesRegex(ValueError, 'exactly rom.bin, claim.json, experiments'):
            frozen_source_submission(self.candidate, self.snapshot)

    def test_duplicate_claim_field_is_rejected(self):
        (self.candidate/'claim.json').write_text('{"K":"infinity","K":1}')
        with self.assertRaisesRegex(ValueError, 'duplicate JSON key'):
            frozen_source_submission(self.candidate, self.snapshot)

    def test_symlink_source_is_rejected(self):
        source = self.candidate/'experiments'/'initProofScript.sml'
        source.unlink()
        source.symlink_to(self.candidate/'claim.json')
        with self.assertRaisesRegex(ValueError, 'regular files'):
            frozen_source_submission(self.candidate, self.snapshot)

    def test_unrecognized_term_file_is_rejected(self):
        (self.candidate/'experiments'/'allocation.term').write_text('S\n')
        with self.assertRaisesRegex(ValueError, 'unsupported proof source name'):
            frozen_source_submission(self.candidate, self.snapshot)

    def test_allocation_hint_file_is_required(self):
        (self.candidate/'experiments'/'original-allocation.term').unlink()
        with self.assertRaisesRegex(ValueError, 'original-allocation.term is required'):
            frozen_source_submission(self.candidate, self.snapshot)

    def test_fixed_allocation_helper_is_installed_beside_build(self):
        helper = install_author_helpers(self.snapshot)
        self.assertEqual(helper.read_bytes(),
                         (Path(__file__).resolve().parents[1]/
                          'tools/allocationHintLib.sml').read_bytes())
        self.assertEqual(helper.stat().st_mode & 0o777, 0o444)

    def test_candidate_allocation_data_is_installed_read_only_at_quse_path(self):
        work = self.base/'data-work'
        source = work/'input/experiments/original-allocation.term'
        source.parent.mkdir(parents=True)
        source.write_text('S\nBs\nLn\n0\n')
        data = install_author_data(work)
        self.assertEqual(data.read_bytes(),
                         source.read_bytes())
        self.assertEqual(data.stat().st_mode & 0o777, 0o444)

    def test_author_sandbox_clears_host_environment_and_masks_user_dirs(self):
        work = self.base/'work'
        work.mkdir()
        standard = self.base/'standard'
        author = self.base/'author'
        command = author_sandbox_command('/usr/bin/bwrap', work, standard,
                                         author, ['/usr/bin/env'])
        self.assertIn('--clearenv', command)
        self.assertIn(('--tmpfs', '/home'), list(zip(command, command[1:])))
        self.assertIn(('--tmpfs', '/run'), list(zip(command, command[1:])))
        self.assertIn(('--tmpfs', '/var'), list(zip(command, command[1:])))
        ro_bindings = [tuple(command[i:i+3])
                       for i, x in enumerate(command[:-2]) if x == '--ro-bind']
        self.assertIn(('--ro-bind', str(standard), str(standard)),
                      ro_bindings)
        self.assertIn(('--ro-bind', str(author), str(author)),
                      ro_bindings)
        self.assertIn(('--ro-bind', str(work/'input'), str(work/'input')),
                      ro_bindings)
        self.assertIn(('--ro-bind', str(work/'experiments'),
                      str(work/'experiments')), ro_bindings)
        helper = str(work/'tools/allocationHintLib.sml')
        self.assertIn(('--ro-bind', helper, helper), ro_bindings)
        self.assertNotIn('GH_TOKEN', command)


if __name__ == '__main__':
    unittest.main()
