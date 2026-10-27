import unittest
from unittest.mock import patch
import hashlib
import json
from import_ast import translate, generate

class ImportTests(unittest.TestCase):
    def test_list_tuple_and_option(self):
        self.assertEqual(translate('Prog.call (some ((some (VarKind.global, "x")), none)) "f" [Exp.const (BitVec.ofNat 64 3), Exp.baseAddr]', set()),
            'Call ( SOME ( ( SOME ( Global , «x» ) ) , NONE ) ) «f» [ Const 3w ; BaseAddr ]')

    def test_software_rotate_right(self):
        self.assertEqual(translate('Exp.shift Shift.ror (Exp.const (BitVec.ofNat 64 3)) (Exp.const (BitVec.ofNat 64 7))', set()),
            'Shift Ror ( Const 3w ) ( Const 7w )')

    def test_software_namespace_is_consumed_completely(self):
        source = b'namespace Guest.Software\nopen Flapjack\ndef guestAst : List (Decl (BitVec 64)) := []\nend Guest.Software\n'
        provenance = json.dumps({'ast_sha256': hashlib.sha256(source).hexdigest()})
        with patch('import_ast.Path.read_text', return_value=provenance):
            result = generate(source)
        self.assertIn('guestAst : 64 panLang$decl list =', result)
        self.assertNotIn('Software', result)

    def test_unknown_constructor_rejected(self):
        with self.assertRaises(ValueError): translate('Prog.unsupported', set())

    def test_unbalanced_rejected(self):
        with self.assertRaises(ValueError): translate('[Prog.skip)', set())

    def test_wrong_word_width_rejected(self):
        with self.assertRaises(ValueError): translate('(BitVec.ofNat 32 1)', set())

    def test_word_overflow_rejected(self):
        with self.assertRaises(ValueError): translate('(BitVec.ofNat 64 18446744073709551616)', set())

    def test_pin_rejected(self):
        with self.assertRaises(ValueError): generate(b'changed source')

if __name__ == '__main__': unittest.main()
