"""Regression tests for assembling baseline author-export drivers."""
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import export_baseline


class ExportDriverTests(unittest.TestCase):
    def test_driver_resolves_dependencies_from_selected_source_map(self):
        build = Path('/tmp/build')
        source = Path('/tmp/targetScript.sml')
        source_map = {'target': source}
        article = Path('/tmp/proof.art')
        with patch.object(export_baseline, 'dependencies', return_value=[]) as deps:
            script = export_baseline.driver(
                build, Path('/tmp/hol'), source, 'target', ['target'], article,
                source_map)
        deps.assert_called_once_with(build, 'target', source_map)
        self.assertIn('BASELINE_MODULE_EXPORT_OK', script)


if __name__ == '__main__':
    unittest.main()
