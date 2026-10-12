"""Run the delivered tests and retain a reproducible machine-readable summary."""
from pathlib import Path
import hashlib
import json
import platform
import sys
import time
import unittest
import sympy

ROOT = Path(__file__).resolve().parent

def main():
    result_dir = ROOT/'results'
    result_dir.mkdir(exist_ok=True)
    suite = unittest.defaultTestLoader.discover(str(ROOT/'tests'), pattern='test_*.py', top_level_dir=str(ROOT))
    start = time.perf_counter()
    with (result_dir/'tests.log').open('w') as log:
        result = unittest.TextTestRunner(stream=log, verbosity=2).run(suite)
    summary = {
        'status': 'PASS' if result.wasSuccessful() else 'FAIL',
        'unittest_methods': result.testsRun,
        'failures': len(result.failures), 'errors': len(result.errors),
        'skips': len(result.skipped),
        'elapsed_seconds': time.perf_counter()-start,
        'python': sys.version, 'platform': platform.platform(), 'sympy': sympy.__version__,
        'randomized_case_counts': {
            'expanded_graph_of_surfaces_vs_condensed': 1200,
            'smith_vs_sympy': 1800,
            'determinantal_divisor_audits': 200,
            'canonical_binary_torsion_merge': 500,
            'twisted_free_quotient_formula': 700,
            'oriented_port_cycles': 400},
        'seeds': list(range(2026101201,2026101207)),
        'largest_binary_parameter': '2^16384',
        'native_repository_suite_run': False,
        'regina_cut_oracle_run': False,
        'source_hashes': {
            str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for folder in ('interface_homology','tests')
            for p in sorted((ROOT/folder).glob('*.py'))},
        'scope': 'Finite algebraic interface models and explicit surface presentations; no source geometry authentication.'
    }
    (result_dir/'validation.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k not in ('source_hashes','python')},indent=2))
    return not result.wasSuccessful()

if __name__=='__main__':raise SystemExit(main())
