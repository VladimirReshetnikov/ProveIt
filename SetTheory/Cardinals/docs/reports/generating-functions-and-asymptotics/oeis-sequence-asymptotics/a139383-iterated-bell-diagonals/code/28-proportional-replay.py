"""Replay exact checks in a temporary directory without editing frozen outputs.
Requires Python 3 and SymPy. Optional --diagnostics also needs NumPy, SciPy,
and mpmath. The optional quadrature is exploratory, never an interval proof.
"""
import argparse, json, shutil, subprocess, sys, tempfile
from pathlib import Path
p = argparse.ArgumentParser()
p.add_argument('--diagnostics', action='store_true')
a = p.parse_args()
root = Path(__file__).resolve().parents[1]
def run(*args):
    subprocess.run([sys.executable, *map(str, args)], check=True)
with tempfile.TemporaryDirectory(prefix='bell-proportional-replay-') as tmp:
    work = Path(tmp)
    orbit = work/'orbit-coefficients.json'
    run(root/'verification/generate_coefficients.py', '--order', 3, '--out', orbit)
    assert json.loads(orbit.read_text()) == json.loads((root/'results/orbit-coefficients.json').read_text())
    shutil.copy2(root/'verification/generate_proportional.py', work/'generate_proportional.py')
    run(work/'generate_proportional.py')
    assert json.loads((work/'proportional-coefficients.json').read_text()) == json.loads((root/'results/proportional-coefficients.json').read_text())
    run(root/'verification/check_coefficients_portable.py', '--base', orbit, '--out', work/'independent.json')
    assert json.loads((work/'independent.json').read_text()) == json.loads((root/'review/proportional-audit/coefficient-checks.json').read_text())
    if a.diagnostics:
        shutil.copy2(root/'verification/check_proportional.py', work/'check_proportional.py')
        run(work/'check_proportional.py')
        produced = json.loads((work/'diagnostics.json').read_text())
        assert produced['not_certified'] is True
        print('Optional exploratory diagnostics completed; values are not rigorous enclosures.')
print('PASS: exact orbit JSON, general-beta JSON, and independent coefficient checks agree.')
