"""Reproduce the delivered SK compiler's negative-start counterexample.

Pass the recovered source24 package root from reproduce_151.py. The package
is read only; counterexample input and output are written to fresh scratch.
"""
from pathlib import Path
import argparse
import json
import sys
import tempfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--package', type=Path, required=True)
args = parser.parse_args()
sys.dont_write_bytecode = True
sys.path.insert(0, str(args.package.resolve() / 'experiments/sk_carrier'))
from build_carrier import Terms, interpreter, compile_machine, parse_tm
from test_carrier import native_step, sk_step

work = Path(tempfile.mkdtemp(prefix='zfc-sk-negative-start-'))
path = work / 'negative-start.tm'
path.write_text('#! start -1\n1 0 0 R 1\n1 1 1 R 1\n')
start, rows = parse_tm(path)
terms = Terms()
core = interpreter(terms)
machine = compile_machine(terms, core, start, rows)
configuration = (start, [], 0, [])
expected = native_step(rows, configuration)
actual, _ = sk_step(terms, core, machine, configuration)
if start != -1 or expected is not None or actual != (1, [0], 0, []):
    raise SystemExit('Counterexample did not reproduce.')
result = {
    'parsed_start': start, 'native_first_step': expected,
    'compiled_first_step': actual,
    'cause': 'Python states[-1] selects encoded state1 instead of named state-1',
    'scope': 'Generic parser-domain defect; the frozen253 input starts at0 and is unaffected',
    'scratch': str(work),
}
(work / 'evidence.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
