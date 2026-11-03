#!/usr/bin/env python3
"""Read-only independent review of the 92-node algebra receipt and sources."""
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
P = D / 'research/ordinary12-qcube92-candidate'
O = P / 'observations/attempt05'
PIN = {
    P/'QCube92.lean': 'd79cdacdeb36d6d080d71284b501d651be80312ae85edb43c270f5360244e8aa',
    P/'ALGEBRA.md': '5951718c69d58563d11920b927589f7dda64596a8a8e9b344e799891c91990e1',
    P/'check_lean_graph.py': '89d7fc53665cde61e1847a05c80fb79e002dc0f5da0983c7725395d37cd4c791',
    P/'check_graph.py': '1ac391115e6cc25fbc2c333af9cc17a41a20387f381eeac00d0d8e3c64d80dcd',
    P/'run.py': '76c2e30af23b71b626bd7e0e36032324f347bd6c8f317bd607d59b18cfc45910',
    P/'candidate.json': '3a21d323adb96788a4b46c0b33800e07f2d1cb708b5c3c53ab709f6e186acee3',
    O/'terminal.json': 'aaf66f7a256fb37d8412a8b92e595314ff42c097a5c83af0fbcf421f587f6d59',
    O/'QCube92-source.txt': 'd79cdacdeb36d6d080d71284b501d651be80312ae85edb43c270f5360244e8aa',
    O/'stdout': '2c93357006ce3ebdfc3bb335bb75ed1f681bcb18153bc66f5f584d7aa22e6159',
    P/'observations/graph01/stdout': '7811b1c8a017a5bbfc176024f3ac9e91f6274fb32ef4b2a53e0b94a6ad332d07',
    D/'research/ordinary12-sum-of-squares-candidate/observations/attempt03/terminal.json': 'a2d1c86c49776e439b74a3cb929907ee15c2a77ed7c6f1afc0642fb9a63f0913',
    D/'research/ordinary12-sum-of-squares-candidate/observations/attempt03/source.lean': '77f22764b45732e2f7b837bf98caf40e6563c232f48ba682c421889b396b7794',
    D/'research/ordinary12-sum-of-squares-candidate/FreeJSumSquares.lean': '77f22764b45732e2f7b837bf98caf40e6563c232f48ba682c421889b396b7794',
}

def must(condition, message):
    if not condition:
        raise SystemExit(message)

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

for file, value in PIN.items():
    must(digest(file) == value, 'input hash mismatch: ' + str(file))
source = (P/'QCube92.lean').read_text()
graph = json.loads((P/'candidate.json').read_text())
receipt = json.loads((O/'terminal.json').read_text())
# A second parser: every graph definition line must match the graph's ordered
# input, port or operation table. Reject unexpected/extra/unparsed lines.
start = 'def graph (p : Fin 4 → ℤ) : Graph :=\n'
must(source.count(start) == 1, 'ambiguous graph declaration')
block = source.split(start, 1)[1].split('\nvariable {R', 1)[0].splitlines()
expected = []
for index, name in enumerate(graph['witnesses']):
    expected.append('  let ' + name + ' : Expr (Fin 12) := .var ' + str(index))
for index, name in enumerate(graph['fixed_numerals']):
    expected.append('  let ' + name + ' : Expr (Fin 12) := .constant (p ' + str(index) + ')')
for name, op, left, right in graph['source']:
    expected.append('  let ' + name + ' := ' + str(left) + ' ' + op + ' ' + str(right))
expected.append('  ⟨A0, A1, N, P12⟩')
must(block == expected and len(graph['source']) == 92, 'Lean graph source mismatch')
struct = 'structure Graph where\n  first : Expr (Fin 12)\n  main : Expr (Fin 12)\n  ordinary : Expr (Fin 12)\n  output : Expr (Fin 12)'
must(struct in source, 'unexpected projection structure')
must(source.splitlines()[0] == 'import FreeJSumSquares', 'unexpected direct import')
must('Function.update v 6 (qcube p v * v 6)' in source, 'unexpected lift')
for theorem, lhs, rhs in [
    ('first_eval', '(FreeJSumSquares.firstResidual p).evalRing (lift p v)', '(qcube p v * qcube p v) * ((graph p).first.evalRing v)'),
    ('main_eval', '(FreeJSumSquares.mainResidual p).evalRing (lift p v)', '(graph p).main.evalRing v'),
    ('ordinary_eval', '(FreeJSumSquares.ordinaryResidual p).evalRing (lift p v)', '(graph p).ordinary.evalRing v'),
]:
    pattern = 'theorem ' + theorem + ' (p : Fin 4 → ℤ) (v : Fin 12 → R) :\n    ' + lhs + ' =\n      ' + rhs + ' := by'
    must(pattern in source, 'theorem statement mismatch: ' + theorem)
must('variable {R : Type*} [CommRing R]' in source, 'ring typeclass mismatch')

# Rerun the author's external source and graph checks, with no Lean invocation.
source_check = subprocess.run([sys.executable, '-I', '-S', '-B', str(P/'check_lean_graph.py')], capture_output=True, check=True)
must(not source_check.stderr and source_check.stdout == (P/'observations/graph01/stdout').read_bytes(), 'author Lean-graph output mismatch')
graph_check = subprocess.run([sys.executable, '-I', '-S', '-B', str(P/'check_graph.py')], capture_output=True, check=True)
result = json.loads(graph_check.stdout)
must(not graph_check.stderr and result['status'] == 'PASS' and result['rows'] == result['live'] == 92, 'author graph check failed')
for file in ('check_lean_graph.py', 'check_graph.py'):
    opt = subprocess.run([sys.executable, '-I', '-S', '-B', '-O', str(P/file)], capture_output=True, text=True)
    must(opt.returncode != 0 and 'optimized python' in opt.stderr.lower(), 'optimized execution not refused: ' + file)

# Match the receipt's direct source, output, logs and current selected provider.
must(receipt['exit'] == 0 and receipt['reason'] is None and receipt['before'] == receipt['after'], 'attempt05 did not succeed')
must(receipt['selected_provider_unchanged'], 'recorded provider drift')
for path, value in receipt['before'].items():
    must(Path(path).is_file() and digest(Path(path)) == value, 'recorded direct input mismatch: ' + path)
must(digest(O/'stdout') == receipt['stdout_sha256'] and digest(O/'stderr') == receipt['stderr_sha256'], 'log hash mismatch')
expected_log = ("'FreeJQCube92.first_eval' depends on axioms: [propext, Quot.sound]\n"
                "'FreeJQCube92.main_eval' depends on axioms: [propext]\n"
                "'FreeJQCube92.ordinary_eval' depends on axioms: [propext]\n")
must((O/'stdout').read_text() == expected_log and not (O/'stderr').read_bytes(), 'unexpected theorem report')
must(not any(x in (O/'stdout').read_text() for x in ('sorryAx', 'warning:', 'error:')), 'bad log content')
command = receipt['command']
output = Path(command[command.index('-o')+1])
compiled_source = Path(command[command.index('-o')-1])
must(digest(output) == receipt['object_sha256'], 'object hash mismatch')
must(digest(compiled_source) == PIN[P/'QCube92.lean'], 'compiled source snapshot mismatch')
must(len(receipt['samples']) == 3 and min(s['mem_available_kib'] for s in receipt['samples']) == 18501092, 'sample observation mismatch')
must(all(len(s['lean']) <= 1 for s in receipt['samples']), 'sample Lean count mismatch')
paths = receipt['lean_path'].split(':')
provider = {}
for root in paths[:-1]:
    for path in sorted(Path(root).rglob('*.olean')):
        must(path.is_file(), 'selected provider file missing')
        provider[str(path)] = {'sha256': digest(path), 'realpath': str(path.resolve())}
must(provider == receipt['selected_provider_before'] and len(provider) == 74, 'selected provider inventory mismatch')
direct = Path(paths[0])/'FreeJSumSquares.olean'
must(str(direct) in provider, 'direct imported object missing from inventory')
old_receipt = json.loads((D/'research/ordinary12-sum-of-squares-candidate/observations/attempt03/terminal.json').read_text())
must(old_receipt['exit_code'] == 0 and provider[str(direct)]['sha256'] == old_receipt['object_sha256'], 'prior direct object receipt mismatch')
must(old_receipt['guards_unchanged'] and old_receipt['provider_unchanged'], 'prior direct object guards failed')
must(old_receipt['source_sha256'] == digest(D/'research/ordinary12-sum-of-squares-candidate/observations/attempt03/source.lean'), 'prior source receipt mismatch')
for file, value in PIN.items():
    must(digest(file) == value, 'input changed during review: ' + str(file))
for path, info in provider.items():
    file = Path(path)
    must(digest(file) == info['sha256'] and str(file.resolve()) == info['realpath'], 'provider changed during review: ' + path)
must(digest(output) == receipt['object_sha256'], 'output changed during review')
print(json.dumps({'graph_rows': len(graph['source']), 'projections': ['A0', 'A1', 'N', 'P12'],
                  'attempt05_exit': receipt['exit'], 'object_sha256': receipt['object_sha256'],
                  'provider_files_rehashed': len(provider), 'prior_direct_object_matches': True,
                  'author_external_checks': 'PASS', 'optimized_guards': 'PASS'}, indent=2))
