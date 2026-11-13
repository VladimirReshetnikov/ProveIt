#!/usr/bin/env python3
"""Compare the literal Lean source to the candidate JSON. Does not run Lean."""
from pathlib import Path
import hashlib, json, re

P = Path(__file__).resolve().parent
D = P.parents[1]
def pin(path, digest):
    data = path.read_bytes()
    assert hashlib.sha256(data).hexdigest() == digest, str(path)
    return data

graph = json.loads(pin(D / 'research/ordinary14-natural-forced-gamma80/candidate.json',
                       '136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5'))
source = pin(P / 'P80NaturalForcedGamma.lean',
             '015214c4176ab1600c573297521b43987eb66fe863d918a6bcff803a76ca44d9').decode()
assert graph['domain'] == 'nonnegative integers' and graph['output'] == 'out'
inputs = ['n_J', 'n_F', 'n_alpha', 'n_f', 'n_i', 'n_T', 'n_w', 'n_s',
          'n_r', 'n_eta', 'n_zeta', 'n_y', 'n_gamma', 'n_h']
ports = ['beta', 'K0', 'MC', 'MF']
assert graph['witnesses'] == inputs and graph['fixed_numerals'] == ports
aliases = re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.var (\d+)$', source, re.M)
port_aliases = re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.constant \(p (\d+)\)$', source, re.M)
assert aliases == [(n, str(i)) for i, n in enumerate(inputs)]
assert port_aliases == [(n, str(i)) for i, n in enumerate(ports)]
lo, hi = '  -- BEGIN LITERAL GRAPH\n', '  -- END LITERAL GRAPH\n'
assert source.count(lo) == source.count(hi) == 1
pattern = re.compile(r'^  let ([A-Za-z][A-Za-z0-9_]*) := ([A-Za-z0-9_]+) ([+*\-]) ([A-Za-z0-9_]+)$')
def atom(x): return int(x) if x.isdecimal() else x
rows = []
for line in source.split(lo, 1)[1].split(hi, 1)[0].splitlines():
    m = pattern.fullmatch(line)
    assert m, line
    n, x, op, y = m.groups()
    rows.append([n, op, atom(x), atom(y)])
assert rows == graph['source'] and len(rows) == graph['operations'] == 80
fields = ['first', 'main', 'aux', 'strong', 'guardFactor', 'output', 'qF', 'C', 'G', 'rank']
nodes = ['F0', 'F1', 'Fa', 'Fs', 'guard', 'out', 'qF', 'C', 'G', 'R']
block = source.split('structure Graph where\n', 1)[1].split('\nset_option ', 1)[0]
assert re.findall(r'^  (\w+) : Expr \(Fin 14\)$', block, re.M) == fields
assert source.count('  ⟨' + ', '.join(nodes) + '⟩') == 1
assert re.search(r'theorem output_shape \(p : Fin 4 → ℤ\) : \(graph p\)\.output =\s*'
                 r'\(graph p\)\.first \* \(graph p\)\.main \* \(graph p\)\.aux \*\s*'
                 r'\(graph p\)\.strong \* \(graph p\)\.guardFactor - 1 := by rfl', source)
known = set(inputs + ports)
for n, op, x, y in rows:
    assert n not in known and op in ('+', '-', '*')
    assert all(type(v) is int or v in known for v in (x, y))
    known.add(n)
needed = {'out'}
for n, op, x, y in reversed(rows):
    if n in needed: needed.update(v for v in (x, y) if isinstance(v, str))
assert all(n in needed for n, _, _, _ in rows) and set(inputs + ports) <= needed
by = {n: [op, x, y] for n, op, x, y in rows}
assert by['P01'] == ['*', 'F0', 'F1']
assert by['P012'] == ['*', 'P01', 'Fa']
assert by['P0123'] == ['*', 'P012', 'Fs']
assert by['P01234'] == ['*', 'P0123', 'guard']
assert by['out'] == ['-', 'P01234', 1]
print(json.dumps({'scope': 'literal source transcription only; no Lean elaboration, semantic or iPRA binding',
                  'rows': len(rows), 'slots': len(inputs), 'ports': len(ports),
                  'fields': dict(zip(fields, nodes)), 'all_gates_inputs_ports_live': True},
                 sort_keys=True, indent=2))
