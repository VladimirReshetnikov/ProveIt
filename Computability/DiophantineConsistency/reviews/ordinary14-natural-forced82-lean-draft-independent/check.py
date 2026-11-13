#!/usr/bin/env python3
"""Reconstruct the entire Lean draft from its graph JSON; never invokes Lean."""
from pathlib import Path
import hashlib
import json

D = Path(__file__).resolve().parents[2]
graph_raw = (D / 'research/ordinary14-root74-natural-forced82/candidate.json').read_bytes()
source_raw = (D / 'research/ordinary14-natural-forced82-lean-draft/P82NaturalForced.lean').read_bytes()
assert hashlib.sha256(graph_raw).hexdigest() == '1532ea5ec5f8dee349353044b9618a2e8a633f618e6f7ef5f1d19630b53b6c8a'
assert hashlib.sha256(source_raw).hexdigest() == '4fd5635afea3327181cdce6d176103195a9d2698f40ab8c40e2ea5c9a9b1fb84'
g = json.loads(graph_raw)
inputs = g['witnesses']
ports = g['fixed_numerals']
rows = g['source']
assert g['domain'] == 'nonnegative integers' and g['output'] == 'out'
assert len(inputs) == 14 and len(ports) == 4 and len(rows) == g['operations'] == 82
assert len(set(inputs + ports)) == 18
fields = [('first','F0'), ('main','F1'), ('aux','Fa'), ('strong','Fs'),
          ('guardFactor','guard'), ('output','out'), ('qF','qF'), ('C','C'), ('G','G'), ('rank','R')]
lines = [
'import DiophantineConsistency.AdaptiveEquationSyntax2011',
'',
'/-! Literal source-only proposal. No Lean elaboration or endpoint claim. -/',
'set_option autoImplicit false',
'set_option Elab.async false',
'set_option maxRecDepth 16384',
'noncomputable section',
'namespace P82NaturalForced',
'open DiophantineConsistency AdaptiveEquationSyntax2011',
'',
'structure Graph where',
]
lines += [f'  {name} : Expr (Fin 14)' for name, _ in fields]
lines += [
'',
'set_option linter.unusedVariables false in',
'def graph (p : Fin 4 → ℤ) : Graph :=',
]
lines += [f'  let {name} : Expr (Fin 14) := .var {i}' for i, name in enumerate(inputs)]
lines += [f'  let {name} : Expr (Fin 14) := .constant (p {i})' for i, name in enumerate(ports)]
lines += ['  -- BEGIN LITERAL GRAPH']
known = set(inputs + ports)
for name, op, left, right in rows:
    assert name not in known and op in ('+', '-', '*')
    for atom in (left, right):
        assert type(atom) is int or atom in known
        if type(atom) is int: assert atom >= 0
    known.add(name)
    lines.append(f'  let {name} := {left} {op} {right}')
assert all(node in known for _, node in fields)
lines += [
'  -- END LITERAL GRAPH',
'  ⟨' + ', '.join(node for _, node in fields) + '⟩',
'',
'theorem output_shape (p : Fin 4 → ℤ) : (graph p).output =',
'    (graph p).first * (graph p).main * (graph p).aux *',
'      (graph p).strong * (graph p).guardFactor - 1 := by rfl',
'',
'end P82NaturalForced',
'',
'#print axioms P82NaturalForced.output_shape',
]
assert ('\n'.join(lines) + '\n').encode('utf-8') == source_raw
needed = {g['output']}
for name, op, left, right in reversed(rows):
    if name in needed:
        needed.update(x for x in (left,right) if isinstance(x,str))
assert all(name in needed for name, *_ in rows) and set(inputs + ports) <= needed
by = {name:(op,left,right) for name,op,left,right in rows}
assert by['P01'] == ('*','F0','F1')
assert by['P012'] == ('*','P01','Fa')
assert by['P0123'] == ('*','P012','Fs')
assert by['P01234'] == ('*','P0123','guard')
assert by['out'] == ('-','P01234',1)
print(json.dumps({'scope':'exact source-byte reconstruction from graph; no Lean elaboration, semantics, provider or iPRA claim',
                  'variables':len(inputs), 'ports':len(ports), 'graph_rows':len(rows),
                  'structure_fields':len(fields), 'all_graph_nodes_inputs_ports_live':True,
                  'source_sha256':hashlib.sha256(source_raw).hexdigest(),
                  'candidate_sha256':hashlib.sha256(graph_raw).hexdigest()},sort_keys=True,indent=2))
