#!/usr/bin/env python3
"""Compare every literal gate and input position with the checked candidate graph."""
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parent; raw=(D/'candidate.json').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='a7934aac8f72dc632ebc86f15fa4300106b6af2e6ab5cd73e94f8bdd4c11e735'
c=json.loads(raw);root=D.parents[3]
source=(root/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/AdaptiveNamedValues33.lean').read_text()
literal=source.split('def literal (p : Fin 4 → ℤ) : Expr (Fin 33) :=\n',1)[1].split('\ndef embed ',1)[0]
variables=re.findall(r'^  let (\w+) : Expr \(Fin 33\) := \.var \((\d+)\)$',literal,re.M)
constants=re.findall(r'^  let (\w+) : Expr \(Fin 33\) := \.constant \(p (\d+)\)$',literal,re.M)
assert variables==[(n,str(i)) for i,n in enumerate(c['witnesses'])]
assert constants==[(n,str(i)) for i,n in enumerate(c['fixed_numerals'])]
gates=re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',literal,re.M)
def normalize(x):return int(x) if x.isdigit() else x
assert [[name,op,normalize(a),normalize(b)] for name,a,op,b in gates]==c['source']
assert literal.rstrip().splitlines()[-1].strip()==c['output']
print('PASS',len(variables),'witnesses',len(constants),'ports',len(gates),'gates; Lean literal matches graph')
