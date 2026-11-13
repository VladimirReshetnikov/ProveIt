#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];N=D/'research/nine-seed38-jones-named-equality-retry01';O=D/'research/nine-seed38-jones-named-equality-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'0e3372d764049b7de2bd5a2ba9a23cdbc5c8bfcf933b645557ebaedc336af65e','provider_preflight.py':'7c2541107e28c6ad9ce2dba47e40cb0c96f9d9d8dff40ae805c559dce86b2f6c','source-manifest.json':'cfc9874ed0c1a04767f05b84df644934d73767c8921a31a397225bc5b9c123f8'}.items():assert sha(N/n)==h
m=json.loads((N/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['Norm38MacroNamedVars','Norm38MacroNamedEquality']
for row in m:
 n=row['module'].split('.')[-1];p=N/'src/DiophantineConsistency'/f'{n}.lean';assert sha(p)==row['source_sha256'];assert [x[7:] for x in p.read_text().splitlines() if x.startswith('import ')]==row['imports']
a=(O/'src/DiophantineConsistency/Norm38MacroNamedVars.lean').read_text();b=(N/'src/DiophantineConsistency/Norm38MacroNamedVars.lean').read_text();assert a.split('theorem vars_eq_named')[0]==b.split('theorem vars_eq_named')[0];assert a.split('theorem vars_eq_named')[1].split(':= by')[0]==b.split('theorem vars_eq_named')[1].split(':= by')[0]
for i in range(1,9):
 assert f'have h{i} : Fin.cons (1 : R) a ({i} : Fin 10) = a ({i-1} : Fin 9)' in b
 assert f'have hi : ({i-1} : Fin 9).succ = ({i} : Fin 10)' in b
assert 'Nat.reduceAdd' in b and 'rw [d11_rank_symbolic]' in b and sha(O/'src/DiophantineConsistency/Norm38MacroNamedEquality.lean')==sha(N/'src/DiophantineConsistency/Norm38MacroNamedEquality.lean')=='e04fa148a65dfbe3cce2d641c7afb35fc547902822d829dad2b4d26c6ee2d2c4'
print(json.dumps({'status':'PASS_STATIC','scope':'same proposed Lean recipe equality; h1-h8 index normalization and Nat.reduceAdd proof change only'}))
