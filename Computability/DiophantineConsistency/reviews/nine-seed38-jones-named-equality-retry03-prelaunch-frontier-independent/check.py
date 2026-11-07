#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];N=D/'research/nine-seed38-jones-named-equality-retry03';O=D/'research/nine-seed38-jones-named-equality-retry02';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'78a328c5dc8842f909b96153d1194292df765ad3706203b7070c4a8c5e38a985','provider_preflight.py':'1dd496ec292f8b99cd6482b49c293a6c6898015dc3f1d58e1e379bbf616fec9f','source-manifest.json':'d7aeb3a11122a42909370e5513b4893a7e85d3539ea7c57aa63f14015fe57d06'}.items():assert sha(N/n)==h
m=json.loads((N/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['Norm38MacroNamedVars','Norm38MacroNamedEquality']
for row in m:
 n=row['module'].split('.')[-1];p=N/'src/DiophantineConsistency'/f'{n}.lean';assert sha(p)==row['source_sha256'];assert [x[7:] for x in p.read_text().splitlines() if x.startswith('import ')]==row['imports']
a=(O/'src/DiophantineConsistency/Norm38MacroNamedVars.lean').read_text();b=(N/'src/DiophantineConsistency/Norm38MacroNamedVars.lean').read_text();assert a.replace('base, Nat.reduceAdd]\n','base, Nat.reduceAdd] <;> rfl\n')==b
assert sha(O/'src/DiophantineConsistency/Norm38MacroNamedEquality.lean')==sha(N/'src/DiophantineConsistency/Norm38MacroNamedEquality.lean')=='e04fa148a65dfbe3cce2d641c7afb35fc547902822d829dad2b4d26c6ee2d2c4'
print(json.dumps({'status':'PASS_STATIC','scope':'sole proof delta adds rfl following existing simplifier; unchanged theorem and second stage'}))
