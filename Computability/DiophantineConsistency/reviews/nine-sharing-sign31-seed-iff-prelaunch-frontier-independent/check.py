#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-seed-iff-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'ab07005e420055cba00e364ce0abe3b1c7c3231af4ac8c80b463b576111d39f5','source-manifest.json':'a8df9c7a5bf2bad12955201342579c300b2e1ced89464c91252325eb74929b05','first-cut-survey.py':'a1bb29c1a7fb7eca8b12e63d4e1cb06fbaa47eec509fc35175f65e55cb346f41'}.items():assert sha(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['Sign31SeedPointwise','Sign31SeedExistential'];ss=[]
for row in m:
 n=row['module'].split('.')[-1];p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();ss.append(s);assert sha(p)==row['source_sha256'];assert [x[7:] for x in s.splitlines() if x.startswith('import ')]==row['imports']
a,b=ss
for x in ('drop (Sign31FirstCut.lift v) = v','InternalZero (SharingSeed31Sextic.seed p) v ↔','InternalZero (SharingSeed32Sextic.seed p) (Sign31FirstCut.lift v)','Sign31ZeroBridge.forward p v','Sign31ZeroBridge.backward p (Sign31FirstCut.lift v) hz','simpa only [drop_lift]'):assert x in a
for x in ('(p : Fin 4 → ℤ) (x : V)','∃ v : Fin 32 → V, v 0 = x','∃ v : Fin 33 → V, v 0 = x','Sign31ZeroBridge.forward p v hz','Sign31ZeroBridge.backward p v hz','simpa [Sign31FirstCut.lift] using hv','simpa [Sign31CoordinateRecover.drop] using hv'):assert x in b
assert a.count('#print axioms')==2 and b.count('#print axioms')==1
print(json.dumps({'status':'PASS_STATIC','scope':'pointwise and existential same-input symbolic-port equivalence; source/iPRA composition separate'}))
