#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];N=D/'research/nine-seed38-jones-named-equality-retry02';O=D/'research/nine-seed38-jones-named-equality-retry01';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'6e1556f2c83b8b0e05060a60fb196900537923e5278ccf5b0225e72641c6070f','provider_preflight.py':'a60a802f3899b157daefcf0239fffa06014212d831dbd42d9bb03a44f69e1c86','source-manifest.json':'f01804a47332271b56bbd69dc477fdbe31178b56cad4fe07838625c74d880369'}.items():assert sha(N/n)==h
m=json.loads((N/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['Norm38MacroNamedVars','Norm38MacroNamedEquality']
for row in m:
 n=row['module'].split('.')[-1];p=N/'src/DiophantineConsistency'/f'{n}.lean';assert sha(p)==row['source_sha256'];assert [x[7:] for x in p.read_text().splitlines() if x.startswith('import ')]==row['imports']
a=(O/'src/DiophantineConsistency/Norm38MacroNamedVars.lean').read_text();b=(N/'src/DiophantineConsistency/Norm38MacroNamedVars.lean').read_text();assert a.count('Fin.cons (1 : R) a (')==8 and a.replace('Fin.cons (1 : R) a (','Fin.cons (α := fun _ : Fin 10 => R) (1 : R) a (')==b
assert sha(O/'src/DiophantineConsistency/Norm38MacroNamedEquality.lean')==sha(N/'src/DiophantineConsistency/Norm38MacroNamedEquality.lean')=='e04fa148a65dfbe3cce2d641c7afb35fc547902822d829dad2b4d26c6ee2d2c4'
print(json.dumps({'status':'PASS_STATIC','scope':'sole proof delta specifies constant family on eight Fin.cons helpers; unchanged theorem and second stage'}))
