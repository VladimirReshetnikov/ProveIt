#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-compact-cuts-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'run.py')=='61a5a2528624434c74e3154e31572a6e1cf11ab131e5f725e8a9e2c7fceb1a20' and sha(P/'source-manifest.json')=='80de3d533eaa5b58109f9bd821aaa67f52f7897adb608ff0a5112186952ac655'
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Sign33MacroCuts','Sign33MacroPrefixEmbedding'];assert [r['module'].split('.')[-1] for r in m]==names
base=[(D/'research/nine-seed38-jones-compact-semantics-cut-check/src/DiophantineConsistency/Norm38MacroCuts.lean','de5a30d88de5f15a6b08f9a450e2b430104928dae8af67888f4bd92fb578da9d'),(D/'research/nine-seed38-jones-prefix-embedding-check/src/DiophantineConsistency/Norm38MacroPrefixEmbedding.lean','0e44abd4d3cbc028dac5759b7091c3e861376f42f6327a4db11c1512ede71477')]
for row,n,(prior,h) in zip(m,names,base):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==row['source_sha256'] and sha(prior)==h and [x[7:] for x in s.splitlines() if x.startswith('import ')]==row['imports'];assert prior.read_text().replace('Norm38','Sign33').replace('Fin 40','Fin 35').replace('codingStar 38 4','codingStar 33 4')==s
print(json.dumps({'status':'PASS_STATIC','scope':'four generic cut identities and prefix-path lookup proposals only; no recipe equality'}))
