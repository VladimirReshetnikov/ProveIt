#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-compact-language-import-retry01';O=D/'research/nine-seed33-jones-compact-language-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'run.py')=='eb214ef13ee2ab5c8c61d339afa2cb0383b636bdecfa91a2a6cd7ce82e2d8b20' and sha(P/'source-manifest.json')=='b659ef31fb11904d97554122bd12456ee61c47cdbacb84c9f0bacb2d9d19d6ce'
n='Sign33MacroLanguage';a=(O/'src/DiophantineConsistency'/f'{n}.lean').read_text();p=P/'src/DiophantineConsistency'/f'{n}.lean';b=p.read_text();assert a.replace('import DiophantineConsistency.Sign33NamedFormula','import DiophantineConsistency.SharingSeed33Syntax\nimport DiophantineConsistency.CurrentKernelData2011')==b and sha(p)=='7bea6cf1ea90c54007de2eab62afad11d06328bfd27df3ffea0afbe34bd16fa1'
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['source_sha256']==sha(p) and m[0]['imports']==['DiophantineConsistency.SharingSeed33Syntax','DiophantineConsistency.CurrentKernelData2011']
prior=D/'research/nine-seed33-jones-compact-language-check/attempt01/state.json';assert sha(prior)=='7cd3124ef2828b60aabcc368435dded8893ef8e3795d8f8b74b79c50733f008c';s=json.loads(prior.read_text());assert s['status']=='FAILED' and s['rows'][0]['compile']['exit']==-6
print(json.dumps({'status':'PASS_STATIC','scope':'import-only retry; kernel source/object ancestry inherited, no recipe or semantic theorem'}))
