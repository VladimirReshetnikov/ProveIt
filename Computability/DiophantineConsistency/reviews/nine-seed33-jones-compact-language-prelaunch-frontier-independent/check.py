#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-compact-language-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'run.py')=='89b7b671bc89d8b2d9453ed39075c8dd463bfc64b90a24b793567157531c5873' and sha(P/'source-manifest.json')=='d12641dc47c495c9e2d106ae908fd0c0c82f21abdc557d53557d7c460e3b347d'
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['module']=='DiophantineConsistency.Sign33MacroLanguage' and m[0]['imports']==['DiophantineConsistency.Sign33NamedFormula'];p=P/'src/DiophantineConsistency/Sign33MacroLanguage.lean';d=D/'research/nine-seed33-jones-compact-lean-specialized-draft/Sign33MacroLanguage.lean';assert m[0]['source_sha256']==sha(p)==sha(d)=='de51ea7d49bbf72cb046f50b8000027bf723a59e4d54ae17368ee7490da7e864'
s=p.read_text();assert [x[7:] for x in s.splitlines() if x.startswith('import ')]==m[0]['imports'] and 'def seed : Expr (Fin 34)' in s and 'codingExpo 33 4' in s and 'codingStar 33 4' in s and 'Sign33IPRAEndpoint' not in s
review=D/'reviews/nine-seed33-jones-compact-lean-specialized-frontier-independent/check.py';assert sha(review)=='49dc9267bb909ee2e595e336ee439abf7c246f9a533f271c1297e606cc28c3f4';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_STATIC','scope':'language definitions only; no recipe/scopedness/equality'}))
