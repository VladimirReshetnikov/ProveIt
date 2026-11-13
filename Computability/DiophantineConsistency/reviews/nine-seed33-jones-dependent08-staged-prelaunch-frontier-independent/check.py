#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent08-staged-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P/'run.py')=='eb35b873ef5d9fef7e4b4e585cba5044d466d119d0e1deb24313d45af00455cc' and H(P/'source-manifest.json')=='9bb8ad0d288c34191aff0f81896c9d8e37c2fa699610e762530295edbf4d6fe8'
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['BdCd','DmKc','Output'];assert [r['module'].split('.')[-1] for r in m]==['Sign33MacroDependent'+n for n in names];ss=[]
for row,n,dep in zip(m,names,['Sign33MacroDependentV','Sign33MacroDependentBdCd','Sign33MacroDependentDmKc']):
 f=P/'src/DiophantineConsistency'/f'Sign33MacroDependent{n}.lean';old=D/'research/nine-seed38-jones-dependent08-staged-check/src/DiophantineConsistency'/f'Norm38MacroDependent{n}.lean';s=f.read_text();assert s==old.read_text().replace('Norm38','Sign33') and H(f)==row['source_sha256'] and row['imports']==['DiophantineConsistency.'+dep];ss.append(s)
for s,n,node,indices in [(ss[0],'Bd',40,[27,31]),(ss[0],'Cd',41,[28,31,27,33,26]),(ss[1],'Dm',42,[22,9,26,22,19,9,7,22]),(ss[1],'Kc',43,[39,41]),(ss[2],'T',44,[39,17,40,42,40,37,38]),(ss[2],'output',45,[43,42,35,42,37,36,43,42,35])]:
 h=s.split('theorem prefix_'+n,1)[1].split(':= by',1)[0];assert f'd{node}.values a (Fin.last {node-1})' in h and [int(x) for x in re.findall(r'd\d+.values a ⟨(\d+), by decide⟩',h)]==indices,n
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':3,'scope':'local d40–d45 immediate-prefix identities only'},sort_keys=True,indent=2))
