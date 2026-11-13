#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-constructor-ell-retry02';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'7f97c590f156cd8e0c0501219f0c0e366a2e7ba4ce9ea25c1fa0ab12c4da4f5e','provider_survey.py':'a97860b5dc347b8eb69aac4276e75353547df27b199433ab26ee195ef12be844','source-manifest.json':'aaab6357b1a2ec97642ff4b45d841990f3aaa408e53b365e62c14f8cfb78741c'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Sign33AbstractProjection21','781dcb6cb8a8268f3fecfeefd3299aa3aba173b93f24c0dc34dc41b97e6699b8',['Sign33AbstractTuple']),('Sign33ConstructorEllRetry','caf316602e1cfb029422902bc53a57fbf0609eaa77d18df21b8407800d7aea26',['Sign33StaticNode30','Sign33ReferenceEll','Norm38ForwardGatesAssembly','Norm38ForwardPrefix','Sign33AbstractProjection21'])];assert len(rows)==2
for row,(n,h,imports) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports]
a=(p/'src/DiophantineConsistency/Sign33AbstractProjection21.lean').read_text();b=(p/'src/DiophantineConsistency/Sign33ConstructorEllRetry.lean').read_text();f=(d/'research/nine-sharing-sign33-abstract-projection22-check/src/DiophantineConsistency/Sign33AbstractTuple.lean').read_text();vec=[x.strip() for x in re.search(r'!\[(.*?)\]',f,re.S).group(1).split(',')];assert vec[20]=='w 20' and '(20 : Fin 33).succ = (21 : Fin 34)' in a and ') 21 = w 20' in a and 'ports u 20 :=' in a
for x in ['Sign33StaticNode30.node30 ports w hg','Norm38ForwardGates.forward_gatesHold','Norm38Forward.forward_prefix','Sign33ReferenceEll.reference_ell','ht.trans hc','Sign33AbstractProjection21.project','ι (v 21)']:assert x in b
survey=(p/'provider_survey.py').read_text()
for h in ['2464c7f1a7f03d85770c354c5dbb5130c51edf6fdce392e297732373b0cdb8eb','55e40338fc8a1c4274b7a53aa696c4a03eb7382c22b949fb3eec82ec9a916c0d','c1e7cabe5281270ce4d094989938ad9dee3897f11fa1426787cad078b3b3a86f']:assert h in survey

old=d/'research/nine-sharing-sign33-constructor-ell-retry01';oldsrc=(old/'src/DiophantineConsistency/Sign33ConstructorEllRetry.lean').read_text();assert oldsrc.count('  exact he\n')==1 and oldsrc.replace('  exact he\n','  simpa only [map_add, map_one] using he\n')==b
assert (old/'src/DiophantineConsistency/Sign33AbstractProjection21.lean').read_text()==a
oldrun=(old/'run.py').read_text().replace('nine-sharing-sign33-constructor-ell-retry01-20261106','nine-sharing-sign33-constructor-ell-retry02-20261106').replace('f4d908397809594741cf4b8cdf45648b2a54d89c43d47ed8a21c10d0a349aecf','aaab6357b1a2ec97642ff4b45d841990f3aaa408e53b365e62c14f8cfb78741c');assert oldrun==(p/'run.py').read_text()
assert sha(old/'attempt01/state.json')=='62e2f3801100daab95302a5f33cb84efa8902ba4b87a2845ec982aefed09baea' and 'Type mismatch' in (old/'attempt01/Sign33ConstructorEllRetry-compile.txt').read_text()

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'factored constructor ell proposal; no Lean replay'},indent=2,sort_keys=True))
