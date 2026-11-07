#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-p-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'6ff04fa9b9dc4ee3d38bcfa65a0af3caf8da4805720a9f0963e0d468283b1fde','provider_survey.py':'e93e0ae60790a3d94e7fa5dcc43319e962df44972ad865e7989b00f738809f25','source-manifest.json':'d6394c4acaeeaaed03f056266985e39826f9437fc9a4fd862562d7c7aac1c3a7'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Sign33ForwardNormPEll','af8221a7514d2d1647170b7f1cc2aee1b9e7a271a520983b73135ad4224596b8',['DiophantineConsistency.SharingForward33','DiophantineConsistency.Sign33ResidualAssembly','FreshModel106'],'ell_of_core'),('Sign33ForwardNormP','7cc4c48aadb9af79a61f5414cfabddb464aadfb844d82c739d63047e43592f05',['DiophantineConsistency.Sign33ForwardNormPEll'],'norm_p_of_core')];assert len(rows)==2
for row,(n,h,imports,t) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==imports and re.findall(r'^theorem (\w+)',s,re.M)==[t] and s.count('#print axioms ')==1
a=(p/'src/DiophantineConsistency/Sign33ForwardNormPEll.lean').read_text();b=(p/'src/DiophantineConsistency/Sign33ForwardNormP.lean').read_text()
for x in ['ι (v 21)','u j+1','SharingForward38.witnessCoordinates','Carrier65.core']:assert x in a
for x in ['ι tau = d.tau','d.P = 1','ι (v 27)*ι (v 27)-ι (v 21)*(ι (v 21)+((ι (v 11)+1)+(ι (v 12)+1))) = 1','ell_of_core ports u gap tau inner value negative','d.k = ((ι (v 11)+1)+(ι (v 12)+1))','d.tau ^ 2 - d.ell*(d.ell+d.k) = 1 at hp']:assert x in b
f=(d/'research/nine-sharing-sign33-forward-constructor-check/src/DiophantineConsistency/SharingForward33.lean').read_text();part=f.split('def witnessCoordinates',1)[1].split('theorem witness_inputs',1)[0];vec=[x.strip() for x in re.search(r'!\[(.*?)\]',part,re.S).group(1).split(',')];assert vec[20]=='w 20' and vec[26]=='tau' and vec[10]=='u 10' and vec[11]=='u 11'
w=(d/'research/nine-sharing-seed38-weighted-retry/src/DiophantineConsistency/ForwardWitness38.lean').read_text();assert 'let w20 : S := ((((u 10) + (1 : S)) + ((u 11) + (1 : S))) * w18)' in w
c=(d/'Lean/DiophantineConsistency/Carrier65.lean').read_text()
for x in ['let k := eta + zeta','let ell := E * k * Y','let P := tau ^ 2 - ell * (ell + k)']:assert x in c
run=(p/'run.py').read_text();assert "if mod in survey['selected']" in run and "elif mod in {e['module'] for e in entries}" in run and "need(guard(deps)==row['direct_guard']" in run
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'conditional P-core and explicit tau representative to constructor cut; no Lean replay'},indent=2,sort_keys=True))
