#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-u-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'a0ae1e5a67ae5f6d1e78075c398ffc7c6ecd3c9ef46fb652b3a54386c97b54b6','provider_survey.py':'2bd1321774c2659b5e057206c376f9ef9f182dd8cf929d53fe1393e2ef08387a','source-manifest.json':'b21303a427288af77bab5da9ef085bcb74671b8b1ca75f683d3af18302e0bcce'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Sign33ForwardNormU38','9df0246ba865b64dac84da5728aadda9695ef3ebe96f278c53b8ec55de753058',['Norm38ReferenceTerminals','Norm38ReferenceFieldsAll','Norm38ForwardGatesAssembly','Norm38ForwardPrefix']),('Sign33ForwardNormU','2b0d55d16ee1b0dba4eeff30ddb25d2545e6d6d61a910dccc84809c1217e1ab7',['Sign33ForwardNormU38','Sign33Node78Factor','Sign33NegativeNode76','Sign33AbstractProjection32','Norm38ForwardPrefix'])];assert len(rows)==2
for row,(n,h,imports) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports] and s.count('#print axioms ')==1
a=(p/'src/DiophantineConsistency/Sign33ForwardNormU38.lean').read_text();b=(p/'src/DiophantineConsistency/Sign33ForwardNormU.lean').read_text()
for x in ['d.U = 1','witnessCoordinates ports u) 78) = 1','ht.2.2.1.trans (hc.2.2.1.trans hu)']:assert x in a
for x in ['ι negative = d.y*d.y-d.V*d.V','d.U = 1','(ι (v 13)+1)*(ι (v 13)+1)-ι (v 32)*ι (v 33) = 1','Sign33Node78Factor.node78 ι ports w','Sign33NegativeNode76.negative_of_core ports u negative hn','Sign33AbstractProjection32.project','v 33 = negative','v 13 = u 12','map_add, map_one']:assert x in b
f=(d/'research/nine-sharing-sign33-forward-constructor-check/src/DiophantineConsistency/SharingForward33.lean').read_text();vec=[x.strip() for x in re.search(r'!\[(.*?)\]',f.split('def witnessCoordinates',1)[1].split('theorem witness_inputs',1)[0],re.S).group(1).split(',')];assert vec[12]=='u 12' and vec[31]=='w 35' and vec[32]=='negative'
fields=(d/'research/nine-sharing-norm38-reference-fields-combine-check/src/DiophantineConsistency/Norm38ReferenceFieldsAll.lean').read_text();assert 'reference p x 78 = d.U' in fields
survey=(p/'provider_survey.py').read_text()
for h in ['c59906a32aa1a905544c2bac4b791f4fa76d7bc179fd8ba1ccb83feb9a4261c3','80883e2565238e882f9a9dd3773313888bdee7b5d8921ccf6497c6e406bba13c','db2eaf9f695f596451f3cefa87f5051b4c2bf56d32c7e43d3c8279c79b0e5932']:assert h in survey
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'conditional U core and negative representative to constructor U cut; no Lean replay'},indent=2,sort_keys=True))
