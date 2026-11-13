#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-source-import-diagnostic';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'1c535471f4e526c19051c88a4a7e2d67e7c391fb437f1cf934d5382351798227','source-manifest.json':'f325d8da7f1369f45987208fa4bbedfa79e74f26e8e79852aa99ebed54d52d41','partial-survey.py':'462acee066ec0a45fb30b682cc7d435a0b4b1414b9f8129c6f326ca3049ded8e','union-survey.py':'a2f88678529dfef74f0f93aebf5b9e62ee0830842571089b48e91f646b91ab12','union.json':'89b996196cb27d9ec751b673e8ac76e7b636a79ba2f5d03118982bd17e117651'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];a='DiophantineConsistency.Sign28CurrentConsIff';b='DiophantineConsistency.Sign31CurrentSourceIff';assert [r['imports'] for r in m]==[[a],[b],[a,b]]
for row in m:
 f=P/'src/DiophantineConsistency'/(row['module'].split('.')[-1]+'.lean');s=f.read_text();assert H(f)==row['source_sha256'];s=re.sub(r'/\-![\s\S]*?-/', '', s);assert [x.strip() for x in s.splitlines() if x.strip()]==['import '+i for i in row['imports']]
review=D/'reviews/nine-sharing-sign28-current-source-iff-retry01-failure-frontier-independent/check.py';assert H(review)=='77ca3857775edd5aa43f7aa6da12f437c726cb0b0982aa470ef5e835c780a481';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=60)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':3,'scope':'declaration-free imports only, fail-stop; no source iff claim'},sort_keys=True,indent=2))
