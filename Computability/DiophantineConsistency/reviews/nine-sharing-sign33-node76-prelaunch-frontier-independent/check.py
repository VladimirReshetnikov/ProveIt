#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-node76-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'25ab1abcd513a268e31900c6f8b5dc0397d6d9d799bc9bdb21bce538bff5b96c','provider_survey.py':'e93e0ae60790a3d94e7fa5dcc43319e962df44972ad865e7989b00f738809f25','source-manifest.json':'e2925d853dd49efc5b9c10c37793b33c9409bbfaec2f942d583c1f6124264ce5'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Sign33StaticNode76','4a02b6635246805523e826d496a536ca9b3543804b6b7b840615e32fa1632ca9','Norm38ReferenceTerminals'),('Sign33ReferenceNode76','022c20ec186337c0072cb4d0fb10d1eb07e16c72891a89ec7bb8d809e2926fe1','Norm38ReferenceFieldsAll')];assert len(rows)==2
for row,(n,h,imp) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+imp] and s.count('#print axioms ')==1
a=(p/'src/DiophantineConsistency/Sign33StaticNode76.lean').read_text();b=(p/'src/DiophantineConsistency/Sign33ReferenceNode76.lean').read_text()
for x in ['(hg : NormAssignment38.gatesHold ι ports w)','NormAssignment38.assignment ports w 76','Fin.castLE (by decide : 14 ≤ 38)','static_assignment_fixed ι ports w hg','ringRun_agrees_of_topological','(congrFun hfixed 76).trans (hrun 76 (by decide))']:assert x in a
for x in ['[CommRing R]','reference p x 76','(Carrier65.core p x).V * (Carrier65.core p x).V -','(Carrier65.core p x).y * (Carrier65.core p x).y','reference_76_edge, h74, h75, reference_V_node']:assert x in b
ref=(d/'research/nine-sharing-norm38-reference-draft/Norm38Reference.lean').read_text()
for x in ['let a74 : R := a71 * a71','let a75 : R := a12 * a12','let a76 : R := a74 - a75']:assert x in ref
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'conditional static node76 and generic V²−y² reference identity; no Lean replay'},indent=2,sort_keys=True))
