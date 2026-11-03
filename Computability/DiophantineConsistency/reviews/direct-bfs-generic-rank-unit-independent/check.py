#!/usr/bin/env python3
"""Audit frozen Gamma-order, controller-unit and chosen-rank receipts without Lean."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2]
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
cases=[('direct-bfs-gamma-order-prototype','DirectBFSGammaOrder','directbfsgammaorder-attempt01','f41f2c0a42606b9c70368e467a5d4ef589cffada1a0d4ff101674b8a24766a62'),('direct-bfs-controller-unit-prototype','DirectBFSControllerUnit','directbfscontrollerunit-attempt02','1678575c029eeee7d6b6d8a5b5dd3bc08efb4c4b634f61fa48ff9663ff1e64c6'),('direct-bfs-generic-chosen-rank-prototype','DirectBFSGenericChosenRank','directbfsgenericrank-attempt01','4aa19a2a942e445dcd33f22d16b8e75e9b0546e85a249ed95446f2efa905c372')]
result={}
for folder,mod,attempt,obj in cases:
 p=D/'research'/folder;s=p/(mod+'.lean');o=p/'observations'/attempt;t=json.loads((o/'terminal.json').read_text());r=pathlib.Path(t['output_root']);pins=t['pins']
 need(t['exit']==0 and t['reason'] is None and pins==t['after'] and t['direct_imports']==t['direct_imports_after'],'receipt '+mod)
 need(sha(s)==pins['source']==sha(o/'source.txt')==sha(r/s.name),'source '+mod)
 need(sha(p/'run.py')==pins['runner'] and sha(t['command'][0])==pins['lean'],'runner '+mod)
 need(sha(r/(mod+'.olean'))==t['object_sha256']==obj,'object '+mod)
 need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs '+mod)
 reports=re.findall(r'^#print axioms ([\w.]+)$',s.read_text(),re.M)
 need((o/'stdout').read_text()==''.join(f"'{x}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for x in reports) and (o/'stderr').read_text()=='','reports '+mod)
 need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder '+mod)
 imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);records=t['direct_imports'];need([x['module'] for x in records]==imports,'import list '+mod)
 for x in records:
  rel=x['module'].replace('.','/')+'.olean';q=next((pathlib.Path(z)/rel for z in t['lean_path'].split(':') if (pathlib.Path(z)/rel).is_file()),None)
  need(q and q.resolve()==pathlib.Path(x['path']).resolve() and sha(q)==x['sha256'],'provider '+mod+' '+x['module'])
 for x in t.get('stage_receipts',[]):need(sha(x['path'])==x['sha256'],'stage receipt '+mod)
 result[mod]={'object_sha256':obj,'source_sha256':sha(s),'runner_sha256':sha(p/'run.py'),'imports':records,'reports':reports,'stage_receipts':len(t.get('stage_receipts',[]))}
for parent,child in [('DirectBFSControllerUnit','DirectBFSGammaOrder'),('DirectBFSGenericChosenRank','DirectBFSControllerUnit')]:
 need(next(x for x in result[parent]['imports'] if x['module']==child)['sha256']==result[child]['object_sha256'],'provider chain '+parent)
failed=D/'research/direct-bfs-controller-unit-prototype/observations/directbfscontrollerunit-attempt01';ft=json.loads((failed/'terminal.json').read_text())
need(ft['exit']!=0 and 'memory' in ((failed/'stdout').read_text()+(failed/'stderr').read_text()).lower(),'failed controller attempt')
print(json.dumps({'status':'PASS','packets':result,'lean_replayed':False},indent=2,sort_keys=True))
