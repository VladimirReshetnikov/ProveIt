#!/usr/bin/env python3
"""Audit retained BFS natural/model residue receipts without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2]
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
cases=[('direct-bfs-symbolic-k-residue-prototype','DirectBFSSymbolicKernelResidue','directbfskernelresidue-attempt01','68770ad5dc1990c415734a812b4384a1b17f786f3272c98ee1ed7b0fb5cd7739'),('direct-bfs-model-residue-prototype','DirectBFSModelResidue','directbfsmodelresidue-attempt01','421f11c8cad5ef90c0e138234eb1bdb598b8430b0989f4a9cbfb0261ab85921f'),('direct-bfs-halt-rank-prototype','DirectBFSHaltRank','directbfshaltrank-attempt03','e0de9db897a4dc7175a4056e0cfa797c63de0d182cb34b78c1b2a7b81627e405')];result={}
for folder,mod,attempt,obj in cases:
 p=D/'research'/folder;s=p/(mod+'.lean');o=p/'observations'/attempt;t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root']);pins=t['pins']
 need(t['exit']==0 and t['reason'] is None and pins==t['after'] and t['direct_imports']==t['direct_imports_after'],'state '+mod)
 need(sha(p/'run.py')==pins['runner'] and sha(t['command'][0])==pins['lean'],'runner '+mod)
 need(sha(s)==pins['source']==sha(o/'source.txt')==sha(root/s.name),'source '+mod)
 need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder '+mod)
 need(sha(root/(mod+'.olean'))==t['object_sha256']==obj,'object '+mod)
 need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs '+mod)
 reports=re.findall(r'^#print axioms ([\w.]+)$',s.read_text(),re.M)
 observed=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",(o/'stdout').read_text(),re.S)
 need(len(observed)==len(reports) and all([x.strip() for x in a.split(',')]==['propext','Classical.choice','Quot.sound'] for _,a in observed) and (o/'stderr').read_text()=='','reports '+mod)
 need([n.split('.')[-1] for n,_ in observed]==[n.split('.')[-1] for n in reports],'report names')
 imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);records=t['direct_imports'];need(imports==[x['module'] for x in records],'imports '+mod)
 for x in records:
  rel=x['module'].replace('.','/')+'.olean';q=next((pathlib.Path(z)/rel for z in t['lean_path'].split(':') if (pathlib.Path(z)/rel).is_file()),None)
  need(q and q.resolve()==pathlib.Path(x['path']).resolve() and sha(q)==x['sha256'],'selected '+x['module'])
 for x in t.get('stage_receipts',[]):need(sha(x['path'])==x['sha256'],'stage receipt')
 result[mod]={'object_sha256':obj,'imports':records,'reports':[x[0] for x in observed],'stage_receipts':len(t.get('stage_receipts',[]))}
need(result['DirectBFSModelResidue']['imports'][0]['sha256']==result['DirectBFSSymbolicKernelResidue']['object_sha256'],'residue provider')
need(next(x for x in result['DirectBFSHaltRank']['imports'] if x['module']=='DirectBFSModelResidue')['sha256']==result['DirectBFSModelResidue']['object_sha256'],'model provider')
need(next(x for x in result['DirectBFSHaltRank']['imports'] if x['module']=='DirectBFSHaltChosenRank')['sha256']=='a0ef6012dbb42a769e8c4ae3bae81ee73d9b57f427e0abc5e48236454af65690','chosen provider')
for f in ['research/direct-bfs-halt-rank-prototype/observations/directbfshaltrank-attempt03/terminal.json','research/direct-bfs-symbolic-k-residue-prototype/observations/directbfskernelresidue-attempt01/terminal.json','research/direct-bfs-halt-chosen-rank-prototype/observations/directbfshaltchosen-attempt02/terminal.json']:
 t=json.loads((D/f).read_text())
 for mod,want in {'DirectBFSSymbolicKernel':'69f4a2f9d32229b6846ec7f0b84fe4b4d69d5eba8de1ff5c9ddb063e1d855c3f','DirectBFSFourFieldsPacking':'cfd3cc0045adbca24395a947ac2a4855ac94b313318f9c81660e38818ee3601c'}.items():
  q=next((pathlib.Path(x)/(mod+'.olean') for x in t['lean_path'].split(':') if (pathlib.Path(x)/(mod+'.olean')).is_file()),None)
  need(q and sha(q)==want,'shared post-hoc provider '+f+' '+mod)
print(json.dumps({'status':'PASS','packets':result,'lean_replayed':False},indent=2,sort_keys=True))
