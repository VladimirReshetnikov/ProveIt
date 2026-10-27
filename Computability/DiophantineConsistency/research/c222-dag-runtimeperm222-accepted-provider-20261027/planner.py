from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';RES=D/'research';REV=D/'reviews'
pins={};observations=0
def record(p):
 p=Path(p);p=p if p.is_absolute() else R/p
 return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
def check(x):
 global observations
 a=record(x['path']);assert a['sha256']==x['sha256'],(x,a)
 pins[a['path']]=a;observations+=1;return a
def load(p,sha):
 a=check({'path':str(p),'sha256':sha});return json.loads(Path(a['path']).read_text())
def headers(p):
 s=Path(p).read_text();o=[];i=depth=0
 while i<len(s):
  pair=s[i:i+2]
  if depth:
   if pair=='/-':depth+=1;i+=2
   elif pair=='-/':depth-=1;i+=2
   else:o.append('\n' if s[i]=='\n' else ' ');i+=1
  elif pair=='/-':depth=1;i+=2
  elif pair=='--':
   while i<len(s) and s[i]!='\n':i+=1
  else:o.append(s[i]);i+=1
 assert depth==0
 return list(dict.fromkeys(['Init']+[n for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(o),re.M) for n in line.split()]))
planpath=RES/'c222-dag-runtimeperm222-cache-plan-20261027.json'
p=load(planpath,'e0d0736f57ebddca9a2530f93fdec69308ed77c1dec74c18787866f2ebfaf3d6')
for x in p['authenticated_paths']:check(x)
for m in p['modules']:
 assert headers(m['source']['path'])==m['actual_imports'],m['module']
 check(m['source'])
 for x in m['objects']:check(x)
check({'path':str(REV/'arithmetic-dag-rootperm222-root.md'),'sha256':'cdee704d2f11ca38b0d00eab459a1110a7d13351bc334fa2a5f169d540336f05'})
rmf=REV/'arithmetic-dag-rootperm222-root-auth/FILES.json'
for x in load(rmf,'35b9c5628521911f85ef0404f5853e57921ea8e9c76d1e5e61561280a4adcd1b'):check(x)
root=json.loads((REV/'arithmetic-dag-rootperm222-root-auth/state.json').read_text());assert root['status']=='PASS'
peerpath=REV/'arithmetic-dag-rootperm222-peer-replay.json';peer=load(peerpath,root['peer']['sha256'])
assert peer['status']=='PASS'
check(peer['manifest'])
for x in json.loads(Path(peer['manifest']['path']).read_text()):check(x)
for r in peer['records']:
 for k in ['source','snapshot','object','log','timing']:check(r[k])
 assert r['exit_code']==0 and r['object_byte_identical'] and r['full_log_byte_identical']
r=peer['records'][0];old=next(m for m in p['modules']if m['module']==r['module'])
assert r['module']=='BusyBeaver.ZFC.ArithmeticDagRootPerm222'
assert r['source']['sha256']==old['source']['sha256']
assert r['object']['sha256']==old['objects'][0]['sha256']
assert r['object']['path']=='/tmp/arithmetic-dag-rootperm222-peer-p41b9lmc/lib/BusyBeaver/ZFC/ArithmeticDagRootPerm222.olean'
replacement={'module':r['module'],'historical_provider':old['objects'][0],'accepted_provider':r['object'],'source':r['source'],'snapshot':r['snapshot'],'reason':'ROOT accepted independently replayed byte-identical provider; historical plan preserved.'}
for x in p['external']:
 primary=x if 'path'in x else x['object'];rel=Path(*x['module'].split('.')).with_suffix('.olean')
 actual=next((Path(q)/rel for q in p['package_paths']if(Path(q)/rel).exists()),None)
 assert actual and record(actual)['sha256']==primary['sha256']
newnames=['ArithmeticDagRuntimePerm222','ArithmeticDagRuntimePerm222Checks'];new=[]
for name in newnames:
 s=record(R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'/(name+'.lean'));check(s);new.append(s)
assert headers(new[0]['path'])==['Init']+p['direct_imports']
assert headers(new[1]['path'])==['Init','BusyBeaver.ZFC.ArithmeticDagRuntimePerm222']
check(record(__file__))
for x in list(pins.values()):check(x)
result={'status':'ACCEPTED_PROVIDER_SUPPLEMENT_WAITING_EXPLICIT_LAUNCH_APPROVAL','historical_plan':record(planpath),'historical_proposal':record(RES/'c222-dag-runtimeperm222-proposal-20261027.md'),'root_acceptance':record(REV/'arithmetic-dag-rootperm222-root.md'),'root_manifest':record(rmf),'root_state':record(REV/'arithmetic-dag-rootperm222-root-auth/state.json'),'peer_packet':record(peerpath),'peer_manifest':peer['manifest'],'provider_override':replacement,'counts':p['counts'],'new_sources':new,'author_history_qualification':root['unexecuted_historical_input_hash_only'],'planner':record(__file__),'authentication':list(pins.values()),'observations':observations,'scope':'Only the source-matching RootPerm primary is switched to the accepted independent peer provider. No overlay/compiler/refresh/Git action. Historical plan unchanged; one generic unchanged refresh plus two new leaves awaits ROOT launch approval.'}
out=RES/'c222-dag-runtimeperm222-accepted-provider-20261027.json';assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'supplement':record(out),'observations':observations,'paths':len(pins),'counts':p['counts']},indent=2))
