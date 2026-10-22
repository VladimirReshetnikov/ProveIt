from pathlib import Path
import hashlib,json,subprocess
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');O=Path('/tmp/k215-upstream565-review')
BASE='57541fe0cfe3af62b4cb58747d8d1d7c16b338d5';TIP='565936b4774b7c8d4f078d1c11d03baaf7da8897'
def git(*xs):return subprocess.check_output(['git',*xs],cwd=R)
def sha(b):return hashlib.sha256(b).hexdigest()
def saved(rel,data):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);return str(p)
def at(rev,path):
 raw=git('ls-tree',rev,'--',path).decode().strip()
 if not raw:return {'exists':False}
 info,name=raw.split('\t');mode,kind,obj=info.split();assert kind=='blob' and name==path
 b=git('cat-file','blob',obj)
 return {'exists':True,'mode':mode,'git_blob':obj,'sha256':sha(b),'bytes':len(b),'snapshot':saved('inputs/'+rev[:10]+'/'+path,b)}
changes=[x.split('\t') for x in git('diff','--name-status',BASE,TIP).decode().splitlines()]
assert len(changes)==11 and all(len(x)==2 for x in changes)
protected=['Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DominatedImplication.lean','Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Lukasiewicz.lean','Computability/BusyBeaver/Research/ZFC/k225-formal/generate_dominated_implication_lean.py','Computability/BusyBeaver/Research/ZFC/k225-formal/rho8cd/derivation_core.txt','Computability/BusyBeaver/Research/ZFC/k225-formal/rho8cd/generate_domrho8_cd.py']
pins={p:sha((R/p).read_bytes()) for p in protected}
rows=[]
for status,path in changes:
 b=at(BASE,path);u=at(TIP,path);p=R/path
 c={'exists':p.exists()}
 if p.exists():
  data=p.read_bytes();c|={'mode':format(p.stat().st_mode&0o777,'o'),'git_mode':'100755' if p.stat().st_mode&0o111 else '100644','git_blob_from_raw_bytes':sha(b'blob '+str(len(data)).encode()+b'\0'+data) if False else hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest(),'sha256':sha(data),'bytes':len(data),'snapshot':saved('current/'+path,data),'same_as_base':b.get('sha256')==sha(data),'same_as_upstream':u['sha256']==sha(data)}
 lean=path.endswith('.lean')
 rows.append({'path':path,'status':status,'base':b,'upstream':u,'checked_worktree':c,'merge_decision':'retain_exact_checked_worktree' if lean else 'import_exact_upstream_research_data_only','execution':'none'})
assert sum(x['path'].endswith('.lean') for x in rows)==4
assert all(x['checked_worktree'].get('same_as_base') for x in rows[:4])
assert {p:sha((R/p).read_bytes()) for p in protected}==pins
res={'status':'READ_ONLY_EXACT_ELEVEN_PATH_CENSUS','base':BASE,'upstream':TIP,'head_at_census':git('rev-parse','HEAD').decode().strip(),'rows':rows,'preserve_four_lean':[r['path'] for r in rows if r['path'].endswith('.lean')],'import_seven_as_research_data':[r['path'] for r in rows if not r['path'].endswith('.lean')],'phase13_five_adopted_before_after':pins,'scope':'Git reads and raw byte snapshots only. No compiler, producer, submitted code, canonical edit, index mutation or adoption. Upstream research paths are proposal data, not checked Rocq production.'}
saved('preservation-map.json',json.dumps(res,indent=2).encode()+b'\n')
saved('lean.diff',git('diff',BASE,TIP,'--',*[r['path'] for r in rows if r['path'].endswith('.lean')]))
saved('research.diff',git('diff',BASE,TIP,'--',*[r['path'] for r in rows if not r['path'].endswith('.lean')]))
saved('commits.txt',git('log','--format=%H %s',BASE+'..'+TIP))
print('rows',len(rows),'map_sha256',sha((O/'preservation-map.json').read_bytes()))
for r in rows:print(r['status'],r['path'],r['upstream']['git_blob'],r['upstream']['sha256'],r['upstream']['bytes'])
