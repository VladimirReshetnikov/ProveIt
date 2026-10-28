from pathlib import Path
import hashlib,json,os,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');H=R/'Computability/DiophantineConsistency/research'
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
plan=H/'arithmetic-pell-auxiliary-seed-cache-plan.json';j=json.loads(plan.read_text());seen=set();count=0
assert rec(plan)['sha256']=='59de0e399ed01693294f7c5d6363287c5268797619abc9a2f4b42b0f7ebc3e35'
def check(x):
 global count
 if isinstance(x,dict):
  if {'path','sha256'}<=x.keys():
   a=rec(x['path']);assert a['sha256']==x['sha256'],x['path']
   if 'bytes'in x:assert a['bytes']==x['bytes']
   count+=1;seen.add(a['path'])
  for k,v in x.items():check(v)
 elif isinstance(x,list):
  for v in x:check(v)
check(j)
assert shutil.disk_usage('/tmp').free>=512*1024**2
out=H/'arithmetic-pell-auxiliary-seed-plan-authentication.json';assert not out.exists()
proposal=H/'arithmetic-pell-auxiliary-seed-proposal.md';auditor=H/'arithmetic-pell-auxiliary-seed-cache-audit.py';frozen=H/'arithmetic-pell-auxiliary-seed-plan-freeze.py'
assert rec(auditor)['sha256']==j['auditor']['sha256'];assert not frozen.exists();shutil.copyfile(__file__,frozen)
save(out,dict(status='READ_ONLY_PASS_NO_LEAN_OR_OVERLAY',plan=rec(plan),proposal=rec(proposal),auditor=rec(auditor),freeze=rec(frozen),comparisons=count,unique_paths=len(seen),counts=j['counts']))
files=[plan,proposal,auditor,frozen,out];mf=H/'arithmetic-pell-auxiliary-seed-plan-FILES.json';assert not mf.exists()
save(mf,[dict(rec(p),path=str(p.relative_to(R)))for p in files])
print(json.dumps(dict(proposal=rec(proposal),plan=rec(plan),manifest=rec(mf),comparisons=count,unique_paths=len(seen)),indent=2))
