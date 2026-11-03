#!/usr/bin/env python3
"""Bounded single-provider author check of compact rank forcing."""
import os,sys,hashlib,json,tempfile,subprocess,shutil,time
from pathlib import Path
H=Path(__file__).resolve().parent
OBS=H/'observations'/sys.argv[1]
OBS.mkdir(parents=True,exist_ok=False)
repo=H.parents[2]/'Lean/DiophantineConsistency/ArithmeticRankForcing.lean'
source=H/'CompactConstructedRank.lean'
provider=Path('/tmp/compact44-halt-rank-overlay-vp7w2rjg')
base=Path('/tmp/ipra-compact-word-cell-author-01/lib')
packing=Path('/tmp/ipra-compact44-symbolic-unit-join/lib')
halt=Path('/tmp/ipra-halt-dimensions-explore-02/lib')
pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
lean='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def inv(p):return {x.name:sha(x) for x in sorted(p.iterdir()) if x.is_file()}
assert shutil.disk_usage('/tmp').free>=4*1024**3
project=provider/'DiophantineConsistency'
assert not (project/'ArithmeticRankForcing.olean').exists()
before=inv(project)
roots=[provider,base,packing,halt]
overlap={}
for i,left in enumerate(roots):
 for right in roots[i+1:]:
  a=inv(left/'DiophantineConsistency'); b=inv(right/'DiophantineConsistency')
  common=sorted(a.keys() & b.keys())
  conflicts=[name for name in common if a[name]!=b[name]]
  overlap[str(left)+' | '+str(right)]={'common':len(common),'conflicts':conflicts}
  if conflicts:raise RuntimeError('project provider conflict: '+str(conflicts))
(OBS/'overlap.json').write_text(json.dumps(overlap,indent=2)+'\n')
source_hashes={str(p):sha(p) for p in (source,repo)}
shutil.copyfile(source,OBS/'client-source.lean')
run=Path(tempfile.mkdtemp(prefix='compact44-constructed-rank-author-'))
(run/'DiophantineConsistency').mkdir()
for entry in project.iterdir():
 if entry.is_file(): (run/'DiophantineConsistency'/entry.name).symlink_to(entry.resolve())
shutil.copyfile(repo,run/'DiophantineConsistency/ArithmeticRankForcing.lean')
shutil.copyfile(source,run/source.name)
env={'PATH':'/usr/bin:/bin','LEAN_NUM_THREADS':'1','LEAN_PATH':':'.join(map(str,[run,provider,base,packing,halt,pkg]))}
steps=[]
for mod in ['DiophantineConsistency/ArithmeticRankForcing','CompactConstructedRank']:
 src=run/(mod+'.lean'); obj=run/(mod+'.olean')
 dep=subprocess.run([lean,'--deps',str(src)],env=env,capture_output=True,text=True,timeout=120)
 (OBS/(mod.split('/')[-1]+'.deps')).write_text(dep.stdout+dep.stderr)
 if dep.returncode or dep.stderr: raise RuntimeError('deps error')
 guards={}
 for x in dep.stdout.splitlines():
  p=Path(x)
  if not p.is_absolute() or not p.is_file() or p.suffix!='.olean':raise RuntimeError('invalid dependency '+x)
  for suf in ['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash']:
   f=Path(str(p)[:-6]+suf); guards[str(f)]=sha(f) if f.is_file() else None
 cmd=[lean,'-M3000','-j1','-DElab.async=false',f'--root={run}',str(src),'-o',str(obj)]
 start=time.monotonic()
 try:
  r=subprocess.run(cmd,env=env,capture_output=True,text=True,timeout=180);code=r.returncode;log=r.stdout+r.stderr
 except subprocess.TimeoutExpired as e:code=None;log=str(e)
 (OBS/(mod.split('/')[-1]+'.log')).write_text(log)
 afterguards={p:sha(p) if Path(p).is_file() else None for p in guards}
 rec={'module':mod,'command':cmd,'exit_code':code,'seconds':round(time.monotonic()-start,3),'source_sha256':sha(src),'object_sha256':sha(obj) if obj.is_file() else None,'guards_before':guards,'guards_unchanged':guards==afterguards}
 steps.append(rec)
 (OBS/'terminal.json').write_text(json.dumps({'run':str(run),'steps':steps,'sources':source_hashes},indent=2)+'\n')
 if code!=0 or not obj.is_file() or guards!=afterguards or any(t in log for t in ('error:','warning:','sorryAx')):raise SystemExit(1)
 if inv(project)!=before or any(sha(p)!=v for p,v in source_hashes.items()):raise RuntimeError('input changed')
(OBS/'provider.json').write_text(json.dumps({'project_count':len(before),'project':before,'unchanged':inv(project)==before},indent=2)+'\n')
print(json.dumps({'run':str(run),'steps':[{k:s[k] for k in ('module','exit_code','seconds','object_sha256')} for s in steps]}))
