from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile,time
root=Path('/home/codex/.codex/worktrees/46be/Proofs');d=root/'Computability/DiophantineConsistency';rev=d/'reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(b,s):
 if not b:raise RuntimeError(s)
def check(p,h):require(sha(p)==h,'Pin drift '+str(p))
pp=rev/'foundation-ha-order-base-peer-replay/PEER.json';check(pp,'bf133a5cfd82c69a54fb9ffc1ffda1e81549052b59b2c1e2df5e5f284cf1228c');r=json.loads(pp.read_text())
mods=r['modules']+[r['fresh_modules'][0]];require(len(mods)==94,'94cached')
loc=Path('/tmp/foundation-ha-order-additive-location.txt')
if loc.exists():p=Path(loc.read_text())
else:p=Path(tempfile.mkdtemp(prefix='foundation-ha-order-additive-'));loc.write_text(str(p))
lib=p/'lib';lib.mkdir(exist_ok=True)
def validate():
 for x in r['pins']:check(x['path'],x['sha256'])
 check(r['author_packet'],r['author_packet_sha256'])
 check(r['compiler']['path'],r['compiler']['sha256'])
 for name,x in r['package_identity'].items():check(root/name,x['current_sha256'])
 for m in mods:
  check(m['source'],m['source_sha256'])
  if 'trace' in m:check(m['trace'],m['trace_sha256'])
  for o in m.get('objects',[dict(path=m.get('object'),sha256=m.get('object_sha256'))]):check(o['path'],o['sha256'])
validate()
for m in mods:
 for o in m.get('objects',[dict(path=m.get('object'),sha256=m.get('object_sha256'))]):
  target=lib/Path(*m['module'].split('.')[:-1])/Path(o['path']).name;target.parent.mkdir(parents=True,exist_ok=True)
  if not target.exists():target.symlink_to(o['path'])
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(lib),*r['lean_path'].split(':')[1:]]);env.pop('LEAN_SRC_PATH',None)
(p/'inputs.json').write_text(json.dumps(dict(parent=str(pp),parent_sha256=sha(pp),modules=mods,pins=r['pins'],compiler=r['compiler'],package_identity=r['package_identity'],lean_path=env['LEAN_PATH']),indent=2)+'\n')
for leaf in sys.argv[1:]:
 require(shutil.disk_usage(p).free>=512*1024*1024,'Diskreserve')
 src=d/'Lean/DiophantineConsistency'/(leaf+'.lean');stamp=str(time.time_ns());snapshot=p/(stamp+'-'+leaf+'.lean');shutil.copy2(src,snapshot);log=p/(stamp+'-'+leaf+'.log');obj=lib/'DiophantineConsistency'/(leaf+'.olean')
 cmd=[r['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(obj),str(src)];start=time.time()
 with log.open('w')as f:code=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 validate();require(src.read_bytes()==snapshot.read_bytes(),'Source changed during build')
 rec=dict(module='DiophantineConsistency.'+leaf,source=str(src),source_sha256=sha(src),snapshot=str(snapshot),snapshot_sha256=sha(snapshot),command=cmd,exit_code=code,seconds=time.time()-start,log=str(log),log_sha256=sha(log),object=str(obj),object_sha256=sha(obj)if code==0 else None,driver_sha256=sha(__file__))
 (p/(stamp+'-'+leaf+'.json')).write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True);print(log.read_text(),flush=True)
 if code:sys.exit(code)
