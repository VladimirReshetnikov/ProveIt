from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');rev=R/'Computability/DiophantineConsistency/reviews';parent=Path('/tmp/foundation-ha-arithmetic-root-peer-uqm7vi7q')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
loc=Path('/tmp/foundation-ha-closure-location.txt')
if loc.exists():p=Path(loc.read_text())
else:p=Path(tempfile.mkdtemp(prefix='foundation-ha-closure-root-'));loc.write_text(str(p));(p/'lib/DiophantineConsistency').mkdir(parents=True)
pins=json.loads((parent/'pins.json').read_text());d=json.loads((parent/'packet.json').read_text());mods=d['foundation']+d['nonfoundation'];lib=p/'lib'
for e in mods:
 for obj in e.get('objects',[{'path':e.get('object')} ]):
  q=Path(obj['path']);target=lib/Path(*e['module'].split('.')[:-1])/q.name;target.parent.mkdir(parents=True,exist_ok=True)
  if not target.exists():target.symlink_to(q)
for e in pins:assert sha(e['path'])==e['sha256'],e['path']
compiler=d['compiler']['path'];assert sha(compiler)==d['compiler']['sha256']
for name,e in d['package_identity'].items():assert sha(R/name)==e['current_sha256']
ext=json.loads((rev/'current-positive-zero2011-refresh/manifest.json').read_text())['external_lean_path'];env=os.environ.copy();env['LEAN_PATH']=':'.join([str(lib),*ext]);env.pop('LEAN_SRC_PATH',None)
(p/'inputs.json').write_text(json.dumps({'parent_packet_sha256':sha(parent/'packet.json'),'parent_pins_sha256':sha(parent/'pins.json'),'pins':pins,'modules':mods,'compiler':d['compiler'],'package_identity':d['package_identity'],'lean_path':env['LEAN_PATH']},indent=2)+'\n')
for leaf in sys.argv[1:]:
 assert shutil.disk_usage(p).free>=512*1024*1024
 src=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'/(leaf+'.lean');stamp=str(time.time_ns());snapshot=p/(stamp+'-'+leaf+'.lean');shutil.copyfile(src,snapshot);log=p/(stamp+'-'+leaf+'.log');out=lib/'DiophantineConsistency'/(leaf+'.olean');cmd=[compiler,'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];start=time.time()
 with log.open('w')as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 x={'module':'DiophantineConsistency.'+leaf,'source':str(src),'source_sha256':sha(src),'snapshot':str(snapshot),'snapshot_sha256':sha(snapshot),'command':cmd,'exit_code':code,'seconds':time.time()-start,'log':str(log),'log_sha256':sha(log),'object':str(out),'object_sha256':sha(out)if code==0 else None,'driver_sha256':sha(__file__)}
 for e in pins:assert sha(e['path'])==e['sha256'],e['path']
 (p/(stamp+'-'+leaf+'.json')).write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x),flush=True);print(log.read_text(),flush=True)
 if code:sys.exit(code)
