from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check(p,h):assert sha(p)==h,str(p)
loc=Path('/tmp/foundation-ha-peano-location.txt')
if loc.exists():p=Path(loc.read_text())
else:p=Path(tempfile.mkdtemp(prefix='foundation-ha-peano-root-'));loc.write_text(str(p));(p/'lib').mkdir()
mods={};pins=[];alternatives=[];parents=[]
def add(e):
 n=e['module'];src=R/Path(e['source']);check(src,e['source_sha256']);pins.append(dict(path=str(src),sha256=e['source_sha256']))
 for key,hashkey in [('cache_source','cache_source_sha256'),('trace','trace_sha256')]:
  if key in e:check(e[key],e[hashkey]);pins.append(dict(path=e[key],sha256=e[hashkey]))
 objects=e.get('objects',[dict(path=e.get('object'),sha256=e.get('object_sha256'))])
 if isinstance(e.get('object'),dict):objects=[e['object']]
 for o in objects:check(o['path'],o['sha256']);pins.append(dict(path=o['path'],sha256=o['sha256']))
 primary=next(o for o in objects if o['path'].endswith('.olean'))
 if n in mods:
  assert mods[n]['source_sha256']==e['source_sha256'],n
  oldprimary=next(o for o in mods[n]['objects']if o['path'].endswith('.olean'))
  if oldprimary['sha256']!=primary['sha256']:alternatives.append(dict(module=n,selected=oldprimary,authenticated_alternate=primary))
 else:mods[n]=dict(module=n,source=str(src),source_sha256=e['source_sha256'],objects=objects)
for name in ['foundation-ha-induction','foundation-ha-theory-transfer','foundation-ha-order-multiplicative','foundation-ha-order-irreflexive','foundation-ha-order-trichotomy']:
 path=V/(name+'-dependency-replay.json');parents.append(dict(path=str(path),sha256=sha(path)));d=json.loads(path.read_text())
 for e in d.get('modules',d.get('foundation',[])+d.get('nonfoundation',[])):add(e)
 for e in d['fresh_modules']:
  if not e['module'].endswith('Checks'):add(e)
 compiler=d['compiler'];package=d['package_identity']
for e in parents:pins.append(e)
check(compiler['path'],compiler['sha256'])
for n,e in package.items():check(R/n,e['current_sha256']);check(Path('/home/codex/src/Proofs')/n,e['cache_sha256'])
lib=p/'lib'
for n,e in mods.items():
 for o in e['objects']:
  q=lib/Path(*n.split('.')[:-1])/Path(o['path']).name;q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():q.symlink_to(o['path'])
ext=json.loads((V/'current-positive-zero2011-refresh/manifest.json').read_text())['external_lean_path'];env=os.environ.copy();env['LEAN_PATH']=':'.join([str(lib),*ext]);env.pop('LEAN_SRC_PATH',None)
inputs=dict(modules=list(mods.values()),pins=pins,parents=parents,compiler=compiler,package_identity=package,lean_path=env['LEAN_PATH'],authenticated_object_alternatives=alternatives)
(p/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
for leaf in sys.argv[1:]:
 assert shutil.disk_usage(p).free>=512*1024*1024
 src=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'/(leaf+'.lean');stamp=str(time.time_ns());snap=p/(stamp+'-'+leaf+'.lean');shutil.copyfile(src,snap);out=lib/'DiophantineConsistency'/(leaf+'.olean');log=p/(stamp+'-'+leaf+'.log');cmd=[compiler['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];start=time.time()
 with log.open('w')as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 x=dict(module='DiophantineConsistency.'+leaf,source=str(src),source_sha256=sha(src),snapshot=str(snap),snapshot_sha256=sha(snap),command=cmd,exit_code=code,seconds=time.time()-start,log=str(log),log_sha256=sha(log),object=str(out),object_sha256=sha(out)if code==0 else None,driver_sha256=sha(__file__))
 for e in pins:check(e['path'],e['sha256'])
 (p/(stamp+'-'+leaf+'.json')).write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x),flush=True);print(log.read_text(),flush=True)
 if code:raise SystemExit(code)
