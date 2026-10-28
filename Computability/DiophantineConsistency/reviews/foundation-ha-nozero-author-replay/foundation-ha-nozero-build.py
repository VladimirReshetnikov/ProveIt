from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile,time
root=Path('/home/codex/.codex/worktrees/46be/Proofs');d=root/'Computability/DiophantineConsistency';rev=d/'reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(b,s):
 if not b:raise RuntimeError(s)
def check(p,h):require(sha(p)==h,'Pin drift '+str(p))
pp=rev/'foundation-ha-order-witnesses-dependency-replay.json';check(pp,'a2de378685941a5072db3f15e54b7f04bbf0833e33b7611f94e328b3a1f9c1ee');r=json.loads(pp.read_text())
mods=r['modules']+[r['fresh_modules'][0]];require(len(mods)==96,'96ordercache')
extras=[]
def metadata(name,pin):
 f=rev/name;check(f,pin);extras.append(dict(path=str(f),sha256=pin));return json.loads(f.read_text())
cl=metadata('foundation-ha-closure-dependency-replay.json','88cf1f0983335cd29fafcc99fbaea13a6c39033e4d822d9885f81e23aae1bfbe')
ar=metadata('arithmetic-expression-replay.json','432c3b1603952c93cab465c3a07ca939913d84f334331b770a28968261419878')
ob=metadata('object-current-equation2011-dependency-replay.json','afdd946ecf76e6c31da7badf138fffc378080b82f0c2e66b8e33b5fd059edddd')
mods += [cl['fresh_modules'][0], ar['fresh'][0]]
for name in ['Representation','ArithmeticRepresentation','NaturalExpression','NaturalExpressionSemiring']:
 m=next(m for m in ob['object_language_dependencies']['modules'] if m['module']=='DiophantineConsistency.'+name)
 o=next(o for o in ar['prior_custom_object_references'] if o['path']=='DiophantineConsistency/'+name+'.olean')
 require(o['sha256']==m['overlay_object_sha256'],'Old selected object inconsistent')
 mods.append(dict(module=m['module'],source=m['source'],source_sha256=m['source_sha256'],object=o['object'],object_sha256=o['sha256'],mode='Exact-source reviewed arithmetic-expression dependency, prior-cache reuse'))
require(len(mods)==102,'102cached');require(len({m['module'] for m in mods})==102,'Module duplicate')

loc=Path('/tmp/foundation-ha-nozero-location.txt')
if loc.exists():p=Path(loc.read_text())
else:p=Path(tempfile.mkdtemp(prefix='foundation-ha-nozero-'));loc.write_text(str(p))
lib=p/'lib';lib.mkdir(exist_ok=True)
def validate():
 for x in r['pins']+extras:check(x['path'],x['sha256'])
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
(p/'inputs.json').write_text(json.dumps(dict(parent=str(pp),parent_sha256=sha(pp),modules=mods,pins=r['pins']+extras,compiler=r['compiler'],package_identity=r['package_identity'],lean_path=env['LEAN_PATH']),indent=2)+'\n')
for leaf in sys.argv[1:]:
 require(shutil.disk_usage(p).free>=512*1024*1024,'Diskreserve')
 src=d/'Lean/DiophantineConsistency'/(leaf+'.lean');stamp=str(time.time_ns());snapshot=p/(stamp+'-'+leaf+'.lean');shutil.copy2(src,snapshot);log=p/(stamp+'-'+leaf+'.log');obj=lib/'DiophantineConsistency'/(leaf+'.olean')
 cmd=[r['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(obj),str(src)];start=time.time()
 with log.open('w')as f:code=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 validate();require(src.read_bytes()==snapshot.read_bytes(),'Source changed during build')
 rec=dict(module='DiophantineConsistency.'+leaf,source=str(src),source_sha256=sha(src),snapshot=str(snapshot),snapshot_sha256=sha(snapshot),command=cmd,exit_code=code,seconds=time.time()-start,log=str(log),log_sha256=sha(log),object=str(obj),object_sha256=sha(obj)if code==0 else None,driver_sha256=sha(__file__))
 (p/(stamp+'-'+leaf+'.json')).write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True);print(log.read_text(),flush=True)
 if code:sys.exit(code)
