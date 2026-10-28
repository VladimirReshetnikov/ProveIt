from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile,time
root=Path('/home/codex/.codex/worktrees/46be/Proofs');d=root/'Computability/DiophantineConsistency';rev=d/'reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(b,s):
 if not b:raise RuntimeError(s)
def check(p,h):require(sha(p)==h,'Pin drift '+str(p))
pp=rev/'foundation-ha-nozero-dependency-replay.json';check(pp,'7df6f5a05338153b6bcda78b825e6191ea5135cdaa0528b88da7987acab3a082');r=json.loads(pp.read_text())
np=rev/'ha-native-merge-refresh-20261026/plan.json';check(np,'9cee732c0a97e05d7868a136b563a0c5de8281a1aec2dec79de83f8d7fa9f1ab');native=json.loads(np.read_text())
sp=np.with_name('state.json');state=json.loads(sp.read_text());require(state['status']=='PASS','Native refresh incomplete');check(np,state['plan_sha256'])
mods=r['modules']+[r['fresh_modules'][0]]
names=['BusyBeaver.Core','BusyBeaver.ZFC.KZip','BusyBeaver.ZFC.KDenseBridge','BusyBeaver.ZFC.KTableCore','BusyBeaver.ZFC.KTable215','BusyBeaver.ZFC.KDense215','DiophantineConsistency.DecimalMachine215','DiophantineConsistency.WangTiles942Data']
for name in names:
 m=next(m for m in native['modules'] if m['module']==name);require(m['action']=='authenticated-reuse','Unexpected refreshed dependency')
 mods.append(dict(module=name,source=m['source']['path'],source_sha256=m['source']['sha256'],object=m['object']['path'],object_sha256=m['object']['sha256'],mode='Exact-source accepted native469 inventory reuse; no fresh replay here',origin=m['origin']))
require(len(mods)==111 and len({m['module'] for m in mods})==111,'111distinct cached modules')
extra=[dict(path=str(pp),sha256=sha(pp)),dict(path=str(np),sha256=sha(np)),dict(path=str(sp),sha256=sha(sp))]
loc=Path('/tmp/current-equation-narrow-location.txt')
if loc.exists():p=Path(loc.read_text())
else:p=Path(tempfile.mkdtemp(prefix='current-equation-narrow-'));loc.write_text(str(p))
lib=p/'lib';lib.mkdir(exist_ok=True)
def validate():
 for x in r['pins']+extra:check(x['path'],x['sha256'])
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
(p/'inputs.json').write_text(json.dumps(dict(parent=str(pp),parent_sha256=sha(pp),native_inventory=str(np),native_inventory_sha256=sha(np),modules=mods,pins=r['pins']+extra,compiler=r['compiler'],package_identity=r['package_identity'],lean_path=env['LEAN_PATH']),indent=2)+'\n')
for leaf in sys.argv[1:]:
 require(shutil.disk_usage(p).free>=512*1024*1024,'Diskreserve')
 src=d/'Lean/DiophantineConsistency'/(leaf+'.lean');stamp=str(time.time_ns());snapshot=p/(stamp+'-'+leaf+'.lean');shutil.copy2(src,snapshot);log=p/(stamp+'-'+leaf+'.log');obj=lib/'DiophantineConsistency'/(leaf+'.olean')
 cmd=[r['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(obj),str(src)];start=time.time()
 with log.open('w')as f:code=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 validate();require(src.read_bytes()==snapshot.read_bytes(),'Source changed during build')
 rec=dict(module='DiophantineConsistency.'+leaf,source=str(src),source_sha256=sha(src),snapshot=str(snapshot),snapshot_sha256=sha(snapshot),command=cmd,exit_code=code,seconds=time.time()-start,log=str(log),log_sha256=sha(log),object=str(obj),object_sha256=sha(obj)if code==0 else None,driver_sha256=sha(__file__))
 (p/(stamp+'-'+leaf+'.json')).write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True);print(log.read_text(),flush=True)
 if code:sys.exit(code)
