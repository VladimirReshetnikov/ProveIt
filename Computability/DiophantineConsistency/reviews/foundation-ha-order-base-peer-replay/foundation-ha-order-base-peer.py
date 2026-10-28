from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
root=Path('/home/codex/.codex/worktrees/46be/Proofs');d=root/'Computability/DiophantineConsistency';rev=d/'reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(b,s):
 if not b:raise RuntimeError(s)
def check(p,h):require(sha(p)==h,'Pin drift '+str(p))
packet=rev/'foundation-ha-order-base-dependency-replay.json';check(packet,'8fc56248155a5a7ac4eea743d21707ca5e0a0c5ed954de9612c8add527e93682');r=json.loads(packet.read_text());author=rev/'foundation-ha-order-base-author-replay'
for f,h in r['bundle_files'].items():check(author/f,h)
inputs=json.loads((author/'inputs.json').read_text());check(author/'inputs.json',r['inputs_sha256'])
p=Path(tempfile.mkdtemp(prefix='foundation-ha-order-base-peer-'));lib=p/'lib';lib.mkdir()
def validate():
 for x in inputs['pins']:check(x['path'],x['sha256'])
 check(r['compiler']['path'],r['compiler']['sha256'])
 for name,x in r['package_identity'].items():check(root/name,x['current_sha256'])
 for x in r['prior_manifests']:check(root/x['path'],x['sha256'])
 for m in r['fresh_modules']:check(m['source'],m['source_sha256'])
validate()
require(len(r['modules'])==93,'Prerequisite count')
for m in r['modules']:
 check(m['source'],m['source_sha256'])
 if 'trace' in m:check(m['trace'],m['trace_sha256'])
 for o in m.get('objects',[dict(path=m.get('object'),sha256=m.get('object_sha256'))]):
  check(o['path'],o['sha256']);target=lib/Path(*m['module'].split('.')[:-1])/Path(o['path']).name;target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(o['path'])
ext=inputs['lean_path'].split(':')[1:];env=os.environ.copy();env['LEAN_PATH']=':'.join([str(lib),*ext]);env.pop('LEAN_SRC_PATH',None)
results=[]
for m in r['fresh_modules']:
 require(shutil.disk_usage(p).free>=512*1024*1024,'Disk reserve')
 src=Path(m['source']);snapshot=p/src.name;shutil.copy2(src,snapshot);log=p/(src.stem+'.log');obj=lib/Path(*m['module'].split('.')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 cmd=[r['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(obj),str(src)];start=time.time()
 with log.open('w')as f:code=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 validate();rec=dict(module=m['module'],source=str(src),source_sha256=sha(src),object=str(obj),object_sha256=sha(obj) if code==0 else None,command=cmd,exit_code=code,seconds=time.time()-start,log=str(log),log_sha256=sha(log),author_object_sha256=m['object_sha256'],object_identical=(code==0 and sha(obj)==m['object_sha256']));results.append(rec);print(json.dumps(rec),flush=True)
 require(code==0,'Build failed, see '+str(log))
 require(not re.search(r'error:|warning:|sorryAx',log.read_text()),'Diagnostics')
require(not Path(results[0]['log']).read_bytes(),'Main log not empty')
reports=re.findall(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",Path(results[1]['log']).read_text(),re.S)
require(len(reports)==10,'Expected10reports')
for name,_,axs in reports:require(set(x.strip() for x in axs.split(',') if x.strip())<= {'propext','Quot.sound'},'Unexpected axiom '+name)
result=dict(reviewer='circuit_reduction',scope='Independent full source review and two fresh leaves;93 exact-source/object prerequisite modules reused, no closure rebuild.',private=str(p),snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),author_packet=str(packet),author_packet_sha256=sha(packet),compiler=r['compiler'],package_identity=r['package_identity'],modules=r['modules'],pins=inputs['pins'],lean_path=env['LEAN_PATH'],fresh_modules=results,axiom_reports=[dict(theorem=n,axioms=[x.strip()for x in a.split(',')if x.strip()])for n,_,a in reports],driver_sha256=sha(__file__))
bundle=rev/'foundation-ha-order-base-peer-replay';bundle.mkdir(exist_ok=True)
for f in [*p.glob('*.lean'),*p.glob('*.log'),Path(__file__)]:shutil.copy2(f,bundle/f.name)
result['bundle_files']={f.name:sha(f)for f in sorted(bundle.iterdir())}
out=bundle/'PEER.json';out.write_text(json.dumps(result,indent=2)+'\n');print('PEER',sha(out),p,flush=True)
