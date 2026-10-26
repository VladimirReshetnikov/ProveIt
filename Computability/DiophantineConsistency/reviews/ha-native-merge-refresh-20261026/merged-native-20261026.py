from pathlib import Path
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys,tempfile,time,tomllib
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=R/'Computability/DiophantineConsistency';V=B/'reviews';U=Path('/home/codex/.codex/worktrees/62ff/Proofs')
PARSER=V/'current-positive-zero2011-closure/plan.py'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
assert sha(PARSER)=='fce21bcc246d82485ef1cf99510eedcce4bf9d90e21c0ae34681ea385cac9a34'
spec=importlib.util.spec_from_file_location('approved_parser',PARSER);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
loc=Path('/tmp/merged-native-20261026-location.txt')
if sys.argv[1]=='plan':
 p=Path(tempfile.mkdtemp(prefix='merged-native-20261026-'));loc.write_text(str(p));lib=p/'lib';lib.mkdir()
 prp=V/'thirteen-unit-sphere96-replay/prerequisites.json';pr=json.loads(prp.read_text());sp=V/'thirteen-unit-sphere96-replay/REPLAY.json';sphere=json.loads(sp.read_text())
 old={e['module']:dict(source=e['source'],object=e['object'],origin='accepted447')for e in pr['inventory']}
 for e in pr['parent_fresh']+pr['shared_fresh']+sphere['fresh']:
  n='DiophantineConsistency.'+e['module'];src=B/'Lean/DiophantineConsistency'/(e['module']+'.lean')
  old[n]=dict(source=dict(path=str(src),sha256=e['source_sha256']),object=dict(path=e['object'],sha256=e['object_sha256']),origin='accepted-new-size-leaf')
 D=V/'lean-proof-simplification-309-refresh-20261026';mp=D/'manifest.json';xp=D/'execution.json';bp=D/'BUNDLE.json';m=json.loads(mp.read_text());x=json.loads(xp.read_text());bundle=json.loads(bp.read_text())
 assert x['complete'] and len(x['records'])==94 and all(e['actual_exit_code']==0 for e in x['records'])
 for f,e in bundle['files'].items():assert sha(D/f)==e['sha256'],f
 upstream={}
 for e in m['reused_objects']:
  src=R/e['source'];assert sha(src)==m['protected'][e['source']]
  o=dict(path=str(U/e['object']),sha256=e['sha256']);check(o);upstream[str(src)]=dict(source=rec(src),object=o,origin='incoming-authenticated-reuse')
 for e in m['previous_successes']+[e for e in x['records']if'object'in e]:
  src=R/e['source']['path'];assert sha(src)==e['source']['sha256']
  o=dict(path=str(U/e['object']['path']),sha256=e['object']['sha256']);check(o);upstream[str(src)]=dict(source=rec(src),object=o,origin='incoming88-fresh-source')
 changed=[];mods={}
 for n,e in old.items():
  src=Path(e['source']['path']);current=rec(src)
  if current['sha256']!=e['source']['sha256']:changed.append(n)
  check(e['object']);deps=parser.imports(src);use=upstream.get(str(src),e)
  if n not in changed:assert current['sha256']==use['source']['sha256'],n
  mods[n]=dict(module=n,source=current,imports=deps,object=use['object'],origin=use['origin'])
 expected={'DiophantineConsistency.'+n for n in ['CurrentControllerPositions2011','CurrentKernelResidues2011','CurrentWordRephase2011','NativePackingPopulation','NativePellBootstrap','WangTiles942Boundary','WangTiles942Core']}
 assert set(changed)==expected,changed
 roots={e['name']:e.get('srcDir','.')for e in tomllib.loads((R/'lakefile.toml').read_text())['lean_lib']}
 added=set()
 def add_new(n):
  if n in mods or n.split('.')[0]not in roots:return
  src=R/roots[n.split('.')[0]]/Path(*n.split('.')).with_suffix('.lean')
  assert src.is_file(),n
  deps=parser.imports(src);mods[n]=dict(module=n,source=rec(src),imports=deps,object=None,origin='new-fresh-client');added.add(n)
  for dep in deps:add_new(dep)
 for name in ['CarrierScaledAuxiliary118','CarrierScaledAuxiliary118Checks','CurrentWitnessEquivalence2011','CurrentWitnessEquivalence2011Checks','ArithmeticCurrentEquation2011','ArithmeticExpressionChecks','HAEquationStability2011','HAEquationStability2011Checks']:
  add_new('DiophantineConsistency.'+name)
 hp=V/'foundation-ha-theory-transfer-dependency-replay.json';ha=json.loads(hp.read_text());ha_known={e['module']:e for e in ha['modules']};ha_pins=[]
 for n in list(added):
  if n not in ha_known:continue
  e=ha_known[n];src=R/Path(e['source']);assert sha(src)==e['source_sha256']==mods[n]['source']['sha256'],n
  objects=e.get('objects',[dict(path=e.get('object'),sha256=e.get('object_sha256'))])
  for o in objects:check(o);ha_pins.append(o)
  primary=next(o for o in objects if o['path'].endswith('.olean'))
  mods[n].update(object=primary,origin='accepted-HA-current-source-reuse');added.remove(n)
 affected=set(changed)
 while True:
  more={n for n,e in mods.items()if any(d in affected for d in e['imports'])}
  if more<=affected:break
  affected|=more
 fresh=added|{n for n in affected if str(Path(mods[n]['source']['path'])) not in upstream}
 ordered=[];seen=set();visiting=set()
 def visit(n):
  if n in seen:return
  assert n not in visiting,n
  visiting.add(n)
  for d in mods[n]['imports']:
   if d in mods:visit(d)
  visiting.remove(n);seen.add(n);ordered.append(n)
 for n in mods:visit(n)
 oldm=json.loads((V/'ha-postmerge-refresh-20261026/manifest.json').read_text());ext=oldm['external_lean_path'];compiler=next(e for e in oldm['toolchain']if e['path'].endswith('/bin/lean'))
 pins=[rec(f)for f in [PARSER,prp,sp,mp,xp,bp,hp,*[R/n for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']],B/'equation.tex',B/'equation.pdf']]+oldm['toolchain']+ha_pins
 for e in oldm['external_boundary']:
  pins += [e['object'],*e['companions']]+([e['observed_source']]if e['observed_source']else[])
 for n in {dep for e in mods.values()for dep in e['imports']if dep not in mods}:
  q=next((Path(base)/Path(*n.split('.')).with_suffix('.olean')for base in ext if(Path(base)/Path(*n.split('.')).with_suffix('.olean')).is_file()),None)
  assert q is not None,n
  pins += [rec(q)]+[rec(Path(str(q)+suffix))for suffix in ['.private','.server']if Path(str(q)+suffix).is_file()]
 for e in mods.values():
  src=Path(e['source']['path']);committed=subprocess.check_output(['git','show','HEAD:'+str(src.relative_to(R))],cwd=R)
  assert hashlib.sha256(committed).hexdigest()==e['source']['sha256'],e['module']
 for e in pins:check(e)
 for n,e in mods.items():
  q=lib/Path(*n.split('.')).with_suffix('.olean');q.parent.mkdir(parents=True,exist_ok=True)
  e['action']='fresh'if n in fresh else'authenticated-reuse'
  if n not in fresh:q.symlink_to(e['object']['path'])
 plan=dict(snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),upstream='8e13da9d92cf9f4f4aa004d80f34c98fd26ba093',private=str(p),modules=[mods[n]for n in ordered],changed=changed,affected=sorted(affected),fresh=[n for n in ordered if n in fresh],compiler=compiler,external_lean_path=ext,pins=pins,driver_sha256=sha(__file__),scope='Current-source union of accepted453 custom modules, authenticated matching incoming objects and additional target clients. Only missing affected clients and new targets freshly compiled. External packages cached; no whole closure replay.')
 save(p/'plan.json',plan);print(json.dumps(dict(private=str(p),custom=len(mods),changed=len(changed),affected=len(affected),fresh=len(fresh),fresh_order=plan['fresh']),indent=2))
elif sys.argv[1]=='run':
 p=Path(loc.read_text());d=json.loads((p/'plan.json').read_text());assert sha(__file__)==d['driver_sha256'];lib=p/'lib';env=os.environ.copy();env['LEAN_PATH']=':'.join([str(lib),*d['external_lean_path']]);env.pop('LEAN_SRC_PATH',None)
 for e in d['pins']:check(e)
 mods={e['module']:e for e in d['modules']};current={n:e['object']for n,e in mods.items()if e['action']!='fresh'}
 for e in mods.values():
  check(e['source'])
  if e['object']is not None:check(e['object'])
 s=dict(status='RUNNING',plan_sha256=sha(p/'plan.json'),driver_sha256=sha(__file__),completed=[]);save(p/'state.json',s)
 try:
  for n in d['fresh']:
   assert shutil.disk_usage(p).free>=512*1024*1024
   e=mods[n];check(e['source'])
   for dep in e['imports']:
    if dep in current:check(current[dep])
   out=lib/Path(*n.split('.')).with_suffix('.olean');log=p/(n+'.txt');cmd=[d['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),e['source']['path']];start=time.time();s['active']=dict(module=n,command=cmd,log=str(log));save(p/'state.json',s);print(json.dumps(s['active']),flush=True)
   with log.open('w')as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
   result=dict(module=n,command=cmd,source=e['source'],exit_code=code,seconds=time.time()-start,log=rec(log),object=rec(out)if code==0 else None);s['completed'].append(result);s['active']=None;save(p/'state.json',s);assert code==0,n
   reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());result['axiom_reports']=reports
   for title,a in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',a))<={'propext','Quot.sound','Classical.choice'},title
   current[n]=result['object'];save(p/'state.json',s);print(json.dumps(dict(module=n,seconds=result['seconds'],reports=len(reports))),flush=True)
  for n,e in mods.items():check(e['source']);check(current[n])
  for e in d['pins']:check(e)
  s['status']='PASS';save(p/'state.json',s);print('PASS',len(s['completed']),flush=True)
 except BaseException as exc:
  s.update(status='FAILED',failure=str(exc));save(p/'state.json',s);raise
else:raise SystemExit('plan or run')
