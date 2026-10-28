from pathlib import Path
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';A=V/'fixed-consistency-nat-cache-audit';loc=Path('/tmp/fixed-consistency73-root-location.txt')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
if sys.argv[1]=='plan':
 plan=A/'refresh-plan.json';assert sha(plan)=='9e3911caaadd1c4a1d18162089dc9a9fcc19865dcd2c9dc7b63838d564d6d530';d=json.loads(plan.read_text());check(d['inventory']);check(d['external_boundaries']);ext=json.loads(Path(d['external_boundaries']['path']).read_text());pins=[rec(plan),d['inventory'],d['external_boundaries'],d['driver'],ext['compiler'],ext['root_toolchain'],ext['root_manifest'],ext['central_manifest']]
 parserfile=V/'current-positive-zero2011-closure/plan.py';assert sha(parserfile)=='fce21bcc246d82485ef1cf99510eedcce4bf9d90e21c0ae34681ea385cac9a34';sp=importlib.util.spec_from_file_location('parser',parserfile);parser=importlib.util.module_from_spec(sp);sp.loader.exec_module(parser);pins.append(rec(parserfile));rows=d['modules'];names={e['module']for e in rows};fresh={e['module']for e in rows if e['action']=='fresh'};boundaries={e['module']:e for e in ext['modules']};seen=set();allimports=set()
 for e in rows:
  check(e['source']);pins.append(e['source']);actual=parser.imports(Path(e['source']['path']));assert set(actual)-{'Init'}==set(e['imports'])-{'Init'},e['module'];e['actual_imports']=actual;allimports.update(actual);assert all(x in seen for x in actual if x in names),e['module'];seen.add(e['module'])
  if e['action']=='reuse':
   assert not any(x in fresh for x in actual);check(e['provenance']);pins.append(e['provenance'])
   for o in e['objects']:check(o);pins.append(o)
  else:assert not e['module'].startswith('Foundation.')
 assert allimports-names==set(boundaries),(allimports-names)^set(boundaries)
 for e in ext['modules']:pins += [e['source'],*e['objects']]
 # Freshly accepted syntax clients replace their source-identical historical providers.
 ep=Path('/tmp/validator-formula-encoder222-root-peer-c0wplw6c/state.json');es=json.loads(ep.read_text());assert es['status']=='PASS';pins.append(rec(ep));replacements=[]
 for c in es['completed'][:3]:
  e=next(x for x in rows if x['module']==c['module']);assert e['action']=='reuse'and e['source']['sha256']==c['source_sha256'];o=dict(path=c['object'],sha256=c['object_sha256']);check(o);pins.append(o);replacements.append(dict(module=e['module'],original=e['objects'],fresh_provider=o));e['objects']=[o]
 g=d['additional_generic_leaf'];check(g['source']);check(g['object']);check(g['provenance']);pins += [g['source'],g['object'],g['provenance']];assert all(x in names for x in parser.imports(Path(g['source']['path']))if x not in boundaries),'generic closure';p=Path(tempfile.mkdtemp(prefix='fixed-consistency73-root-'));lib=p/'lib';lib.mkdir()
 for e in rows+[dict(module=g['module'],action='reuse',objects=[g['object']])]:
  if e['action']=='fresh':continue
  for o in e['objects']:
   q=lib/Path(*e['module'].split('.')[:-1])/Path(o['path']).name;q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(o['path'])
 external=json.loads((V/'current-positive-zero2011-refresh/manifest.json').read_text())['external_lean_path'];pins.append(rec(V/'current-positive-zero2011-refresh/manifest.json'))
 for e in pins:check(e)
 out=dict(status='PLANNED',private=str(p),snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),modules=rows,additional_generic=g,fresh_order=d['fresh_order'],pins=pins,compiler=ext['compiler'],lean_path=':'.join([str(lib),*external]),replacements=replacements,driver=rec(__file__),scope='73 fresh local sources,336 cached closure members plus accepted generic leaf;139 Foundation cached;51 external boundaries. No shared project cache or Foundation build.')
 save(p/'plan.json',out);loc.write_text(str(p));print(json.dumps(dict(private=str(p),fresh=len(fresh),reuse=337,pins=len(pins))))
elif sys.argv[1]=='run':
 p=Path(loc.read_text());plan=p/'plan.json';d=json.loads(plan.read_text());check(d['driver']);env=os.environ.copy();env['LEAN_PATH']=d['lean_path'];env.pop('LEAN_SRC_PATH',None);statefile=p/'state.json'
 if statefile.exists():s=json.loads(statefile.read_text());assert s['status']=='RUNNING'
 else:s=dict(status='RUNNING',plan_sha256=sha(plan),completed=[])
 assert sha(plan)==s['plan_sha256'];done={e['module']for e in s['completed']};assert all(e['exit_code']==0 for e in s['completed']);save(statefile,s)
 for e in d['pins']:check(e)
 for e in s['completed']:
  check(e['source']);check(e['snapshot']);check(e['object']);check(e['log']);text=Path(e['log']['path']).read_text();e['warning_count']=len(re.findall(r'\bwarning:',text));e['axiom_reports']=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)
  for title,ax in e['axiom_reports']:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},title
 save(statefile,s)
 for e in d['modules']:
  if e['action']!='fresh'or e['module']in done:continue
  assert shutil.disk_usage(p).free>=512*1024**2,'512MiB reserve';check(e['source']);n=e['module'];out=p/'lib'/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists()and not out.is_symlink();log=p/(n+'.txt');snapshot=p/(n+'.lean');shutil.copyfile(e['source']['path'],snapshot);cmd=[d['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),e['source']['path']];start=time.time();print('START '+n,flush=True)
  with log.open('w')as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  x=dict(module=n,source=e['source'],snapshot=rec(snapshot),command=cmd,exit_code=code,seconds=time.time()-start,log=rec(log),object=rec(out)if code==0 else None);s['completed'].append(x);save(statefile,s);print(json.dumps(x),flush=True)
  if code:s.update(status='FAILED',failure=n);save(statefile,s);raise SystemExit(code)
  reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());x['axiom_reports']=reports
  for title,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},title
  x['warning_count']=len(re.findall(r'\bwarning:',log.read_text()));assert not re.search(r'\berror:',log.read_text()),'errors '+n;save(statefile,s)
 for e in d['pins']:check(e)
 assert len(s['completed'])==73;s['status']='PASS';save(statefile,s);print('PASS73',flush=True)
else:raise SystemExit('plan or run')
