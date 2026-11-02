#!/usr/bin/env python3
"""Independent read-only fixed clean-carry artifact audit; no Lean execution."""
import hashlib,importlib.util,json,os,pathlib,re,subprocess,sys
P=pathlib.Path;root=P.cwd();base=root/'Computability/DiophantineConsistency';research=base/'research/ordinary12-ipra-bridge';pkg=research/'compact44-fixed-clean-carry-pair-prototype';evidence=pkg/'evidence';out=P('/tmp/ipra-fixed-clean-carry-pair-01');H=lambda p:hashlib.sha256(P(p).read_bytes()).hexdigest();wanted='423e649f00ef18759a953855f1d13c436dccf8c887430e7c201d21ef4fa4ddf1';driver_hash='b636767b6c9ca4d847d62fbf0d674abb03f07969ac1ca50bf41148cbad637bb6';head='4d5474f10e00412135d659dc7a1f74fc6457656a'
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated nonoptimized Python required')
if H(pkg/'replay.py')!=driver_hash or H(evidence/'receipt.json')!=wanted or H(out/'receipt.json')!=wanted:raise ValueError('driver or receipt mismatch')
spec=importlib.util.spec_from_file_location('driver',pkg/'replay.py');d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d)
scan=json.loads((d.PLAN/'scan.json').read_bytes());receipt=json.loads((evidence/'receipt.json').read_bytes());term=json.loads((evidence/'terminal-observation.json').read_bytes());pre=json.loads((evidence/'preflight-observation.json').read_bytes())
if receipt['status']!='PASS_PAIRED_FIXED_CLEAN_CARRY' or receipt['protected_head']!=head or receipt['driver_sha256']!=driver_hash or len(receipt['guards'])!=1090:raise ValueError('receipt metadata')
if type(term['observed_exit']) is not int or term['observed_exit']!=0 or term['receipt_sha256']!=wanted or term['protected_head']!=head or term['source_path']!=str(out) or term['lean_processes_remaining'] is not False:raise ValueError('terminal observation')
prefout=json.loads((evidence/'preflight.stdout').read_bytes());pairout=json.loads((evidence/'pair.stdout').read_bytes())
if type(pre['observed_exit']) is not int or pre['observed_exit']!=0 or pre['protected_head']!=head or pre['lean_launched'] is not False or H(evidence/'preflight.stdout')!=pre['stdout_sha256'] or H(evidence/'preflight.stderr')!=pre['stderr_sha256'] or (evidence/'preflight.stderr').stat().st_size!=0 or prefout!={'status':'PASS_FIXED_CLEAN_CARRY_READ_ONLY_PREFLIGHT','driver_sha256':driver_hash,'expected_head':head,'source_modules':33,'parent_audit_status':'PASS_INDEPENDENT_ROTATION_WINDOWS_PAIRED_ARTIFACT_AUDIT','lean_launched':False}:raise ValueError('preflight observation')
if H(evidence/'pair.stdout')!=term['wrapper_stdout_sha256'] or H(evidence/'pair.stderr')!=term['wrapper_stderr_sha256'] or (evidence/'pair.stderr').stat().st_size!=0 or pairout!={'status':'PASS_PAIRED_FIXED_CLEAN_CARRY','receipt_sha256':wanted}:raise ValueError('wrapper output')
if H(evidence/'progress.json')!=term['progress_sha256'] or H(out/'progress.json')!=term['progress_sha256']:raise ValueError('progress drift')
if receipt['fixed_pins']!={str(p):h for p,h in d.PINS.items()}:raise ValueError('fixed pin inventory')
for p,h in d.PINS.items():
 if not p.is_file() or H(p)!=h:raise ValueError(('pin drift',str(p)))
rows=scan['source_order'];
if len(rows)!=33 or [x['module'] for x in rows]!=d.MODULES or sum(len(x['axiom_reports']) for x in rows)!=54:raise ValueError('source inventory')
frozen=out/'frozen/DiophantineConsistency';
if out.is_symlink() or (out/'frozen').is_symlink() or frozen.is_symlink():raise ValueError('frozen directory redirection')
for row in rows:
 original=P(row['source']); f=frozen/(row['module'].split('.')[-1]+'.lean');t=f.read_text();imports=[x[7:] for x in t.splitlines() if x.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',t,re.M)
 if f.is_symlink() or not f.is_file() or H(f)!=row['source_sha256'] or H(original)!=row['source_sha256'] or imports!=row['imports'] or reports!=row['axiom_reports']:raise ValueError(('source drift',row['module']))
 blob=subprocess.run(['git','show',row['source_commit']+':'+original.relative_to(root).as_posix()],cwd=root,capture_output=True,check=True,timeout=60).stdout
 if hashlib.sha256(blob).hexdigest()!=row['source_sha256']:raise ValueError(('source commit drift',row['module']))
if [r['side'] for r in receipt['runs']]!=['author','peer']:raise ValueError('side order')
package=d.PACKAGE;slots=d.SUFFIXES; expected_guards=set();summaries=[]
for side,run in zip(('author','peer'),receipt['runs']):
 lib=out/side/'lib';
 if lib.is_symlink() or lib.parent.is_symlink() or len(run['steps'])!=33:raise ValueError(('side dirs/count',side))
 actual={p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()};parents={x['path']:x for x in scan['parent_objects'][side]};new={str(pathlib.Path(*x['module'].split('.')).with_suffix('.olean')) for x in rows}
 if len(actual)!=236 or set(actual)!=set(parents)|new or set(parents)&new:raise ValueError(('full overlay inventory',side,len(actual)))
 for name,item in parents.items():
  p=actual[name]
  if not p.is_file() or str(p.resolve())!=item['realpath'] or H(p)!=item['sha256']:raise ValueError(('inherited object drift',side,name))
 for row,step in zip(rows,run['steps']):
  name=row['module'];obj=(lib/P(*name.split('.'))).with_suffix('.olean');src=frozen/(name.split('.')[-1]+'.lean');log=out/side/(name.replace('.','_')+'.log');saved=evidence/side/log.name
  if step['module']!=name or step['source_sha256']!=row['source_sha256'] or type(step['compiler_exit']) is not int or step['compiler_exit']!=0 or step['stop_reason'] is not None or step['deps_exit']!=0 or type(step['sampled_peak_rss_bytes']) is not int or not 0<step['sampled_peak_rss_bytes']<=int(3.5*1024**3):raise ValueError(('step status',side,name))
  if obj.is_symlink() or not obj.is_file() or H(obj)!=step['object_sha256'] or log.is_symlink() or not log.is_file() or H(log)!=step['log_sha256'] or not saved.is_file() or H(saved)!=step['log_sha256'] or log.read_text()!=step['stdout']:raise ValueError(('output drift',side,name))
  expected_cmd=[str(d.LEAN),'-M3000','-j1','-DElab.async=false','--root='+str(out/'frozen'),str(src),'-o',str(obj)]
  if step['command']!=expected_cmd:raise ValueError(('command mismatch',side,name))
  expected={str(package/'Init.olean')}
  for dep in row['imports']:
   p=((lib if dep.startswith('DiophantineConsistency.') else package)/P(*dep.split('.'))).with_suffix('.olean')
   if not p.is_file():raise ValueError(('missing direct import',side,name,dep))
   expected.add(str(p))
  lines=step['deps_stdout'].splitlines();init=str(package/'Init.olean')
  if set(lines)!=expected or not 1<=lines.count(init)<=2 or any(lines.count(x)!=1 for x in expected if x!=init):raise ValueError(('dependency mismatch',side,name))
  for item in expected|{str(obj)}:
   for suffix in slots:expected_guards.add(item[:-6]+suffix)
  clean=log.read_text()
  if re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',clean):raise ValueError(('unexpected output diagnostic',side,name))
  reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",clean,re.M)
  if len(reports)!=len(row['axiom_reports']) or {x[0] for x in reports}!=set(row['axiom_reports']) or any({x.strip() for x in ax.split(',') if x.strip()}!=({'propext','Quot.sound'} if n in {'CleanGeometry.finite_disjoint','CleanTargetPhase.finite_relation'} else {'propext','Classical.choice','Quot.sound'}) for n,ax in reports) or [list(x) for x in reports]!=step['axiom_reports']:raise ValueError(('report mismatch',side,name))
  summaries.append({'side':side,'module':name,'source_sha256':row['source_sha256'],'object_sha256':step['object_sha256'],'log_sha256':step['log_sha256'],'reports':len(reports)})
if expected_guards!=set(receipt['guards']):raise ValueError(('guard inventory mismatch',len(expected_guards),len(receipt['guards'])))
for name,prior in receipt['guards'].items():
 p=P(name)
 if prior is None:
  if os.path.lexists(p):raise ValueError(('unexpected companion',name))
 elif not p.is_file() or str(p.resolve())!=prior['realpath'] or H(p)!=prior['sha256']:raise ValueError(('guard drift',name))
strip=lambda x:{k:v for k,v in x.items() if k not in ('command','deps_stdout','sampled_peak_rss_bytes')}
if [strip(x) for x in receipt['runs'][0]['steps']]!=[strip(x) for x in receipt['runs'][1]['steps']]:raise ValueError('paired outputs differ')
progress=json.loads((evidence/'progress.json').read_bytes())
if progress['completed']!=[receipt['runs'][0]] or progress['current']['side']!='peer' or progress['current']['steps']!=receipt['runs'][1]['steps']:raise ValueError('progress/receipt mismatch')
parent=P(base/'reviews/compact44-rotation-windows-pair-independent-audit/audit.py');r=subprocess.run([sys.executable,'-I','-S','-B',str(parent)],cwd=root,capture_output=True,timeout=1800)
if r.returncode!=0 or r.stderr or json.loads(r.stdout)!=receipt['parent_audit']:raise ValueError(('independent parent rerun',r.returncode,r.stderr))
closure=d.CLOSURE_AUDIT/'audit.py';cr=subprocess.run([sys.executable,'-I','-S','-B',str(closure)],cwd=root,capture_output=True,timeout=2400)
if cr.returncode!=0 or cr.stderr or json.loads(cr.stdout)!=json.loads((d.CLOSURE_AUDIT/'CHECK.json').read_bytes()):raise ValueError(('independent closure rerun',cr.returncode,cr.stderr))
print(json.dumps({'status':'PASS_INDEPENDENT_FIXED_CLEAN_CARRY_PAIRED_ARTIFACT_AUDIT','reviewed_evidence_commit':'2bc682f80c','receipt_sha256':wanted,'protected_head':head,'recorded_outer_exit':term['observed_exit'],'recorded_preflight_scope':'preflight stdout and stderr retained and hashed','source_modules':33,'rows_checked':len(summaries),'named_reports_per_side':54,'overlay_objects_per_side':236,'guard_slots':len(expected_guards),'fixed_pins':len(receipt['fixed_pins']),'parent_audit_exit':r.returncode,'closure_audit_exit':cr.returncode,'lean_launched':False,'rows':summaries,'scope':'Source/artifact verification by an author of several clients, not independent mathematical review; graph zero and positivity are assumed, and raw-column decoder identity, retained-byte binding, machine correctness and internal iPRA proof remain open.'},indent=2,sort_keys=True))
