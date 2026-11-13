#!/usr/bin/env python3
"""No-Lean driver/source/provider/axiom and fake-control verification."""
import hashlib,importlib.util,json,os,pathlib,re,subprocess,sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated nonoptimized Python required')
P=pathlib.Path;root=P.cwd();base=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';p=base/'compact44-graph-support-carry-pair-prototype';H=lambda x:hashlib.sha256(P(x).read_bytes()).hexdigest();want='430ed6f803dbcbe26590fc0414924b9f006803323eb85e2666b65b0d8cfc462a'
if H(p/'replay.py')!=want:raise ValueError('driver drift')
spec=importlib.util.spec_from_file_location('driver',p/'replay.py');d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d);d.validate_provider()
for f,h in d.PINS.items():
 if not f.is_file() or H(f)!=h:raise ValueError(('fixed pin',str(f)))
scan=json.loads((d.PLAN/'scan.json').read_bytes());parent=json.loads((d.PARENT_AUDIT/'CHECK.json').read_bytes());closure=json.loads((d.CLOSURE_AUDIT/'CHECK.json').read_bytes());rows=[]
if scan['status']!='PRELIMINARY_FIXED_GRAPH_SUPPORT_CARRY_SOURCE_CLOSURE_NOT_A_BUILD' or parent['status']!='PASS_INDEPENDENT_ROTATION_WINDOWS_PAIRED_ARTIFACT_AUDIT' or closure['status']!='PASS_INDEPENDENT_FIXED_GRAPH_SUPPORT_CARRY_SOURCE_CLOSURE':raise ValueError('audit status')
small={'CleanGeometry.finite_disjoint'}
if d.SMALL_AXIOMS!=small or d.AXIOMS!={'propext','Classical.choice','Quot.sound'}:raise ValueError('axiom policy')
logs=base/'compact44-fixed-graph-support-carry-prototype/observations';fixed=logs/'graph-support-attempt01.log'
for r in scan['source_order']:
 f=P(r['source']);s=f.read_text();imports=[x[7:] for x in s.splitlines() if x.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',s,re.M)
 if H(f)!=r['source_sha256'] or imports!=r['imports'] or reports!=r['axiom_reports']:raise ValueError(('source drift',r['module']))
 short=r['module'].split('.')[-1];log=fixed if short=='FixedGraphSupportCarry' else logs/(short+'.log');text=log.read_text()
 if re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text):raise ValueError(('retained log diagnostic',str(log)))
 got=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",text,re.M)
 if len(got)!=len(reports) or {n for n,_ in got}!=set(reports):raise ValueError(('retained report names',str(log)))
 for name,ax in got:
  expected={'propext','Quot.sound'} if name in small else {'propext','Classical.choice','Quot.sound'}
  if {x.strip() for x in ax.split(',') if x.strip()}!=expected:raise ValueError(('actual report mismatch',name,ax))
 d.validate_reports(r['module'],text,reports)
 rows.append({'module':r['module'],'sha256':r['source_sha256'],'imports':imports,'reports':reports,'retained_log_sha256':H(log),'retained_log':str(log)})
if len(rows)!=8 or [x['module'] for x in rows]!=d.MODULES or sum(len(x['reports']) for x in rows)!=16:raise ValueError('source/report inventory')
if [{k:x[k] for k in ('module','sha256','imports','reports')} for x in rows]!=closure['source_rows']:raise ValueError('closure row mismatch')
old=P('/tmp/compact44-aligned-family-plan/lib')
if not old.is_dir():raise ValueError('missing inherited old-provider audit dependency')
for side in ('author','peer'):
 lib=d.PREFIX/side/'lib';live={x.relative_to(lib).as_posix():x for x in lib.rglob('*.olean') if x.is_file()};rec={x['path']:x for x in scan['parent_objects'][side]}
 if len(live)!=203 or set(live)!=set(rec):raise ValueError(('provider count',side))
 for n,f in live.items():
  x=rec[n]
  if str(f.resolve())!=x['realpath'] or H(f)!=x['sha256']:raise ValueError(('provider drift',side,n))

for key,num in [('external_direct_slots',220),('target_slots',160),('package_slots',10)]:
 if len(scan[key])!=num:raise ValueError(('slot count',key))
 for name,item in scan[key].items():
  f=P(name)
  if item is None:
   if os.path.lexists(f):raise ValueError(('unexpected slot',name))
  elif not f.is_file() or str(f.resolve())!=item['realpath'] or H(f)!=item['sha256']:raise ValueError(('slot drift',name))
if any(x is not None for x in scan['target_slots'].values()) or len(d.SUFFIXES)!=10 or len(set(d.SUFFIXES))!=10:raise ValueError('targets or suffixes')
fake=json.loads((p/'observations/fake-observation.json').read_bytes())
if fake['driver_sha256']!=want or fake['fake_controls_sha256']!=H(p/'fake-controls.py') or fake['fake_exit']!=0 or fake['fake_modes']!=43 or fake['fake_aggregate_groups']!=2 or fake['lean_launched'] is not False or fake['real_report_controls_exit']!=0:raise ValueError('fake observation')
outputs={}
for script,log in [('fake-controls.py','fake.stdout'),('real-report-controls.py','real-reports.stdout')]:
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/script)],cwd=root,capture_output=True,timeout=240)
 if r.returncode!=0 or r.stderr or r.stdout!=(p/'observations'/log).read_bytes():raise ValueError(('control rerun mismatch',script,r.returncode,r.stderr))
 outputs[script]={'sha256':H(p/script),'log_sha256':hashlib.sha256(r.stdout).hexdigest(),'exit':r.returncode}
print(json.dumps({'status':'PASS_NO_LEAN_INDEPENDENT_GRAPH_SUPPORT_CARRY_DRIVER_REVIEW','driver_sha256':want,'reviewed_commit':'43785f9971','provider':str(d.PREFIX),'old_read_only_audit_dependency':str(old),'fixed_pin_count':len(d.PINS),'source_modules':len(rows),'named_reports':16,'small_axioms':sorted(small),'source_rows':rows,'parent_objects_per_side':203,'slot_counts':{k:len(scan[k]) for k in ('external_direct_slots','target_slots','package_slots')},'controls':outputs,'lean_launched':False,'scope':'Driver, source and artifact verification only, not independent mathematical proof review; no real preflight or paired build.'},indent=2,sort_keys=True))
