#!/usr/bin/env python3
"""Independent no-Lean driver/source/guard check; not a math-proof review."""
import hashlib,importlib.util,json,os,pathlib,re,subprocess,sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated nonoptimized Python required')
P=pathlib.Path;root=P.cwd();base=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';p=base/'compact44-graph-temporal-carry-pair-prototype';H=lambda x:hashlib.sha256(P(x).read_bytes()).hexdigest();want='77f9ef885be8d5a22448f694e21929a5ae328037948246034d9322d03ac6564d'
if H(p/'replay.py')!=want:raise ValueError('driver drift')
spec=importlib.util.spec_from_file_location('driver',p/'replay.py');d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d);d.validate_provider()
for f,h in d.PINS.items():
 if not f.is_file() or H(f)!=h:raise ValueError(('fixed pin',str(f)))
scan=json.loads((d.PLAN/'scan.json').read_bytes());parent=json.loads((d.PARENT_AUDIT/'CHECK.json').read_bytes());closure=json.loads((d.CLOSURE_AUDIT/'CHECK.json').read_bytes());rows=[]
if scan['status']!='PRELIMINARY_GRAPH_TEMPORAL_CARRY_SOURCE_CLOSURE_NOT_A_BUILD' or parent['status']!='PASS_INDEPENDENT_GRAPH_BAND_PAIRED_ARTIFACT_AUDIT' or closure['status']!='PASS_INDEPENDENT_GRAPH_TEMPORAL_CARRY_SOURCE_CLOSURE':raise ValueError('audit status')
for r in scan['source_order']:
 f=P(r['source']);s=f.read_text();imports=[x[7:] for x in s.splitlines() if x.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',s,re.M)
 if H(f)!=r['source_sha256'] or imports!=r['imports'] or reports!=r['axiom_reports']:raise ValueError(('source drift',r['module']))
 text=''.join("'"+x+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for x in reports);d.validate_reports(r['module'],text,reports)
 rows.append({'module':r['module'],'sha256':r['source_sha256'],'imports':imports,'reports':reports})
if len(rows)!=7 or [x['module'] for x in rows]!=d.MODULES or sum(len(x['reports']) for x in rows)!=22 or rows!=closure['source_rows']:raise ValueError('source/report inventory')
for side in ('author','peer'):
 lib=d.PREFIX/side/'lib';live={x.relative_to(lib).as_posix():x for x in lib.rglob('*.olean') if x.is_file()};rec={x['path']:x for x in scan['parent_objects'][side]}
 if len(live)!=171 or set(live)!=set(rec):raise ValueError(('provider count',side))
 for n,f in live.items():
  x=rec[n]
  if str(f.resolve())!=x['realpath'] or H(f)!=x['sha256']:raise ValueError(('provider drift',side,n))
for key,num in [('external_direct_slots',60),('target_slots',140),('package_slots',20)]:
 if len(scan[key])!=num:raise ValueError(('slot count',key))
 for name,item in scan[key].items():
  f=P(name)
  if item is None:
   if os.path.lexists(f):raise ValueError(('unexpected slot',name))
  elif not f.is_file() or str(f.resolve())!=item['realpath'] or H(f)!=item['sha256']:raise ValueError(('slot drift',name))
if any(x is not None for x in scan['target_slots'].values()) or len(d.SUFFIXES)!=10 or len(set(d.SUFFIXES))!=10:raise ValueError('targets or suffixes')
fake=json.loads((p/'observations/fake-observation.json').read_bytes())
if fake['driver_sha256']!=want or fake['fake_controls_sha256']!=H(p/'fake-controls.py') or fake['fake_exit']!=0 or fake['fake_modes']!=44 or fake['fake_aggregate_groups']!=2 or fake['lean_launched'] is not False:raise ValueError('fake observation')
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'fake-controls.py')],cwd=root,capture_output=True,timeout=240)
if r.returncode!=0 or r.stderr or r.stdout!=(p/'observations/fake.stdout').read_bytes():raise ValueError(('fake rerun mismatch',r.returncode,r.stderr))
print(json.dumps({'status':'PASS_NO_LEAN_INDEPENDENT_TEMPORAL_CARRY_DRIVER_REVIEW','driver_sha256':want,'provider':str(d.PREFIX),'fixed_pin_count':len(d.PINS),'source_modules':len(rows),'named_reports':22,'source_rows':rows,'parent_objects_per_side':171,'slot_counts':{k:len(scan[k]) for k in ('external_direct_slots','target_slots','package_slots')},'fake_controls_sha256':H(p/'fake-controls.py'),'fake_log_sha256':hashlib.sha256(r.stdout).hexdigest(),'fake_exit':r.returncode,'lean_launched':False,'scope':'Source/artifact driver verification by an author of several clients, not independent mathematical proof review; no real preflight or paired build.'},indent=2,sort_keys=True))
