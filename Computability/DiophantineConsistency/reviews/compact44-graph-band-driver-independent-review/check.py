#!/usr/bin/env python3
"""Independent no-Lean graph-band driver inventory and full fake controls."""
import hashlib,importlib.util,json,os,pathlib,re,subprocess,sys
P=pathlib.Path.cwd()/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-graph-band-pair-prototype';H=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated nonoptimized Python required')
D=P/'replay.py';want='45f12818c65247286c5d71f5d1805f0eb3a6a3ce4ed37327b1aa70d6fad249f8'
if H(D)!=want:raise ValueError('driver mismatch')
spec=importlib.util.spec_from_file_location('reviewed_driver',D);d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d);d.validate_provider()
for p,h in d.PINS.items():
 if not p.is_file() or H(p)!=h:raise ValueError(('fixed pin mismatch',str(p)))
scan=json.loads((d.PLAN/'scan.json').read_bytes());closure=json.loads((d.CLOSURE_AUDIT/'CHECK.json').read_bytes());survey=json.loads(d.SURVEY.read_bytes());rows=[]
for row in scan['source_order']:
 p=pathlib.Path(row['source']);s=p.read_text();imports=[x[7:] for x in s.splitlines() if x.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',s,re.M)
 if H(p)!=row['source_sha256'] or imports!=row['imports'] or reports!=row['axiom_reports']:raise ValueError(('source/import/report mismatch',str(p)))
 text=''.join("'"+x+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for x in reports);d.validate_reports(row['module'],text,reports)
 rows.append({'module':row['module'],'sha256':row['source_sha256'],'imports':imports,'reports':reports})
if [r['module'] for r in rows]!=d.MODULES or len(rows)!=21 or sum(len(r['reports']) for r in rows)!=35:raise ValueError('source order or report count')
expected_warnings=[{'module':r['module'],'suffix':s} for r in survey['entries'] for s in r['warning_suffixes']]
if [x['module'] for x in expected_warnings]!=['ArithmeticCyclicWord','ArithmeticWindowCarry'] or expected_warnings!=closure['first_14_warning_inventory']:raise ValueError('warning inventory')
for r in expected_warnings:
 row=next(x for x in scan['source_order'] if x['module']=='DiophantineConsistency.'+r['module']);sv=next(x for x in survey['entries'] if x['module']==r['module'])
 if row['source_sha256']!=sv['source_sha256'] or row['axiom_reports'] or 'warning:' not in r['suffix']:raise ValueError(('warning source/report mismatch',r['module']))
for side in ('author','peer'):
 objs=scan['parent_objects'][side]
 if len(objs)!=150:raise ValueError(('parent count',side))
 for item in objs:
  p=d.PREFIX/side/'lib'/item['path']
  if not p.is_file() or str(p.resolve())!=item['realpath'] or H(p)!=item['sha256']:raise ValueError(('provider drift',str(p)))
for k,count in (('external_direct_slots',120),('target_slots',420),('package_slots',30)):
 if len(scan[k])!=count:raise ValueError(('slot count',k))
 for name,v in scan[k].items():
  p=pathlib.Path(name)
  if v is None:
   if os.path.lexists(p):raise ValueError(('unexpected slot',name))
  elif not p.is_file() or str(p.resolve())!=v['realpath'] or H(p)!=v['sha256']:raise ValueError(('slot drift',name))
if any(v is not None for v in scan['target_slots'].values()):raise ValueError('target occupied')
fake=json.loads((P/'observations/fake-observation.json').read_bytes())
if fake['driver_sha256']!=want or fake['fake_controls_sha256']!=H(P/'fake-controls.py') or fake['fake_exit']!=0 or fake['lean_launched'] is not False or fake['fake_modes']!=45 or fake['fake_aggregate_groups']!=2:raise ValueError('fake observation')
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'fake-controls.py')],capture_output=True,timeout=240)
if r.returncode!=0 or r.stderr or r.stdout!=(P/'observations/fake.stdout').read_bytes():raise ValueError(('fake rerun mismatch',r.returncode,r.stderr))
print(json.dumps({'status':'PASS_NO_LEAN_INDEPENDENT_GRAPH_BAND_DRIVER_REVIEW','driver_sha256':want,'provider':str(d.PREFIX),'fixed_pin_count':len(d.PINS),'source_rows':rows,'reports':35,'parent_objects_per_side':150,'slot_counts':{k:len(scan[k]) for k in ('external_direct_slots','target_slots','package_slots')},'warning_inventory':expected_warnings,'fake_controls_sha256':H(P/'fake-controls.py'),'fake_log_sha256':hashlib.sha256(r.stdout).hexdigest(),'fake_exit':r.returncode,'lean_launched':False,'scope':'Point-in-time source/provider/slot inventory and fake controls only; no Lean, parent audit rerun, preflight or pair.'},indent=2,sort_keys=True))
