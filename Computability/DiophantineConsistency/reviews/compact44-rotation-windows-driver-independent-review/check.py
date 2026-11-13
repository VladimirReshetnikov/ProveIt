#!/usr/bin/env python3
"""No-Lean rotation driver/source/provider/report verification."""
import hashlib,importlib.util,json,os,pathlib,re,subprocess,sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated nonoptimized Python required')
P=pathlib.Path;root=P.cwd();base=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';p=base/'compact44-rotation-windows-pair-prototype';H=lambda x:hashlib.sha256(P(x).read_bytes()).hexdigest();want='b65108dad183079f7d51d8191d2742dd1376a33fd07d0d09717b6620ccd3c8cc'
if H(p/'replay.py')!=want:raise ValueError('driver drift')
spec=importlib.util.spec_from_file_location('driver',p/'replay.py');d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d);d.validate_provider()
for f,h in d.PINS.items():
 if not f.is_file() or H(f)!=h:raise ValueError(('fixed pin',str(f)))
scan=json.loads((d.PLAN/'scan.json').read_bytes());parent=json.loads((d.PARENT_AUDIT/'CHECK.json').read_bytes());closure=json.loads((d.CLOSURE_AUDIT/'CHECK.json').read_bytes());rows=[]
if scan['status']!='PRELIMINARY_ROTATION_WINDOWS_SOURCE_CLOSURE_NOT_A_BUILD' or parent['status']!='PASS_INDEPENDENT_INDEXED_GRAPH_CARRY_PAIRED_ARTIFACT_AUDIT' or closure['status']!='PASS_INDEPENDENT_ROTATION_WINDOWS_SOURCE_CLOSURE' or d.AXIOMS!={'propext','Classical.choice','Quot.sound'}:raise ValueError('audit or axiom policy')
dirs=['compact44-fractional-digits-prototype','compact44-rotation-adjacent-prototype','compact44-wrapped-rotation-prototype','compact44-straddling-rotation-prototype','compact44-rotation-coverage-prototype','compact44-rotation-index-bounds-prototype'];logs=[f for dirname in dirs for f in sorted((base/dirname/'observations').glob('*.log'))]
for r in scan['source_order']:
 f=P(r['source']);s=f.read_text();imports=[x[7:] for x in s.splitlines() if x.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',s,re.M)
 if H(f)!=r['source_sha256'] or imports!=r['imports'] or reports!=r['axiom_reports']:raise ValueError(('source drift',r['module']))
 matches=[]
 for log in logs:
  text=log.read_text()
  if re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text):continue
  found=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",text,re.M)
  if len(found)==len(reports) and {n for n,_ in found}==set(reports) and all({x.strip() for x in ax.split(',') if x.strip()}=={'propext','Classical.choice','Quot.sound'} for _,ax in found):matches.append(log)
 if not matches:raise ValueError(('missing retained author report',r['module']))
 d.validate_reports(r['module'],matches[0].read_text(),reports)
 rows.append({'module':r['module'],'sha256':r['source_sha256'],'imports':imports,'reports':reports,'retained_log_sha256':H(matches[0]),'retained_log':str(matches[0])})
if len(rows)!=14 or [x['module'] for x in rows]!=d.MODULES or sum(len(x['reports']) for x in rows)!=24:raise ValueError('source/report inventory')
if [{k:x[k] for k in ('module','sha256','imports','reports')} for x in rows]!=closure['source_rows']:raise ValueError('closure row mismatch')
if not P('/tmp/compact44-aligned-family-plan/lib').is_dir():raise ValueError('missing inherited old-provider audit dependency')
for side in ('author','peer'):
 lib=d.PREFIX/side/'lib';live={x.relative_to(lib).as_posix():x for x in lib.rglob('*.olean') if x.is_file()};rec={x['path']:x for x in scan['parent_objects'][side]}
 if len(live)!=189 or set(live)!=set(rec):raise ValueError(('provider count',side))
 for n,f in live.items():
  x=rec[n]
  if str(f.resolve())!=x['realpath'] or H(f)!=x['sha256']:raise ValueError(('provider drift',side,n))
for key,num in [('external_direct_slots',40),('target_slots',280),('package_slots',10)]:
 if len(scan[key])!=num:raise ValueError(('slot count',key))
 for name,item in scan[key].items():
  f=P(name)
  if item is None:
   if os.path.lexists(f):raise ValueError(('unexpected slot',name))
  elif not f.is_file() or str(f.resolve())!=item['realpath'] or H(f)!=item['sha256']:raise ValueError(('slot drift',name))
if any(x is not None for x in scan['target_slots'].values()) or len(d.SUFFIXES)!=10 or len(set(d.SUFFIXES))!=10:raise ValueError('targets or suffixes')
fake=json.loads((p/'observations/fake-observation.json').read_bytes())
if fake['driver_sha256']!=want or fake['fake_controls_sha256']!=H(p/'fake-controls.py') or fake['fake_exit']!=0 or fake['fake_modes']!=42 or fake['fake_aggregate_groups']!=2 or fake['lean_launched'] is not False or fake['real_report_controls_exit']!=0:raise ValueError('fake observation')
outputs={}
for script,log in [('fake-controls.py','fake.stdout'),('real-report-controls.py','real-reports.stdout')]:
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/script)],cwd=root,capture_output=True,timeout=240)
 if r.returncode!=0 or r.stderr or r.stdout!=(p/'observations'/log).read_bytes():raise ValueError(('control rerun mismatch',script,r.returncode,r.stderr))
 outputs[script]={'sha256':H(p/script),'log_sha256':hashlib.sha256(r.stdout).hexdigest(),'exit':r.returncode}
print(json.dumps({'status':'PASS_NO_LEAN_INDEPENDENT_ROTATION_WINDOWS_DRIVER_REVIEW','driver_sha256':want,'reviewed_commit':'1b0b4cc5d8','provider':str(d.PREFIX),'inherited_old_read_only_audit_dependency':'/tmp/compact44-aligned-family-plan/lib','fixed_pin_count':len(d.PINS),'source_modules':len(rows),'named_reports':24,'source_rows':rows,'parent_objects_per_side':189,'slot_counts':{k:len(scan[k]) for k in ('external_direct_slots','target_slots','package_slots')},'controls':outputs,'lean_launched':False,'scope':'Source/artifact driver verification only, not independent mathematical proof review or a real preflight; next digit is zero padding at q+1=n.'},indent=2,sort_keys=True))
