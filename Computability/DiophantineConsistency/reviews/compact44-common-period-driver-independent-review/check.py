#!/usr/bin/env python3
"""Read-only independent byte/guard inventory and fake controls; never launches Lean."""
import hashlib, importlib.util, json, os, pathlib, re, subprocess, sys
P=pathlib.Path.cwd()/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-common-period-pair-prototype'
H=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
if not sys.flags.isolated or not sys.flags.no_site or not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise ValueError('isolated nonoptimized Python required')
D=P/'replay.py';want='b6937baa668c261b9487a98f54297789beae09411332a183877672486780a943'
if H(D)!=want:raise ValueError('driver mismatch')
spec=importlib.util.spec_from_file_location('driver',D);d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d);d.validate_provider()
for p,h in d.PINS.items():
 if not p.is_file() or H(p)!=h:raise ValueError(('fixed pin mismatch',str(p)))
scan=json.loads((d.PLAN/'scan.json').read_bytes());rows=[]
for row in scan['source_order']:
 p=pathlib.Path(row['source']);t=p.read_text();imports=[x[7:] for x in t.splitlines() if x.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',t,re.M)
 if H(p)!=row['source_sha256'] or imports!=row['imports'] or reports!=d.REPORTS[row['module']]:raise ValueError(('source, import, or report mismatch',str(p)))
 rows.append({'module':row['module'],'sha256':row['source_sha256'],'imports':imports,'reports':reports})
if [x['module'] for x in rows]!=d.MODULES:raise ValueError('source order')
if len(d.SUFFIXES)!=10 or len(set(d.SUFFIXES))!=10:raise ValueError('companion slots')
for side in ('author','peer'):
 if len(scan['objects'][side])!=150:raise ValueError(('object count',side))
 for obj in scan['objects'][side]:
  p=d.PREFIX/side/'lib'/obj['path']
  if not p.is_file() or str(p.resolve())!=obj['resolved'] or H(p)!=obj['sha256']:raise ValueError(('provider object drift',str(p)))
for key in ('external_direct_slots','target_slots','init_slots'):
 for name,v in scan[key].items():
  p=pathlib.Path(name)
  if v is None:
   if os.path.lexists(p):raise ValueError(('unexpected slot',name))
  elif not p.is_file() or str(p.resolve())!=v['resolved'] or H(p)!=v['sha256']:raise ValueError(('slot drift',name))
for name in d.MODULES:
 text=''.join("'"+n+"' depends on axioms: ["+('propext, Quot.sound' if n=='CompactPeriodCopy.position_pos' else 'propext, Classical.choice, Quot.sound')+"]\n" for n in d.REPORTS[name]);d.validate_reports(name,text)
pre=json.loads((P/'preflight-final-observation.json').read_bytes());out=json.loads((P/'preflight-final.json').read_bytes());control=json.loads((P/'control-observation.json').read_bytes())
if pre['driver_sha256']!=want or pre['preflight_sha256']!=H(P/'preflight-final.json') or pre['observed_exit']!=0 or pre['lean_launched'] is not False or pre['output_directory_created'] is not False or out['expected_head']!=pre['expected_head'] or out['driver_sha256']!=want or out['lean_launched'] is not False:raise ValueError('preflight observation')
if control['corrected_driver_sha256']!=want or control['corrected_fake_log_sha256']!=H(P/'fake-controls.log') or control['corrected_fake_exit']!=0 or control['lean_launched'] is not False:raise ValueError('fake observation')
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'fake-controls.py')],capture_output=True,timeout=180)
if r.returncode!=0 or r.stderr or r.stdout!=(P/'fake-controls.log').read_bytes():raise ValueError(('fake rerun',r.returncode,r.stderr))
print(json.dumps({'status':'PASS_NO_LEAN_INDEPENDENT_COMMON_PERIOD_DRIVER_REVIEW','driver_sha256':want,'provider':str(d.PREFIX),'fixed_pin_count':len(d.PINS),'objects_per_side':150,'slot_counts':{k:len(scan[k]) for k in ('external_direct_slots','target_slots','init_slots')},'source_rows':rows,'suffixes':list(d.SUFFIXES),'special_axioms':{'CompactPeriodCopy.position_pos':['propext','Quot.sound'],'other_named_reports':['propext','Classical.choice','Quot.sound']},'fake_controls_exit':r.returncode,'fake_controls_sha256':H(P/'fake-controls.py'),'fake_log_sha256':hashlib.sha256(r.stdout).hexdigest(),'recorded_preflight_head':pre['expected_head'],'recorded_preflight_sha256':pre['preflight_sha256'],'lean_launched':False,'scope':'Source and slot inventory plus fake controls; no Lean, independent parent audit rerun or paired artifact.'},indent=2,sort_keys=True))
