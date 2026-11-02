#!/usr/bin/env python3
"""No-Lean fixed-clean driver/source/provider/report verification."""
import hashlib,importlib.util,json,os,pathlib,re,subprocess,sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated nonoptimized Python required')
P=pathlib.Path;root=P.cwd();base=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';p=base/'compact44-fixed-clean-carry-pair-prototype';H=lambda x:hashlib.sha256(P(x).read_bytes()).hexdigest();want='b636767b6c9ca4d847d62fbf0d674abb03f07969ac1ca50bf41148cbad637bb6'
if H(p/'replay.py')!=want:raise ValueError('driver drift')
spec=importlib.util.spec_from_file_location('driver',p/'replay.py');d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d);d.validate_provider()
for f,h in d.PINS.items():
 if not f.is_file() or H(f)!=h:raise ValueError(('fixed pin',str(f)))
scan=json.loads((d.PLAN/'scan.json').read_bytes());parent=json.loads((d.PARENT_AUDIT/'CHECK.json').read_bytes());closure=json.loads((d.CLOSURE_AUDIT/'CHECK.json').read_bytes());survey=json.loads((p/'report-survey.json').read_bytes());rows=[]
if scan['status']!='PRELIMINARY_FIXED_CLEAN_CARRY_SOURCE_CLOSURE_NOT_A_BUILD' or parent['status']!='PASS_INDEPENDENT_ROTATION_WINDOWS_PAIRED_ARTIFACT_AUDIT' or closure['status']!='PASS_INDEPENDENT_FIXED_CLEAN_CARRY_SOURCE_CLOSURE':raise ValueError('audit status')
small={'CleanGeometry.finite_disjoint','CleanTargetPhase.finite_relation'}
if d.SMALL_AXIOMS!=small or d.AXIOMS!={'propext','Classical.choice','Quot.sound'} or set(survey['small_axioms'])!=small or survey['source_modules']!=33 or survey['reports']!=54 or survey['source_scan_sha256']!=H(d.PLAN/'scan.json') or len(survey['rows'])!=33:raise ValueError('axiom policy or survey')
for r,seen in zip(scan['source_order'],survey['rows']):
 f=P(r['source']);s=f.read_text();imports=[x[7:] for x in s.splitlines() if x.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',s,re.M)
 if H(f)!=r['source_sha256'] or imports!=r['imports'] or reports!=r['axiom_reports'] or seen['module']!=r['module'] or seen['source_sha256']!=r['source_sha256']:raise ValueError(('source drift',r['module']))
 log=P(seen['retained_log']);live=P(seen['author_overlay_log']);text=log.read_text()
 if H(log)!=seen['log_sha256'] or not live.is_file() or H(live)!=seen['log_sha256'] or re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text):raise ValueError(('retained/live log drift',str(log)))
 got=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",text,re.M)
 if len(got)!=len(reports) or {n for n,_ in got}!=set(reports):raise ValueError(('retained report names',str(log)))
 for name,ax in got:
  expected={'propext','Quot.sound'} if name in small else {'propext','Classical.choice','Quot.sound'}
  if {x.strip() for x in ax.split(',') if x.strip()}!=expected:raise ValueError(('actual report mismatch',name,ax))
 d.validate_reports(r['module'],text,reports)
 rows.append({'module':r['module'],'sha256':r['source_sha256'],'imports':imports,'reports':reports,'retained_log_sha256':H(log),'retained_log':str(log)})
if len(rows)!=33 or [x['module'] for x in rows]!=d.MODULES or sum(len(x['reports']) for x in rows)!=54:raise ValueError('source/report inventory')
if [{k:x[k] for k in ('module','sha256','imports','reports')} for x in rows]!=closure['source_rows']:raise ValueError('closure row mismatch')
old=P('/tmp/ipra-compact-clean-carry-pair-01');old2=P('/tmp/compact44-aligned-family-plan/lib')
if not old.is_dir() or not old2.is_dir():raise ValueError('missing historical read-only audit dependency')
for side in ('author','peer'):
 lib=d.PREFIX/side/'lib';live={x.relative_to(lib).as_posix():x for x in lib.rglob('*.olean') if x.is_file()};rec={x['path']:x for x in scan['parent_objects'][side]}
 if len(live)!=203 or set(live)!=set(rec):raise ValueError(('provider count',side))
 for n,f in live.items():
  x=rec[n]
  if str(f.resolve())!=x['realpath'] or H(f)!=x['sha256']:raise ValueError(('provider drift',side,n))
 ol=old/side/'lib';oldfiles={x.relative_to(ol).as_posix():x for x in ol.rglob('*.olean') if x.is_file()};common=live.keys()&oldfiles.keys();diff=[{'path':n,'rotation_sha256':H(live[n]),'older_clean_carry_sha256':H(oldfiles[n])} for n in sorted(common) if H(live[n])!=H(oldfiles[n])]
 if len(oldfiles)!=117 or len(common)!=92 or len(diff)!=4 or diff!=closure['provider_differences'][side]:raise ValueError(('old audit comparison',side))
for key,num in [('external_direct_slots',420),('target_slots',660),('package_slots',10)]:
 if len(scan[key])!=num:raise ValueError(('slot count',key))
 for name,item in scan[key].items():
  f=P(name)
  if item is None:
   if os.path.lexists(f):raise ValueError(('unexpected slot',name))
  elif not f.is_file() or str(f.resolve())!=item['realpath'] or H(f)!=item['sha256']:raise ValueError(('slot drift',name))
if any(x is not None for x in scan['target_slots'].values()) or len(d.SUFFIXES)!=10 or len(set(d.SUFFIXES))!=10:raise ValueError('targets or suffixes')
fake=json.loads((p/'observations/fake-observation.json').read_bytes())
if fake['driver_sha256']!=want or fake['fake_controls_sha256']!=H(p/'fake-controls.py') or fake['fake_exit']!=0 or fake['fake_modes']!=44 or fake['fake_aggregate_groups']!=2 or fake['lean_launched'] is not False or fake['real_report_controls_exit']!=0 or fake['receipt_schema_controls_exit']!=0 or fake['receipt_schema_modes']!=30:raise ValueError('fake observation')
outputs={}
for script,log in [('fake-controls.py','fake.stdout'),('real-report-controls.py','real-reports.stdout'),('schema-controls.py','schema.stdout')]:
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/script)],cwd=root,capture_output=True,timeout=400)
 if r.returncode!=0 or r.stderr or r.stdout!=(p/'observations'/log).read_bytes():raise ValueError(('control rerun mismatch',script,r.returncode,r.stderr))
 outputs[script]={'sha256':H(p/script),'log_sha256':hashlib.sha256(r.stdout).hexdigest(),'exit':r.returncode}
print(json.dumps({'status':'PASS_NO_LEAN_INDEPENDENT_FIXED_CLEAN_CARRY_DRIVER_REVIEW','driver_sha256':want,'reviewed_commit':'6ab762ceb4','provider':str(d.PREFIX),'historical_read_only_audit_dependencies':[str(old),str(old2)],'fixed_pin_count':len(d.PINS),'source_modules':len(rows),'named_reports':54,'small_axioms':sorted(small),'source_rows':rows,'parent_objects_per_side':203,'old_overlap_per_side':92,'old_differing_per_side':4,'slot_counts':{k:len(scan[k]) for k in ('external_direct_slots','target_slots','package_slots')},'controls':outputs,'lean_launched':False,'scope':'Driver/source/artifact verification only, not independent mathematical proof review; no real preflight or paired build.'},indent=2,sort_keys=True))
