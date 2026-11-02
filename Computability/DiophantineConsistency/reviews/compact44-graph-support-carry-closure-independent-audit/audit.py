#!/usr/bin/env python3
"""No-Lean support/carry source/provider closure inventory and parent rerun."""
import hashlib,json,os,pathlib,re,subprocess,sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated nonoptimized Python required')
P=pathlib.Path;root=P.cwd();base=root/'Computability/DiophantineConsistency';plan=base/'research/ordinary12-ipra-bridge/compact44-graph-support-carry-closure-plan';parent=base/'reviews/compact44-rotation-windows-pair-independent-audit';provider=P('/tmp/ipra-rotation-windows-pair-01');H=lambda p:hashlib.sha256(P(p).read_bytes()).hexdigest();scan_sha='b21aa8317cb0a3ec7f2198e80a94e3fd53cb83e9aa5f5cfc26fdfa7ef440252e';source_sha='6d7ece310a8cd8504227bd4b6b8edd5560a4a54531f9ee58c80dd2be71bb3967';parent_script_sha='e8121e39678fcc42114500c92c1b294f2b26fc422569f2b7b70ac3341d09c387';parent_sha='7adb39a15c385f542ff5b8c34db7237a7edff25822d4e49aebdd104689745df0'
def gh(rev,p):return hashlib.sha256(subprocess.run(['git','show',rev+':'+p.relative_to(root).as_posix()],cwd=root,capture_output=True,check=True,timeout=60).stdout).hexdigest()
for p,h in [(plan/'scan.json',scan_sha),(plan/'scan.py',source_sha)]:
 if H(p)!=h or gh('cac5a422fc',p)!=h:raise ValueError(('plan drift',str(p)))
if H(parent/'audit.py')!=parent_script_sha or H(parent/'CHECK.json')!=parent_sha:raise ValueError('parent audit drift')
scan=json.loads((plan/'scan.json').read_bytes());obs=json.loads((plan/'terminal-observation.json').read_bytes());pa=json.loads((parent/'CHECK.json').read_bytes());pto=json.loads((parent/'terminal-observation.json').read_bytes())
if scan['status']!='PRELIMINARY_FIXED_GRAPH_SUPPORT_CARRY_SOURCE_CLOSURE_NOT_A_BUILD' or scan['parent_audit_sha256']!=parent_sha or scan['parent_receipt_sha256']!='87bd0f6934145714f41f18e339f66b325bcb90f3da8fc44402ce3ff21b3d1e4d':raise ValueError('scan receipt')
if type(obs['observed_exit']) is not int or obs['observed_exit']!=0 or obs['optimized_exit']!=1 or obs['lean_launched'] is not False or obs['parent_audit_rerun'] is not False or obs['scan_sha256']!=scan_sha or pto['check_sha256']!=parent_sha or type(pto['observed_exit']) is not int or pto['observed_exit']!=0 or pa['status']!='PASS_INDEPENDENT_ROTATION_WINDOWS_PAIRED_ARTIFACT_AUDIT':raise ValueError('observation')
names=['CompactSymbolicGraphSaturation','CompactSameWitnessSaturation2','CompactPositionIncrement','CompactPositionGraph','CleanGeometry','CleanMaskClasses','CleanModelSupport','FixedGraphSupportCarry'];counts=[1,2,1,2,4,3,2,1];rows=scan['source_order'];allnames={'DiophantineConsistency.'+x for x in names};available=set();external=set();summaries=[]
if len(rows)!=8 or [r['module'] for r in rows]!=['DiophantineConsistency.'+x for x in names]:raise ValueError('source order')
for row,rc in zip(rows,counts):
 p=P(row['source']);s=p.read_text();imports=[l[7:] for l in s.splitlines() if l.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',s,re.M)
 if H(p)!=row['source_sha256'] or gh(row['source_commit'],p)!=row['source_sha256'] or imports!=row['imports'] or reports!=row['axiom_reports'] or len(reports)!=rc:raise ValueError(('source/import/report drift',row['module']))
 for dep in imports:
  if dep not in available:
   if dep in allnames:raise ValueError(('forward import',dep))
   external.add(dep)
 available.add(row['module']);summaries.append({'module':row['module'],'sha256':row['source_sha256'],'imports':imports,'reports':reports})
if external!={'DiophantineConsistency.FreeJConcreteDigitsClient','DiophantineConsistency.CompactLowExact','DiophantineConsistency.CompactLowEven','DiophantineConsistency.CompactHighResidue','DiophantineConsistency.FreeJGraphCongruenceExplore','DiophantineConsistency.CompactMixedIncrement','DiophantineConsistency.ArithmeticStandardCasts','DiophantineConsistency.CompactSymbolicPorts','DiophantineConsistency.CompactConcreteMask','DiophantineConsistency.CompactDummyBound','DiophantineConsistency.FixedGraphIndexedCarry'}:raise ValueError(('external imports',external))
prev=None
for side in ('author','peer'):
 lib=provider/side/'lib';live={x.relative_to(lib).as_posix():x for x in lib.rglob('*.olean') if x.is_file()};entries=scan['parent_objects'][side];rec={x['path']:x for x in entries}
 if len(live)!=203 or set(live)!=set(rec):raise ValueError(('parent inventory',side))
 pairs=[]
 for name,p in sorted(live.items()):
  item=rec[name];digest=H(p)
  if str(p.resolve())!=item['realpath'] or digest!=item['sha256']:raise ValueError(('parent drift',side,name))
  pairs.append((name,digest))
 if prev is not None and pairs!=prev:raise ValueError('same-side hash discrepancy')
 prev=pairs
for k,count in [('external_direct_slots',220),('target_slots',160),('package_slots',10)]:
 if len(scan[k])!=count:raise ValueError(('slot count',k))
 for name,item in scan[k].items():
  p=P(name)
  if item is None:
   if os.path.lexists(p):raise ValueError(('unexpected companion',name))
  elif not p.is_file() or str(p.resolve())!=item['realpath'] or H(p)!=item['sha256']:raise ValueError(('companion drift',name))
if any(x is not None for x in scan['target_slots'].values()):raise ValueError('target occupied')
r=subprocess.run([sys.executable,'-I','-S','-B',str(parent/'audit.py')],cwd=root,capture_output=True,timeout=2400)
if r.returncode!=0 or r.stderr or json.loads(r.stdout)!=pa:raise ValueError(('parent audit rerun',r.returncode,r.stderr))
print(json.dumps({'status':'PASS_INDEPENDENT_FIXED_GRAPH_SUPPORT_CARRY_SOURCE_CLOSURE','reviewed_commit':'cac5a422fc','scan_sha256':scan_sha,'parent_audit_sha256':parent_sha,'parent_receipt_sha256':scan['parent_receipt_sha256'],'source_modules':8,'named_reports':sum(counts),'parent_objects_per_side':203,'external_direct_slots':220,'target_slots':160,'package_slots':10,'parent_audit_rerun_exit':r.returncode,'lean_launched':False,'source_rows':summaries,'review_scope':'Source/artifact closure verification only, not a paired build or independent mathematical review; same N obtained by equality, original carry w retained; no selected clean predecessor, temporal half-radix bound or retained-byte binding.'},indent=2,sort_keys=True))
