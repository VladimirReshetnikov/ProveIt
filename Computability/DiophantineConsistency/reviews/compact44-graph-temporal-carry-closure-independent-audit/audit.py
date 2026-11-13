#!/usr/bin/env python3
"""Independent no-Lean source/companion inventory; not a math-proof review."""
import hashlib,json,os,pathlib,re,subprocess,sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated nonoptimized Python required')
P=pathlib.Path;root=P.cwd();base=root/'Computability/DiophantineConsistency';plan=base/'research/ordinary12-ipra-bridge/compact44-graph-temporal-carry-closure-plan';parent=base/'reviews/compact44-graph-band-pair-independent-audit';provider=P('/tmp/ipra-graph-band-pair-01');H=lambda p:hashlib.sha256(P(p).read_bytes()).hexdigest();scan_sha='de4d762b2491cc64865a80ef5cb6e237526c689370d749900b4e5cc17906fdf5';source_sha='873836abef535b7eae2ff46c4847f2a553dd10e801adadd08761b8a855379ce9';audit_sha='1c05df2a0b710697256688e380503cc2503e135833d54c9c3b986ef8f644a21e';parent_sha='61837a3a0d01b32f7c7a929fef3945f6fef3f1724c4b9a83c4ce721fd7a7572a'
def git_hash(rev,p):return hashlib.sha256(subprocess.run(['git','show',rev+':'+p.relative_to(root).as_posix()],cwd=root,capture_output=True,check=True,timeout=60).stdout).hexdigest()
if H(plan/'scan.json')!=scan_sha or git_hash('42ccbf261d',plan/'scan.json')!=scan_sha or H(plan/'scan.py')!=source_sha or git_hash('42ccbf261d',plan/'scan.py')!=source_sha:raise ValueError('plan drift')
if H(parent/'audit.py')!=audit_sha or H(parent/'CHECK.json')!=parent_sha:raise ValueError('parent audit drift')
scan=json.loads((plan/'scan.json').read_bytes());obs=json.loads((plan/'terminal-observation.json').read_bytes());pa=json.loads((parent/'CHECK.json').read_bytes());pto=json.loads((parent/'terminal-observation.json').read_bytes())
if scan['status']!='PRELIMINARY_GRAPH_TEMPORAL_CARRY_SOURCE_CLOSURE_NOT_A_BUILD' or scan['parent_audit_sha256']!=parent_sha or scan['parent_receipt_sha256']!='b957b92e181a90f5dd0d1b5aa2adabb12eb7ed8eac463e47c19356e2ca5182a7':raise ValueError('scan receipt')
if obs['observed_exit']!=0 or obs['optimized_exit']!=1 or obs['lean_launched'] is not False or obs['parent_audit_rerun'] is not False or obs['scan_sha256']!=scan_sha or pto['check_sha256']!=parent_sha or pto['observed_exit']!=0 or pa['status']!='PASS_INDEPENDENT_GRAPH_BAND_PAIRED_ARTIFACT_AUDIT':raise ValueError('observation')
names=['BandCarryInputs','CompactBitRotation','ActualTemporalBand','FixedGraphTemporal','CompactDigitBound','CompactHeterogeneousCarry','GenericBandCarryFamily'];expected_imports=[['DiophantineConsistency.ArithmeticCyclicWord'],['DiophantineConsistency.ArithmeticCyclicWord'],['DiophantineConsistency.CompactBitRotation','DiophantineConsistency.BandCarryInputs'],['DiophantineConsistency.SymbolicGraphBand','DiophantineConsistency.ActualTemporalBand'],['DiophantineConsistency.ArithmeticWindowCarry'],['DiophantineConsistency.ArithmeticWindowCarry','DiophantineConsistency.CompactDigitBound'],['DiophantineConsistency.BandCarryInputs','DiophantineConsistency.CompactHeterogeneousCarry','Mathlib.Data.Fintype.BigOperators']];report_counts=[4,5,1,1,6,4,1];rows=scan['source_order'];allnames={'DiophantineConsistency.'+x for x in names};available=set();external=set();summaries=[]
if len(rows)!=7 or [r['module'] for r in rows]!=['DiophantineConsistency.'+x for x in names]:raise ValueError('source order')
for row,imports_expected,rc in zip(rows,expected_imports,report_counts):
 p=P(row['source']);s=p.read_text();imports=[l[7:] for l in s.splitlines() if l.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',s,re.M)
 if H(p)!=row['source_sha256'] or git_hash(row['source_commit'],p)!=row['source_sha256'] or imports!=imports_expected or imports!=row['imports'] or reports!=row['axiom_reports'] or len(reports)!=rc:raise ValueError(('source/import/report drift',row['module']))
 for dep in imports:
  if dep not in available:
   if dep in allnames:raise ValueError(('forward import',dep))
   external.add(dep)
 available.add(row['module']);summaries.append({'module':row['module'],'sha256':row['source_sha256'],'imports':imports,'reports':reports})
if external!={'DiophantineConsistency.ArithmeticCyclicWord','DiophantineConsistency.ArithmeticWindowCarry','DiophantineConsistency.SymbolicGraphBand','Mathlib.Data.Fintype.BigOperators'}:raise ValueError(('unexpected external',external))
prev=None
for side in ('author','peer'):
 lib=provider/side/'lib';live={x.relative_to(lib).as_posix():x for x in lib.rglob('*.olean') if x.is_file()};entries=scan['parent_objects'][side];rec={x['path']:x for x in entries}
 if len(live)!=171 or set(live)!=set(rec):raise ValueError(('parent object inventory',side))
 pairs=[]
 for name,p in sorted(live.items()):
  item=rec[name];digest=H(p)
  if str(p.resolve())!=item['realpath'] or digest!=item['sha256']:raise ValueError(('parent drift',side,name))
  pairs.append((name,digest))
 if prev is not None and pairs!=prev:raise ValueError('same-side hash discrepancy')
 prev=pairs
for k,count in [('external_direct_slots',60),('target_slots',140),('package_slots',20)]:
 if len(scan[k])!=count:raise ValueError(('slot count',k))
 for name,item in scan[k].items():
  p=P(name)
  if item is None:
   if os.path.lexists(p):raise ValueError(('unexpected companion',name))
  elif not p.is_file() or str(p.resolve())!=item['realpath'] or H(p)!=item['sha256']:raise ValueError(('companion drift',name))
if any(x is not None for x in scan['target_slots'].values()):raise ValueError('target occupied')
r=subprocess.run([sys.executable,'-I','-S','-B',str(parent/'audit.py')],cwd=root,capture_output=True,timeout=1800)
if r.returncode!=0 or r.stderr or json.loads(r.stdout)!=pa:raise ValueError(('parent audit rerun',r.returncode,r.stderr))
print(json.dumps({'status':'PASS_INDEPENDENT_GRAPH_TEMPORAL_CARRY_SOURCE_CLOSURE','reviewed_commit':'42ccbf261d','scan_sha256':scan_sha,'parent_audit_sha256':parent_sha,'parent_receipt_sha256':scan['parent_receipt_sha256'],'source_modules':7,'named_reports':sum(report_counts),'parent_objects_per_side':171,'external_direct_slots':60,'target_slots':140,'package_slots':20,'parent_audit_rerun_exit':r.returncode,'lean_launched':False,'source_rows':summaries,'review_scope':'Source/artifact closure verification by an author of several clients, not independent mathematical proof review; no paired build or concrete CarryInput instantiation.'},indent=2,sort_keys=True))
