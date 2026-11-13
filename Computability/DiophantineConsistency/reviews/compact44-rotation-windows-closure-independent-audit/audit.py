#!/usr/bin/env python3
"""No-Lean rotation-window source/provider closure inventory and parent rerun."""
import hashlib,json,os,pathlib,re,subprocess,sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated nonoptimized Python required')
P=pathlib.Path;root=P.cwd();base=root/'Computability/DiophantineConsistency';plan=base/'research/ordinary12-ipra-bridge/compact44-rotation-windows-closure-plan';parent=base/'reviews/compact44-indexed-graph-carry-pair-independent-audit';provider=P('/tmp/ipra-indexed-graph-carry-pair-01');H=lambda p:hashlib.sha256(P(p).read_bytes()).hexdigest();scan_sha='701d75f92188f0f1f01cb0ebea7d6ba1f5398d2a8a3dc9c84aeeb00d7bbd09d4';source_sha='1f2f2ac76c6c75d56a3dd717f76cf3a0ee40a69758f1f450aadf62f5177b31db';parent_script_sha='23cb2ed1ef583677e129d7b5a9401d29b0b3abc53f4d0bf25b131bb779437118';parent_sha='fc611469130bf441fb3389e7f17edd7b9dd8bae37e7b63cee88e293bc282ce27'
def gh(rev,p):return hashlib.sha256(subprocess.run(['git','show',rev+':'+p.relative_to(root).as_posix()],cwd=root,capture_output=True,check=True,timeout=60).stdout).hexdigest()
for p,h in [(plan/'scan.json',scan_sha),(plan/'scan.py',source_sha)]:
 if H(p)!=h or gh('37ffc248cc',p)!=h:raise ValueError(('plan drift',str(p)))
if H(parent/'audit.py')!=parent_script_sha or H(parent/'CHECK.json')!=parent_sha:raise ValueError('parent audit drift')
scan=json.loads((plan/'scan.json').read_bytes());obs=json.loads((plan/'terminal-observation.json').read_bytes());pa=json.loads((parent/'CHECK.json').read_bytes());pto=json.loads((parent/'terminal-observation.json').read_bytes())
if scan['status']!='PRELIMINARY_ROTATION_WINDOWS_SOURCE_CLOSURE_NOT_A_BUILD' or scan['parent_audit_sha256']!=parent_sha or scan['parent_receipt_sha256']!='ac61d16759d0af5a28304226dd397e151af4a1d5f1e49ba3dcc204c0945ba13f':raise ValueError('scan receipt')
if type(obs['observed_exit']) is not int or obs['observed_exit']!=0 or obs['optimized_exit']!=1 or obs['lean_launched'] is not False or obs['parent_audit_rerun'] is not False or obs['scan_sha256']!=scan_sha or pto['check_sha256']!=parent_sha or type(pto['observed_exit']) is not int or pto['observed_exit']!=0 or pa['status']!='PASS_INDEPENDENT_INDEXED_GRAPH_CARRY_PAIRED_ARTIFACT_AUDIT':raise ValueError('observation')
names=['FractionalDigits','AdjacentDigits','RotationWindow','RotationAdjacent','RotationWrapped','WrappedAdjacent','RotationStraddling','StraddlingAdjacent','RotationCoverage','RotationCoverage67','RotationAllCases','RotationIndexBounds','RotationCoverageBounded','RotationBoundedCases'];counts=[1,2,1,1,1,1,2,1,2,1,1,6,2,2];rows=scan['source_order'];allnames={'DiophantineConsistency.'+x for x in names};available=set();external=set();summaries=[]
if len(rows)!=14 or [r['module'] for r in rows]!=['DiophantineConsistency.'+x for x in names]:raise ValueError('source order')
for row,rc in zip(rows,counts):
 p=P(row['source']);s=p.read_text();imports=[l[7:] for l in s.splitlines() if l.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',s,re.M)
 if H(p)!=row['source_sha256'] or gh(row['source_commit'],p)!=row['source_sha256'] or imports!=row['imports'] or reports!=row['axiom_reports'] or len(reports)!=rc:raise ValueError(('source/import/report drift',row['module']))
 for dep in imports:
  if dep not in available:
   if dep in allnames:raise ValueError(('forward import',dep))
   external.add(dep)
 available.add(row['module']);summaries.append({'module':row['module'],'sha256':row['source_sha256'],'imports':imports,'reports':reports})
if external!={'DiophantineConsistency.ArithmeticWindowDigits','DiophantineConsistency.ArithmeticCyclicWord'}:raise ValueError(('external imports',external))
prev=None
for side in ('author','peer'):
 lib=provider/side/'lib';live={x.relative_to(lib).as_posix():x for x in lib.rglob('*.olean') if x.is_file()};entries=scan['parent_objects'][side];rec={x['path']:x for x in entries}
 if len(live)!=189 or set(live)!=set(rec):raise ValueError(('parent inventory',side))
 pairs=[]
 for name,p in sorted(live.items()):
  item=rec[name];digest=H(p)
  if str(p.resolve())!=item['realpath'] or digest!=item['sha256']:raise ValueError(('parent drift',side,name))
  pairs.append((name,digest))
 if prev is not None and pairs!=prev:raise ValueError('same-side hash discrepancy')
 prev=pairs
for k,count in [('external_direct_slots',40),('target_slots',280),('package_slots',10)]:
 if len(scan[k])!=count:raise ValueError(('slot count',k))
 for name,item in scan[k].items():
  p=P(name)
  if item is None:
   if os.path.lexists(p):raise ValueError(('unexpected companion',name))
  elif not p.is_file() or str(p.resolve())!=item['realpath'] or H(p)!=item['sha256']:raise ValueError(('companion drift',name))
if any(x is not None for x in scan['target_slots'].values()):raise ValueError('target occupied')
r=subprocess.run([sys.executable,'-I','-S','-B',str(parent/'audit.py')],cwd=root,capture_output=True,timeout=2400)
if r.returncode!=0 or r.stderr or json.loads(r.stdout)!=pa:raise ValueError(('parent audit rerun',r.returncode,r.stderr))
print(json.dumps({'status':'PASS_INDEPENDENT_ROTATION_WINDOWS_SOURCE_CLOSURE','reviewed_commit':'37ffc248cc','scan_sha256':scan_sha,'parent_audit_sha256':parent_sha,'parent_receipt_sha256':scan['parent_receipt_sha256'],'source_modules':14,'named_reports':sum(counts),'parent_objects_per_side':189,'external_direct_slots':40,'target_slots':280,'package_slots':10,'parent_audit_rerun_exit':r.returncode,'lean_launched':False,'source_rows':summaries,'review_scope':'Source/artifact closure verification only, not a paired build or independent mathematical review; next digit is zero padding at q+1=n, not a cyclic identification.'},indent=2,sort_keys=True))
