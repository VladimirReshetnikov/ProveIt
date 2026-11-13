#!/usr/bin/env python3
"""Independent read-only source-order and same-side provider inventory audit."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';PLAN=BASE/'compact44-copy-support-closure-plan';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name in ('scan.py','scan.json','README.md','terminal-observation.json'):
 p=PLAN/name;blob=subprocess.run(['git','show','0c758f7594:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==H(p),name
scan=json.loads((PLAN/'scan.json').read_bytes());q=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],cwd=ROOT,capture_output=True,text=True,timeout=120);assert q.returncode==0 and not q.stderr and json.loads(q.stdout)==scan
q=subprocess.run([sys.executable,'-I','-S','-O','-B',str(PLAN/'scan.py')],cwd=ROOT,capture_output=True,text=True,timeout=120);assert q.returncode!=0 and 'optimized Python rejected' in q.stderr
names=['CompactPositionIncrement','CompactPositionGraph','CompactSelectorMask','CompactSelectorGraph','Compact943Data','CompactCoefficientMass','CompactSymbolicKernel','CompactSupportSlot','CompactCopySupport']
imports=[['CompactMixedIncrement'],['CompactSameWitnessSaturation2','CompactPositionIncrement'],['CompactPositionGraph'],['CompactSelectorMask'],['ArithmeticWindowDigits'],['Compact943Data'],['CompactCoefficientMass'],['CompactSelectorGraph'],['CompactSupportSlot','CompactSymbolicKernel']]
counts=[1,2,2,3,3,8,2,3,2];assert len(scan['source_order'])==9
for row,name,imps,count in zip(scan['source_order'],names,imports,counts):
 p=Path(row['source']);assert row['module']=='DiophantineConsistency.'+name and H(p)==row['source_sha256'];blob=subprocess.run(['git','show',row['source_commit']+':'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==row['source_sha256']
 assert [line[7:] for line in p.read_text().splitlines() if line.startswith('import ')]==['DiophantineConsistency.'+x for x in imps]==row['imports']
 reports=re.findall(r'^#print axioms\s+(\S+)',p.read_text(),re.M);assert reports==row['axiom_reports'] and len(reports)==count and len(set(reports))==count
for side in ('author','peer'):
 rows=scan['objects'][side];assert len(rows)==146
 for z in rows:
  p=Path(z['resolved']);assert p.is_file() and H(p)==z['sha256']
assert [(z['path'],z['sha256']) for z in scan['objects']['author']]==[(z['path'],z['sha256']) for z in scan['objects']['peer']]
for key,count in [('external_direct_slots',60),('target_slots',180),('init_slots',10)]:
 slots=scan[key];assert len(slots)==count
 for name,prior in slots.items():
  p=Path(name)
  if prior is None:assert not os.path.lexists(p),name
  else:assert p.is_file() and str(p.resolve())==prior['resolved'] and H(p)==prior['sha256'],name
assert all(v is None for v in scan['target_slots'].values())
for side in ('author','peer'):
 lib=Path('/tmp/ipra-same-witness-saturation-pair-01')/side/'lib'/'DiophantineConsistency';available={'CompactMixedIncrement','CompactSameWitnessSaturation2','ArithmeticWindowDigits'}
 for name,imps in zip(names,imports):
  for dep in imps:
   assert dep in available,(name,dep)
   if dep in ('CompactMixedIncrement','CompactSameWitnessSaturation2','ArithmeticWindowDigits'):assert (lib/(dep+'.olean')).is_file()
  available.add(name)
print(json.dumps({'status':'PASS_INDEPENDENT_COPY_SUPPORT_SOURCE_CLOSURE','reviewed_commit':'0c758f7594','source_modules':9,'source_order':names,'source_report_counts':counts,'parent_objects_per_side':146,'direct_slots':60,'target_slots':180,'init_slots':10,'lean_launched':False,'scope':'Point-in-time source and same-side provider inventory, not a parent rerun or paired build. The final theorem has explicit graph and positive position/residue assumptions, and does not prove retained K binding, word/column construction, machine or iPRA equivalence.'},indent=2))
