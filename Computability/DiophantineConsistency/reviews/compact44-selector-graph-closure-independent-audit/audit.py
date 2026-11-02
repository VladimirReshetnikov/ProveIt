#!/usr/bin/env python3
"""Independent source and same-side provider checks, without Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';PLAN=BASE/'compact44-selector-graph-closure-plan';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name in ('scan.py','scan.json','README.md'):
 p=PLAN/name;old=subprocess.run(['git','show','5ddcc302c8:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(old).hexdigest()==H(p),name
scan=json.loads((PLAN/'scan.json').read_bytes());q=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,text=True,timeout=120);assert q.returncode==0 and not q.stderr and json.loads(q.stdout)==scan
q=subprocess.run([sys.executable,'-I','-S','-O','-B',str(PLAN/'scan.py')],capture_output=True,text=True,timeout=120);assert q.returncode!=0 and 'requires nonoptimized' in q.stderr
names=['CompactPositionIncrement','CompactPositionGraph','CompactSelectorMask','CompactSelectorGraph'];imports=[['CompactMixedIncrement'],['CompactSameWitnessSaturation2','CompactPositionIncrement'],['CompactPositionGraph'],['CompactSelectorMask']];report_names=[['CompactPositionCarry.increment_digits'],['CompactPositionCarry.generic_position_noCarry','CompactPositionCarry.fixed_position_noCarry'],['CompactSelectorMask.selector_mask_digit','CompactSelectorMask.absent_mask_digit'],['CompactSelectorGraph.selector_slot','CompactSelectorGraph.excluded_slot','CompactSelectorGraph.fixed_graph_selector_bounds']]
for row,name,imps,reports in zip(scan['source_order'],names,imports,report_names):
 p=Path(row['source']);assert row['module']=='DiophantineConsistency.'+name and H(p)==row['source_sha256']
 blob=subprocess.run(['git','show',row['source_commit']+':'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==row['source_sha256']
 assert [line[7:] for line in p.read_text().splitlines() if line.startswith('import ')]==['DiophantineConsistency.'+x for x in imps]==row['imports']
 assert re.findall(r'^#print axioms\s+(\S+)',p.read_text(),re.M)==reports==row['axiom_reports']
for z in scan['objects']:
 for side in ('author_resolved','peer_resolved'):
  p=Path(z[side]);assert p.is_file() and H(p)==z['sha256']
assert len(scan['objects'])==146
for key,count in [('external_direct_companion_slots',40),('target_companion_slots',80),('package_init_companion_slots',10)]:
 slots=scan[key];assert len(slots)==count
 for name,prior in slots.items():
  p=Path(name)
  if prior is None:assert not os.path.lexists(p),name
  else:assert p.is_file() and str(p.resolve())==prior['realpath'] and H(p)==prior['sha256'],name
assert all(v is None for v in scan['target_companion_slots'].values())
for side in ('author','peer'):
 lib=Path('/tmp/ipra-same-witness-saturation-pair-01')/side/'lib'/'DiophantineConsistency';available={'CompactMixedIncrement','CompactSameWitnessSaturation2'}
 for name,imps in zip(names,imports):
  for x in imps:
   assert x in available
   if x in ('CompactMixedIncrement','CompactSameWitnessSaturation2'):assert (lib/(x+'.olean')).is_file()
  available.add(name)
print(json.dumps({'status':'PASS_INDEPENDENT_SELECTOR_GRAPH_SOURCE_CLOSURE','reviewed_commit':'5ddcc302c8','source_modules':4,'source_order':names,'parent_objects_per_side':146,'direct_slots':40,'target_slots':80,'init_slots':10,'source_report_counts':[1,2,2,3],'lean_launched':False,'scope':'Point-in-time source and same-side provider scan, not a parent rerun or paired build; no tuple binding, local decoder premise, machine simulation or internal iPRA theorem.'},indent=2))
