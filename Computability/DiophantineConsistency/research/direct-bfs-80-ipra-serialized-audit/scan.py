#!/usr/bin/env python3
"""Capture actual selected project closure and producer-direct overlaps for the BFS fixed iPRA client."""
from pathlib import Path
from hashlib import sha256
import importlib.util,json,os,sys,traceback
H=Path(__file__).resolve().parent;D=H.parents[1]
BASE=D/'research/ordinary12-direct90-ipra-join/run-v9.py'
ROOT=D/'research/direct-bfs-80-ipra-fixed-prototype/observations/directbfs80iprafixed-attempt01/terminal.json'
OBS=H/'observations/attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
need(not OBS.exists(),'attempt exists')
need(sha(BASE)=='117ca7e29a4822832ffbe8a213431c89c770f1f51ddaa9ee11efee4b7fe15f03','scanner implementation pin')
need(sha(ROOT)=='43185de3adf1609baed29e0fdf951276238f54fba5319d3bd05d1162213a3db7','root receipt pin')
OUTER=D/'research/direct-bfs-80-ipra-fixed-prototype/observations/outer-attempt01/terminal.json'
need(sha(OUTER)=='ac6654aeeeb4300ac952127414cbd2e0886cd150a9c49c129d1db3dd80b034ab','outer receipt pin')
out=json.loads(OUTER.read_text());need(out['exit']==0 and out['pins']==out['after'],'outer runner failed or drifted')
spec=importlib.util.spec_from_file_location('reviewed_v9',BASE);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
need(sha(m.LEAN)==m.PINS[m.LEAN] and sha(m.HELPER)==m.PINS[m.HELPER] and sha(m.INVENTORY)==m.PINS[m.INVENTORY],'tool pins')
r=json.loads(ROOT.read_text());need(r['exit']==0 and r['reason'] is None and r['pins']==r['after'] and r['direct_imports']==r['direct_imports_after'],'root failed or changed')
root=Path(r['output_root'])/'DirectBFS80FixedIPRA.olean';need(sha(root)==r['object_sha256']=='2155f5f05a8e993dc3582f3c14ce9c56916d0ac09dc326c02093d83a878e4703','root object changed')
parts=r['lean_path'].split(':');need(Path(parts[-1])==m.PACKAGE,'unexpected last package root')
paths=[root.parent]+[Path(p) for p in parts[:-1]]
env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(root.parent)+':'+r['lean_path'],'LEAN_NUM_THREADS':'1'}
inv=json.loads(m.INVENTORY.read_text());known=set(inv['objects'])|{'DirectBFS80FixedIPRA'}
for base in paths:
 if base.is_dir():known.update(p.stem for p in base.glob('*.olean'))
OBS.mkdir(parents=True);result={'status':'FAILED','scanner_sha256':sha(__file__),'root_receipt_sha256':sha(ROOT),'root_object_sha256':sha(root),'scope':'actual selected project serialized headers, direct external object/companions, live search-path overlaps and captured matching-producer direct object hashes only; package-transitive, dynamic and historical source/object ancestry excluded'}
try:
 closure=m.scan_closure(['DirectBFS80FixedIPRA'],paths,env,OBS,'selected',known)
 m.recheck_outside(closure)
 for name,row in closure['project'].items():
  stem=str(row['path'])[:-len('.olean')];need(m.rec(row['path'])==row['record'] and {x:m.rec(stem+x) for x in m.SUFFIXES}==row['companions'],'selected drift '+name)
 # All current alternatives are reported, including harmless extra-path conflicts.
 overlaps={}
 for name,row in closure['project'].items():
  rel=m.relative_module(name)+'.olean';variants=[]
  for base in paths:
   p=base/rel
   if p.is_file() and all(str(p)!=x['path'] for x in variants):
    stem=str(p)[:-len('.olean')];variants.append({'path':str(p),'record':m.rec(p),'companions':{x:m.rec(stem+x) for x in m.SUFFIXES}})
  if len(variants)>1:overlaps[name]=variants
 # Match live selected objects to captured author receipts when available.
 receipts={}
 for p in (D/'research').glob('*/observations/*/terminal.json'):
  try:
   data=json.loads(p.read_text());out=data.get('output_root');digest=data.get('object_sha256')
   if data.get('exit')!=0 or data.get('reason') or not out or not digest:continue
   if data.get('pins') is not None and data.get('after') is not None and data['pins']!=data['after']:continue
   for n,row in closure['project'].items():
    if row['record']['sha256']==digest and Path(row['path']).parent==Path(out):receipts.setdefault(n,[]).append((p,data))
  except (OSError,ValueError,KeyError,TypeError):continue
 producer={};mismatches=[]
 for name,items in receipts.items():
  producer[name]=[]
  for p,data in items:
   checked=[]
   for dep in data.get('direct_imports',[]):
    n=dep['module'];target=closure['project'].get(n,closure['outside'].get(n))
    if target is None:continue
    ok=dep['sha256']==target['record']['sha256'];checked.append({'module':n,'producer_path':dep['path'],'producer_sha256':dep['sha256'],'selected_path':target['path'],'selected_sha256':target['record']['sha256'],'matches':ok})
    if not ok:mismatches.append({'producer':name,'receipt':str(p),'dependency':n,'producer_sha256':dep['sha256'],'selected_sha256':target['record']['sha256']})
   producer[name].append({'receipt':str(p),'receipt_sha256':sha(p),'direct_imports_compared':checked})
 conflicts={n:v for n,v in overlaps.items() if len({x['record']['sha256'] for x in v})>1}
 for p,h in [(BASE,'117ca7e29a4822832ffbe8a213431c89c770f1f51ddaa9ee11efee4b7fe15f03'),(ROOT,result['root_receipt_sha256']),(OUTER,'ac6654aeeeb4300ac952127414cbd2e0886cd150a9c49c129d1db3dd80b034ab'),(m.LEAN,m.PINS[m.LEAN]),(m.HELPER,m.PINS[m.HELPER]),(m.INVENTORY,m.PINS[m.INVENTORY]),(Path(__file__),result['scanner_sha256'])]:need(sha(p)==h,'input drift '+str(p))
 result.update(status='PASS_CAPTURE',closure=closure,overlaps=overlaps,conflicting_overlaps=sorted(conflicts),producer_direct=producer,producer_direct_mismatches=mismatches,
  report={'project_count':len(closure['project']),'outside_count':len(closure['outside']),'overlap_names':len(overlaps),'conflicting_overlap_names':len(conflicts),'project_with_matching_receipt':len(producer),'direct_import_mismatches':len(mismatches),'header_batches':closure['header_batches']})
except Exception as e:result.update(error=repr(e),traceback=traceback.format_exc())
(OBS/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':result['status'],'error':result.get('error'),'report':result.get('report')}),flush=True)
if result['status']!='PASS_CAPTURE':sys.exit(1)
