"""Owned two-cell all-tape marker-selector catalog and pair screen."""
from pathlib import Path
import sys,json,time,collections
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'k223_merged_runtime_audit/runtime'));import independent_runtime as R
T=R.table(ROOT/'latest218_baseline/candidate-k218/k218.native.tm');states=sorted({q for q,b in T});pairs=json.load(open(OUT/'MARKED_PAIR_INVENTORY.json'))['pairs']
start=time.monotonic();steps=0
class Cap(Exception):pass

def walk(b,w,H,marker):
 global steps
 q=H;h=-1;bits={-1:marker,0:w};trace=[];points=[];seen=set()
 for i in range(32):
  points.append(dict(q=q,h=h,bits=[bits[-1],bits[0]],trace=list(trace)))
  key=q,h,bits[-1],bits[0]
  if key in seen:return dict(status='CYCLE',points=points)
  seen.add(key)
  if q==254:return dict(status='HALT',points=points)
  if h not in bits:return dict(status='OPAQUE_EXIT',points=points)
  if i==31:return dict(status='STEP_BOUND_UNKNOWN',points=points)
  if steps>=100000 or time.monotonic()-start>=5:raise Cap()
  read=bits[h];ww,d,z=T[q,read];trace.append([q,h,read,ww,d,z]);bits[h]=ww;h+=d;q=z;steps+=1

def validpoint(point,forbid,marker,oldwrite,move,target,phi):
 return phi(point['q'])==phi(target)and point['h']==move and point['bits']==[marker,oldwrite]and all(r[0]not in forbid for r in point['trace'])

def main():
 catalog={};reports=[];matches=[];near=[]
 try:
  for b in(0,1):
   for w in(0,1):
    for H in states:
     for marker in(0,1):catalog[b,w,H,marker]=walk(b,w,H,marker)
  for pair in pairs:
   q,r=pair['states'];b=1-pair['shared_read'];forbid={q,r};phi=lambda s:q if s==r else s
   hits=[];single=0
   for w in(0,1):
    for H in states:
     if H in forbid:continue
     outcomes=[];witnesses=[]
     for old,marker in zip(pair['states'],pair['markers']):
      act=T[old,b];walked=catalog[b,w,H,marker];pts=walked['points'];good=next((pt for pt in pts if validpoint(pt,forbid,marker,*act,phi)),None)
      outcomes.append(good is not None);witnesses.append(good)
     if all(outcomes):
      hit=dict(pair=pair['states'],markers=pair['markers'],read=b,action=[w,-1,H],witnesses=witnesses);hits.append(hit);matches.append(hit)
     elif any(outcomes):
      single+=1;bad=outcomes.index(False);old=pair['states'][bad];marker=pair['markers'][bad];act=T[old,b];ww,d,z=act
      wrong=[pt for pt in catalog[b,w,H,marker]['points']if pt['h']==d and pt['bits']==[marker,ww]and all(row[0]not in forbid for row in pt['trace'])]
      if wrong:
       near.append(dict(pair=pair['states'],markers=pair['markers'],read=b,action=[w,-1,H],matching_role=pair['states'][1-bad],missing_role=old,expected_target=z,actual_target=wrong[-1]['q'],wrong_trace=wrong[-1]['trace'],matching_trace=witnesses[1-bad]['trace']))
   reports.append(dict(pair=pair['states'],read=b,matches=len(hits),one_marker_matches=single))
 except Cap:reports.append(dict(status='AGGREGATE_CAP_UNKNOWN'))
 data=dict(status='COMPLETE'if len(reports)==len(pairs)else'INCOMPLETE',table_sha256=__import__('hashlib').sha256((ROOT/'latest218_baseline/candidate-k218/k218.native.tm').read_bytes()).hexdigest(),pairs=reports,matches=matches,near_matches=near,helper_transitions=steps,seconds=time.monotonic()-start,scope='Existing unchanged helper entries, two known cells, first move left, either first write; exact old whole-tape endpoint within32total steps. Folded states forbidden inside helper. No right-exterior assumptions. Negatives are restricted-family results.')
 (OUT/'TWO_CELL_SELECTOR_SCREEN.json').write_text(json.dumps(data,indent=2)+'\n')
 print(json.dumps({k:v for k,v in data.items()if k not in('near_matches','pairs')},indent=2));print('near_count',len(near));print(json.dumps([{k:v for k,v in n.items()if'trace'not in k}for n in near[:40]],indent=2))
if __name__=='__main__':main()
