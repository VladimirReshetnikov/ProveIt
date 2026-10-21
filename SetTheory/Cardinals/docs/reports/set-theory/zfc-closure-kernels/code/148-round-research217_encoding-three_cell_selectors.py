"""Owned exact two-predecessor-history marker selector screen."""
from pathlib import Path
import sys,json,time,collections,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'k223_merged_runtime_audit/runtime'));import independent_runtime as R
path=ROOT/'latest218_baseline/candidate-k218/k218.native.tm';T=R.table(path);states=sorted({q for q,b in T});incoming=collections.defaultdict(list)
for(q,b),(w,d,z)in T.items():incoming[z].append((q,b,w,d))
markers={}
for q in states:
 if q==0 or not incoming[q]or any(d!=1 or p==0 for p,b,w,d in incoming[q]):continue
 if any(not incoming[p]or any(dd!=1 for pp,bb,ww,dd in incoming[p])for p,b,w,d in incoming[q]):continue
 markers[q]=sorted({(ww,w)for p,b,w,d in incoming[q]for pp,bb,ww,dd in incoming[p]})
pairs=[]
for q in markers:
 for r in markers:
  if q>=r or set(markers[q])&set(markers[r]):continue
  same=[b for b in(0,1)if T[q,b]==T[r,b]]
  if len(same)==1:pairs.append(dict(states=[q,r],markers=[markers[q],markers[r]],shared_read=same[0]))
start=time.monotonic();steps=0;CAP_STEPS=100000;CAP_SECS=5;OUTPUT_PATH=OUT/'THREE_CELL_SELECTOR_SCREEN.json'
class Cap(Exception):pass

def walk(w,H,marker):
 global steps
 q=H;h=-1;bits={-2:marker[0],-1:marker[1],0:w};trace=[];points=[];seen=set()
 for i in range(32):
  points.append(dict(q=q,h=h,bits=[bits[-2],bits[-1],bits[0]],trace=list(trace)))
  key=q,h,tuple(bits.values())
  if key in seen:return dict(status='CYCLE',points=points)
  seen.add(key)
  if q==254:return dict(status='HALT',points=points)
  if h not in bits:return dict(status='OPAQUE_EXIT',points=points)
  if i==31:return dict(status='STEP_BOUND_UNKNOWN',points=points)
  if steps>=CAP_STEPS or time.monotonic()-start>=CAP_SECS:raise Cap()
  bit=bits[h];ww,d,z=T[q,bit];trace.append([q,h,bit,ww,d,z]);bits[h]=ww;h+=d;q=z;steps+=1

def good(pt,forbid,marker,act,phi):
 w,d,z=act
 return phi(pt['q'])==phi(z)and pt['h']==d and pt['bits']==[*marker,w]and all(x[0]not in forbid for x in pt['trace'])

def main():
 catalog={};reports=[];hits=[];near=[]
 try:
  for w in(0,1):
   for H in states:
    for marker in((0,0),(0,1),(1,0),(1,1)):catalog[w,H,marker]=walk(w,H,marker)
  for pair in pairs:
   q,r=pair['states'];b=1-pair['shared_read'];forbid={q,r};phi=lambda s:q if s==r else s;phits=[];counts=collections.Counter()
   for w in(0,1):
    for H in states:
     if H in forbid:continue
     outcomes=[];witnesses=[];wrong=[]
     for role,ms in zip(pair['states'],pair['markers']):
      rw=[];bad=[]
      for marker in ms:
       pts=catalog[w,H,marker]['points'];hit=next((pt for pt in pts if good(pt,forbid,marker,T[role,b],phi)),None)
       if hit:rw.append(dict(marker=marker,endpoint=hit))
       else:
        oldw,d,z=T[role,b]
        restored=[pt for pt in pts if pt['h']==d and pt['bits']==[*marker,oldw]and all(x[0]not in forbid for x in pt['trace'])]
        bad.append(dict(marker=marker,expected_target=z,restored_wrong=restored[-1]if restored else None,stop=catalog[w,H,marker]['status']))
      outcomes.append(not bad);witnesses.append(rw);wrong.append(bad)
     if all(outcomes):
      hit=dict(**pair,read=b,action=[w,-1,H],witnesses=witnesses);hits.append(hit);phits.append(hit)
     elif any(outcomes):
      counts['one_role_matches']+=1;bad=outcomes.index(False)
      if all(x['restored_wrong']is not None for x in wrong[bad]):near.append(dict(**pair,read=b,action=[w,-1,H],matching_role=pair['states'][1-bad],missing_role=pair['states'][bad],witnesses=witnesses[1-bad],failures=wrong[bad]))
   reports.append(dict(**pair,matches=len(phits),**counts))
 except Cap:reports.append(dict(status='AGGREGATE_CAP_UNKNOWN'))
 data=dict(status='COMPLETE'if len(reports)==len(pairs)else'INCOMPLETE',table_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),marker_states=len(markers),marker_premises={str(q):dict(marker_sets=markers[q],incoming=incoming[q],predecessor_incoming={str(p):incoming[p]for p,b,w,d in incoming[q]})for q in markers},pairs=reports,matches=hits,near_matches=near,helper_transitions=steps,seconds=time.monotonic()-start,scope='All-initial-tape invariant from two successive R-writing incoming transitions. Start q=0 and direct predecessor p=0 excluded. New first action writes0/1 then L to an unchanged existing helper; exact old state/head/three-cell tape at positive1..32-step endpoint, arbitrary exterior untouched and unqueried. Interior folded states forbidden, no halts crossed. Negative covers only this family.')
 OUTPUT_PATH.write_text(json.dumps(data,indent=2)+'\n')
 print(json.dumps({k:v for k,v in data.items()if k not in('marker_premises','pairs','near_matches')},indent=2));print('near_count',len(near));print(json.dumps([{k:v for k,v in n.items()if k not in('witnesses','failures')}|dict(failures=[dict(marker=f['marker'],expected=f['expected_target'],actual=f['restored_wrong']['q'])for f in n['failures']])for n in near],indent=2))
if __name__=='__main__':main()
