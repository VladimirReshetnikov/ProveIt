from pathlib import Path
import collections,itertools,json,sys
sys.dont_write_bytecode=True
import source_inventory as I
ROOT=Path('.').resolve()
BASE=ROOT/'upstream/U208_ConPA_History_2026-10-29/U208_ConPA_History_2026-10-29'
T=I.read(BASE/'machine/u208.native.tm')
C=json.loads((ROOT/'analysis/reduction_search/window7_contexts.json').read_text())

def left_tag(q,b):
 vals=set()
 for cylinder in C[str(q)]:
  c=dict(cylinder)
  if 0 in c and c[0]!=b:continue
  vals.update([c[-1]]if -1 in c else[0,1])
 return next(iter(vals))if len(vals)==1 else None

def pairs(t):
 states=sorted({q for q,b in t});out=[]
 for a,b in itertools.combinations([q for q in states if q!=0],2):
  for bit in(0,1):
   if t[a,1-bit]!=t[b,1-bit]:continue
   if t[a,bit][:2]!=(bit,1)or t[b,bit][:2]!=(bit,1):continue
   if t[a,bit]==t[b,bit]:continue
   ta,tb=left_tag(a,bit),left_tag(b,bit)
   if ta is None or tb is None or ta==tb:continue
   u,v=(a,b)if ta==0 else(b,a)
   ds=[]
   for q in(u,v):ds.append([x for x in states if x not in(u,v)and t[x,bit]==t[q,bit]])
   out.append({'zero_tag_state':u,'one_tag_state':v,'changed_bit':bit,'zero_donors':ds[0],'one_donors':ds[1],'old_rows':[t[u,bit],t[v,bit]],'other_row':t[u,1-bit]})
 return out

if __name__=='__main__':
 ps=pairs(T);combinations=[]
 for i,p in enumerate(ps):
  for j,q in enumerate(ps[:i]):
   removed={p['one_tag_state'],q['one_tag_state']};affected={p['zero_tag_state'],p['one_tag_state'],q['zero_tag_state'],q['one_tag_state']}
   if len(affected)!=4:continue
   if p['changed_bit']==q['changed_bit']:
    h0=(set(p['zero_donors'])&set(q['zero_donors']))-affected
    h1=(set(p['one_donors'])&set(q['one_donors']))-affected
   else:
    h0=(set(p['zero_donors'])&set(q['zero_donors']))-affected
    h1=(set(p['one_donors'])&set(q['one_donors']))-affected
   if h0 and h1:combinations.append({'pairs':[i,j],'helper_zero_targets':sorted(h0),'helper_one_targets':sorted(h1)})
 out=ROOT/'analysis/comparison/double_helper';out.mkdir(exist_ok=True)
 (out/'direct_pairs.json').write_text(json.dumps({'pairs':ps,'combinations':combinations},indent=2)+'\n')
 print(json.dumps({'pairs':ps,'combinations':combinations},indent=2))
