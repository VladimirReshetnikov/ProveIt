from pathlib import Path
import sys,json,functools,collections
sys.dont_write_bytecode=True;sys.path.insert(0,'analysis/comparison');import source_inventory as I
L=I.L;rs=json.load(open(I.base/'machine/variant_plain/u208.sites.json'));t=I.read(I.base/'machine/variant_plain/u208.native.tm');root,occ,_=I.inventory(t,rs);g=L.graph_arithmetic(rs)[0]
raw=Path('analysis/reduction_search/source_zero.bin').read_bytes();masks={i:[v for v in range(512)if raw[i*512+v]]for i in range(len(rs))}
idx={p:i for i,(p,_,_)in enumerate(rs)}
@functools.lru_cache(None)
def size(n):return 1 if L.leaf(n)else size(n[0])+size(n[1])
def step(i,v,target):
 _,op,a=rs[i];ts=g[i][1]
 if op=='CI':return[v|(1<<a)]if ts[0]==target else[]
 if op=='CD':
  if v>>a&1:return[v&~(1<<a),v]if ts[1]==target else[]
  return[v]if ts[0]==target else[]
 return[v]if target in ts else[]
incoming=collections.defaultdict(list)
for i,(_,ts)in enumerate(g):
 for z in ts:incoming[z].append(i)
entries={}
for q,ns in occ.items():
 vals=set();intervals=[];bad=[]
 for p,n in ns:
  lo=min(i for pp,i in idx.items()if pp.startswith(p));hi=lo+size(n);intervals.append((lo,hi))
  for z in range(lo,hi):
   for i in incoming[z]:
    if not lo<=i<hi:
     if z!=lo:bad.append((i,z))
     else:
      for v in masks[i]:vals.update(step(i,v,z))
  if lo==0:vals.add(1)
 un=0
 for v in vals:un|=v
 entries[q]={'zero':[i for i in range(9)if not(un>>i&1)],'masks':sorted(vals),'intervals':intervals,'external_interior':bad}
linear=json.load(open('analysis/comparison/linear_donors.json'))[0]['recognized'];results=[]
for a in linear:
 q=a['state'];zeros=set(entries[q]['zero'])
 if entries[q]['external_interior']:continue
 for b in linear:
  r=b['state']
  if r==q:continue
  equal=all(a['matrix'][i][j]==b['matrix'][i][j]for i in range(9)for j in range(10)if j not in zeros)
  if equal:
   rec={'q':q,'r':r,'zero':sorted(zeros),'entry':entries[q]};results.append(rec);print(json.dumps(rec),flush=True)
Path('analysis/reduction_search/source_external_entries.json').write_text(json.dumps(entries,indent=2)+'\n');Path('analysis/reduction_search/conditional_linear_donors.json').write_text(json.dumps(results,indent=2)+'\n')
print('candidates',len(results))
for q in[8,110,127,197,91]:print('entries',q,entries[q]['zero'],entries[q]['external_interior'][:5])
