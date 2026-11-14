import sys,json,collections
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,'analysis/comparison')
import source_inventory as I
L=I.L
results=[]
for label,tp,sp in [('A',I.base/'machine/variant_plain/u208.native.tm',I.base/'machine/variant_plain/u208.sites.json'),('B',I.base/'machine/u208.native.tm',I.base/'machine/u208.sites.json')]:
 t=I.read(tp);rows=json.loads(sp.read_text());root,occ,rots=I.inventory(t,rows)
 @__import__('functools').lru_cache(None)
 def word(n):return (n,)if L.leaf(n)else word(n[0])+word(n[1])
 states=sorted({q for q,b in t});seen={0};stack=[0]
 while stack:
  q=stack.pop()
  if q==84:continue
  for b in(0,1):
   z=t[q,b][2]
   if z!=254 and z not in seen:seen.add(z);stack.append(z)
 sourceonly={8,78,84,95,101,110,127,145,189}
 print('class',label,'sourceonly',sorted(sourceonly))
 signatures={q:{word(n) for _,n in ns}for q,ns in occ.items()}
 for q in sorted(sourceonly|{84}):
  if q not in occ:continue
  ns=occ[q];print(q,len(ns),'words',sorted(set(len(word(n))for _,n in ns)),'variants',len(signatures[q]),'boundaries',sorted(set(L.boundary(n)for _,n in ns)))
  for r in occ:
   if r==q:continue
   if signatures[r]==signatures[q]:
    print('DONOR',q,r)
    results.append({'class':label,'q':q,'r':r,'words':[list(w)for w in signatures[q]],'same_trees':{n for _,n in occ[q]}=={n for _,n in occ[r]}})
Path('analysis/reduction_search/word_donors.json').write_text(json.dumps(results,indent=2)+'\n')
