from pathlib import Path
import sys,json,collections,itertools,functools
sys.dont_write_bytecode=True
sys.path.insert(0,'analysis/comparison');import source_inventory as I
L=I.L
@functools.lru_cache(None)
def word(n):return(n,)if L.leaf(n)else word(n[0])+word(n[1])
def norm(w):
 out=[];i=0
 while i<len(w):
  if w[i][0]!='CI':out.append(w[i]);i+=1;continue
  j=i
  while j<len(w)and w[j][0]=='CI':j+=1
  out.extend(sorted(w[i:j]));i=j
 return tuple(out)
results=[]
for label,tp,sp in [('A',I.base/'machine/variant_plain/u208.native.tm',I.base/'machine/variant_plain/u208.sites.json'),('B',I.base/'machine/u208.native.tm',I.base/'machine/u208.sites.json')]:
 t=I.read(tp);rows=json.loads(sp.read_text());root,occ,rots=I.inventory(t,rows)
 signatures={q:frozenset(norm(word(n))for _,n in ns)for q,ns in occ.items()}
 pairs=[]
 for q,r in itertools.combinations(occ,2):
  if signatures[q]==signatures[r]:
   pair={'q':q,'r':r,'q_occ':len(occ[q]),'r_occ':len(occ[r]),'q_words':[word(n)for _,n in occ[q]],'r_words':[word(n)for _,n in occ[r]]};pairs.append(pair);print(label,q,r,len(occ[q]),len(occ[r]),flush=True)
 results.append({'label':label,'pairs':pairs})
Path('analysis/reduction_search/commuting_donors.json').write_text(json.dumps(results,indent=2)+'\n')
