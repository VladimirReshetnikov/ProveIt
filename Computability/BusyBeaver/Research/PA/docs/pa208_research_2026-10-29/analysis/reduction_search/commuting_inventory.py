from pathlib import Path
import sys,json,collections,itertools,functools
sys.dont_write_bytecode=True
sys.path.insert(0,'analysis/comparison');import source_inventory as I
L=I.L
@functools.lru_cache(None)
def word(n):return(n,)if L.leaf(n)else word(n[0])+word(n[1])
def inventory(label,t,rows):
 root,occ,rots=I.inventory(t,rows);out=[]
 for q,ns in occ.items():
  words={word(n)for _,n in ns}
  if all(all(op=='CI'for op,a in w)for w in words) and any(len(w)>1 for w in words):
   sigs={tuple(sorted(a for op,a in w))for w in words}
   out.append({'q':q,'occurrences':len(ns),'words':[list(w)for w in words],'sigs':[list(s)for s in sigs],'allnonleaf':all(not L.leaf(n)for _,n in ns)})
 print(label,json.dumps(out),flush=True)
 pairs=[]
 for a,b in itertools.combinations(out,2):
  if sorted(a['sigs'])==sorted(b['sigs']):pairs.append([a['q'],b['q']])
 return{'label':label,'inventory':out,'pairs':pairs}
results=[]
for label,tp,sp in [('A',I.base/'machine/variant_plain/u208.native.tm',I.base/'machine/variant_plain/u208.sites.json'),('B',I.base/'machine/u208.native.tm',I.base/'machine/u208.sites.json')]:results.append(inventory(label,I.read(tp),json.loads(sp.read_text())))
Path('analysis/reduction_search/commuting_inventory.json').write_text(json.dumps(results,indent=2)+'\n')
