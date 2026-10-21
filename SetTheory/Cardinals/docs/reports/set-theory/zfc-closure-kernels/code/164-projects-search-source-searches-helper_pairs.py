import sys,json,collections
from pathlib import Path
OUT=Path(__file__).resolve().parent.parent/"search-output"
OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'vendor'))
import source_language as s,build221 as b,source_splice as sp
base=(Path(__file__).resolve().parent.parent/'inputs')
T=b.read_table((base/'k217.native.tm').read_bytes());root=s.tree(json.loads((base/'sites217.json').read_bytes()));G,P=b.decoder_map(T,root)
states=sorted({q for q,bit in T});inc=collections.defaultdict(list)
for (q,bit),(w,d,t)in T.items():inc[t].append((q,bit,w,d))
marks={q:next(iter(ws))for q in states if q!=0 and inc[q]and all(d==1 for _,_,w,d in inc[q])and len(ws:={w for _,_,w,d in inc[q]})==1}
results=[]
for a in states:
 for c in states:
  if a>=c or a not in marks or c not in marks or marks[a]==marks[c]:continue
  for bit in(0,1):
   if T[a,1-bit]!=T[c,1-bit]or T[a,bit]==T[c,bit]or T[a,bit][:2]!=(bit,1)or T[c,bit][:2]!=(bit,1):continue
   x,y=(a,c)if marks[a]==0 else(c,a)
   qs0=[q for q in G if T[q,bit]==T[x,bit]];qs1=[q for q in G if T[q,bit]==T[y,bit]]
   pairs=[(j,k)for j in qs0 for k in qs1 if j not in(a,c)and k not in(a,c)]
   results.append(dict(pair=[x,y],bit=bit,targets=[T[x,bit][2],T[y,bit][2]],helpers=pairs,incoming=[inc[x],inc[y]]))
for r in results:print(r)
(OUT/'helper-pairs.json').write_text(json.dumps(results,indent=2)+'\n')
