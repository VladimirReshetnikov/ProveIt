from core import *
from pathlib import Path
import hashlib,json
D={3:17,4:144,5:45,6:21}
rows,labels=machine();cs=contracts();dense={q:i for i,q in enumerate(labels)}

def literal(r):return ''.join(f'{dense[q]} {b} {w} {"R"if d else"L"} {dense[n]}\n'for q in labels[:-1]for b in(0,1)for w,d,n in[r[q,b]])
def runlit(r,count):
 q=74;h=0;ones=set()
 for i in range(count):
  b=int(h in ones)
  if(q,b)not in r:return None
  w,d,q=r[q,b]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=1 if d else-1
 return q,h,sorted(ones)
seed=runlit(rows,58154);out=[]
for r,target in D.items():
 rr=rows.copy();rr[1365,1]=(1,True,target)
 assert all(rr[q,b]==rows[q,b] for q in BOXSTATES for b in (0,1))
 cc=[(i,(PHYSICAL[r],True)if i==3692 else br,s,t)for i,br,s,t in cs]
 ans=validate(rr,cc);startup=runlit(rr,58154)==seed
 print('r',r,ans,'startup',startup,flush=True)
 if not ans['ok']or not startup:continue
 body=literal(rr);path=Path(f'pa196_close_cd{r}.tm');path.write_text(body)
 native=''.join(f'{q} {b} {w} {"R"if d else"L"} {n}\n'for(q,b),(w,d,n)in sorted(rr.items()));Path(f'pa196_close_cd{r}.native.tm').write_text(native)
 out.append({'register':r,'table':path.name,'sha256':hashlib.sha256(body.encode()).hexdigest(),'native_patch':{'row':[1365,1],'old':list(rows[1365,1]),'new':[1,True,target]},'dense_row':[dense[1365],1],'new_dense_action':[1,'R',dense[target]],'validation':ans,'startup_exact':startup,'state_count':196,'ordinary_proof':'At source3692 the final AX guard has cleared logical registers3,4,5,6,7. Zero branch of CD r equals the old breakTo1 continuation. All other primitive contracts and seed identical.','kernel_checked':False})
Path('closing_patch_receipt.json').write_text(json.dumps(out,indent=2))
