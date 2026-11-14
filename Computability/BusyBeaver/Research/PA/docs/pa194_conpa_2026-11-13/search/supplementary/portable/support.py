"""Unchanged apply/localvalid helpers extracted from the supplied PA195 support.py.
Only these functions are needed by the supplementary searches.
"""
def apply(rows,chosen):
 aliases={a:b for a,b,acts in chosen};actions={b:acts for a,b,acts in chosen};folded={}
 for(q,bit),act in rows.items():
  if q in aliases:continue
  w,d,n=actions[q][bit]if q in actions else act
  folded[q,bit]=w,d,aliases.get(n,n)
 return folded,aliases

def localvalid(rows,folded,alias,chosen):
 for a,b,acts in chosen:
  for q,p in ((a,0),(b,1)):
   for v in(0,1):
    w,d,n=rows[q,v];target=alias.get(n,n);wanthead=1 if d else -1;expect={-1:p,0:w}
    tape={-1:p,0:v};pos=0;now=b
    for step in range(20):
     if step and pos==wanthead and now==target and tape==expect:break
     if pos not in tape:return False
     act=folded.get((now,tape[pos]))
     if act is None:return False
     w2,d2,now=act;tape[pos]=w2;pos+=1 if d2 else -1
    else:return False
 return True
