from pathlib import Path
import sys,json,time,traceback
from collections import Counter
B=Path(__file__).resolve().parents[1]/'reference/context246'
sys.path.insert(0,str(B/'code'))
import review_affine_source as audit
import rebuild_machines as base
A=audit.module(B/'sources/prior/prefix_affine.py')
_,sites=audit.parse_source(B/'sources/Prog254.v')
T={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in base.build().items()}
# Sound targets exactly as the full source audit, but allow cached CEGIS order.
cases=[]
for p,op,r in sites:
  for zero in ((True,False) if op=='CD' else (None,)):
    branch=(r,zero) if op=='CD' else None
    extra,effect,overflow=0,None,False
    if op=='CI': successor,overflow=audit.full_inc(p);effect=('inc',r)
    elif op=='CD' and not zero: successor,overflow=audit.full_inc(p);effect,extra=('dec',r),1
    elif op=='CD': successor,overflow=audit.full_inc(audit.full_strip(p,'0',1))
    elif op=='CB': successor,overflow=audit.full_inc(audit.full_strip(p,'0',r))
    elif op=='CC': successor=audit.full_strip(p,'1',r)
    else: successor=''
    gap=40+extra+int(overflow)-len(successor)
    target=A.canon([('b',1)],[('b',int(b)) for b in successor]+[('r',0,1,gap),('b',1),('box',('plain',effect))])
    cases.append((p,branch,target,op=='CH'))
