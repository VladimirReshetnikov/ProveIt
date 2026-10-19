"""Recheck finite edge survivors with universal affine instruction contracts."""
import sys,re,json,time
from collections import defaultdict
from pathlib import Path
BASE=Path('/workspace/scratch/b65d0f102007/sources/context246/zfc-context246')
HERE=Path(__file__).parent
sys.path.insert(0,str(BASE/'code'))
sys.path.insert(0,str(BASE/'sources/prior'))
import prefix_affine as A
import rebuild_machines as B
import review_affine_source as R

T={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in B.build().items()}
S=defaultdict(list)
for line in (HERE/'edge_results.txt').read_text().splitlines():
    m=re.fullmatch(r'SURVIVOR (\d+) (\d+) orig=(\d+) (-?\d+) (\d+) new=(\d+) (-?\d+) (\d+) cases=(\d+)',line)
    if m:
        a,b,w,d,q,x,y,z,n=map(int,m.groups());S[a,b].append((x,'R' if y==1 else 'L',z))

# Derive exact full-source successor-PC targets independently.
nodes,sites=R.parse_source(BASE/'sources/Prog254.v')
cases=[]; byedge=defaultdict(list)
class Logged(dict):
    def __getitem__(self,key):
        seen.add(key)
        return super().__getitem__(key)

for p,op,r in sites:
    for zero in ((True,False) if op=='CD' else (None,)):
        branch=(r,zero) if op=='CD' else None
        extra=0;effect=None;overflow=False
        if op=='CI':successor,overflow=R.full_inc(p);effect=('inc',r)
        elif op=='CD' and not zero:successor,overflow=R.full_inc(p);effect=('dec',r);extra=1
        elif op=='CD':successor,overflow=R.full_inc(R.full_strip(p,'0',1))
        elif op=='CB':successor,overflow=R.full_inc(R.full_strip(p,'0',r))
        elif op=='CC':successor=R.full_strip(p,'1',r)
        else:successor=''
        right=[('b',int(b)) for b in successor]+[('r',0,1,40+extra+int(overflow)-len(successor)),('b',1),('box',('plain',effect))]
        target=A.canon([('b',1)],right)
        seen=set()
        A.run(Logged(T),p,branch,target,halt=op=='CH',fuel=1000)
        i=len(cases);cases.append((p,branch,target,op=='CH'))
        for e in seen:byedge[e].append(i)

out=[];t0=time.monotonic()
for (a,b), choices in S.items():
    e=str(a),b
    if not byedge[e]:continue
    for w,d,q in choices:
        candidate=T.copy();candidate[e]=(w,d,str(q))
        error=None;tested=0
        for i in byedge[e]:
            p,branch,target,halt=cases[i]
            try:A.run(candidate,p,branch,target,halt=halt,fuel=1000)
            except Exception as ex:
                error=repr(ex);break
            tested+=1
        row=dict(edge=[a,b],replacement=[w,d,q],universal_decoder_cases=len(byedge[e]),passed=tested,status='PASS' if error is None else 'FAIL')
        if error is not None:row['counterexample']=[p,branch,error]
        out.append(row)
        if error is None:print('SYMBOLIC',a,b,'->',w,d,q,'cases',tested,flush=True)

(HERE/'edge_symbolic.json').write_text(json.dumps(out,indent=2)+'\n')
print('DONE',len(out),'passed',sum(x['status']=='PASS' for x in out),'seconds',time.monotonic()-t0,flush=True)
