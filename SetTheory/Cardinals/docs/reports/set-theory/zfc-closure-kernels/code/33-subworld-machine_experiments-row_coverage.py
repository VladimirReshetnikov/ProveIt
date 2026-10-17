"""Concrete coverage witnesses for every row of the prepared 252-state body.

Each witness starts at a published instruction boundary with a finite tape,
gap 40, nine named registers, and one spare block containing zero.
This is an existential finite check per
row, not a claim that the row is reached on the actual blank-tape run.
"""
from pathlib import Path
import json,hashlib
from tmlib import load
ROOT=Path(__file__).resolve().parent
from prepare_inputs import prepare
prepare()
T,_=load(ROOT/'machine/runtime252_oldlabels.tm')
T={(int(q),b):(w,1 if d=='R' else -1,int(n)) for (q,b),(w,d,n) in T.items()}
REG=dict(wffstack=0,param1=1,axiomcode=2,scratch2=3,scratch1=4,prooflist=5,nextproof=6,topwff=7,param2=8)

def inc(p):
    return None if '0' not in p else p[:p.rindex('0')]+'1'
def strip(b,k,p):
    while k>0:
        if not p:return ''
        if p[-1]==b:k-=1
        p=p[:-1]
    return p
def frame(p,vals,D=40,h=0):
    tape={h-1,h+D}|{h+i for i,b in enumerate(p) if b=='1'}
    j=h+D+1
    for v in vals:
        j+=1
        tape.update(range(j,j+v+1));j+=v+1
    return tape

paths=json.loads((ROOT/'paths.json').read_text())
covered={}; checks=0; total=0; maximum=0
schedule=[(idx,path,op,0) for idx,(path,op) in enumerate(paths)] + [(idx,path,op,2) for idx,(path,op) in enumerate(paths[:30])]
for idx,path,op,seed in schedule:
    p=path[3:]
    for br in ('z','p') if op.endswith('.decnz') else ('-',):
        vals=[seed]*9+[0]
        r=REG[op.split('.')[1]] if op.endswith(('.inc','.decnz')) else None
        if br=='p': vals[r]=max(1,seed)
        if br=='z': vals[r]=0
        targetvals=list(vals)
        if op.endswith('.inc'):
            targetvals[r]+=1;p2=inc(p)
        elif op.endswith('.decnz'):
            if br=='p':targetvals[r]-=1;targetvals.append(0);p2=inc(p)
            else:p2=inc(strip('0',1,p))
        elif op.startswith('_break'):p2=inc(strip('0',int(op.split('.')[1]),p))
        elif op.startswith('_continue'):p2=strip('1',int(op.split('.')[1]),p)
        else:p2=''
        ovf=p2 is None
        expected=frame('' if ovf else p2,targetvals,40+ovf,-int(ovf))
        tape=frame(p,vals);q=96;h=0
        for t in range(10000):
            if t and ((op=='halt' and q==254) or (op!='halt' and q==96 and h==-int(ovf) and tape==expected)):
                break
            bit=int(h in tape);key=(q,bit)
            assert key in T,(idx,br,t,key)
            if key not in covered:
                covered[key]={'site':idx,'path':p,'operation':op,'branch':br,'physical_registers':vals,'step':t,'state':q,'read':bit,'head':h}
            w,d,q=T[key]
            if w:tape.add(h)
            else:tape.discard(h)
            h+=d
        else:raise RuntimeError(('fuel',idx,br))
        checks+=1;total+=t;maximum=max(maximum,t)
    if idx%500==0:print('site',idx,'rows',len(covered),flush=True)
assert set(covered)==set(T),(len(covered),set(T)-set(covered))
result={'working_states':252,'rows':504,'prepared_gap':40,'cases_checked':checks,'literal_steps':total,'maximum_steps':maximum,'source_machine_sha256':hashlib.sha256((ROOT/'machine/zfc_254.tm').read_bytes()).hexdigest(),'runtime_delta':{'delete':[5,8],'rows':[[3,0,0,'L',48],[49,1,0,'R',64]]},'scope':'Every row has a concrete prepared-instruction witness. These are not blank-run reachability witnesses. This finite Python check is not kernel verification.','witnesses':[covered[k] for k in sorted(covered)]}
(ROOT/'row_coverage.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:v for k,v in result.items() if k!='witnesses'})
