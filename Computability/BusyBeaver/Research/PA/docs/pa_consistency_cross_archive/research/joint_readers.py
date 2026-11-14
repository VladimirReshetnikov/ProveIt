#!/usr/bin/env python3
"""Joint allocation screen on the cross-grafted corpus."""
import combine_recent as x
from collections import defaultdict
from pathlib import Path
import json,time
c=x.c;s=x.s

def endpoint(rows,q,p,v):
    tape={-1:p,0:v};pos=0
    for k in range(20):
        if k and pos==1:return q,tape[-1],tape[0]
        if pos not in tape:return None
        a=rows.get((q,tape[pos]))
        if a is None:return None
        w,d,q=a;tape[pos]=w;pos+=1 if d else-1
    return None

def screen(path):
    t=c.read_grammar(path);r,idx,sh=c.build(t)
    shape={q:None for q,b in r if q not in c.BOXSTATES}
    ops=c.opportunities_fast(r,shape)
    if len(ops)>20:return {'file':str(path),'too_many_opportunities':len(ops)}
    ch=s.bestcompatible_all(r,shape);rr,alias=s.apply(r,ch)
    incoming=defaultdict(set)
    for(q,b),(w,d,n)in r.items():
        if d and w==b:incoming[alias.get(n,n)].add(b)
    touched={n for a,b,acts in ch for w,d,n in acts if not d}
    poss=[];tested=[]
    for q in sh:
        if q in alias or q in touched:continue
        ctx=incoming[q]
        if not ctx:continue
        want={(p,v):endpoint(rr,q,p,v)for p in ctx for v in(0,1)}
        if any(z is None for z in want.values()):continue
        for b in {z for z,k in rr if z<1300}:
            if all(endpoint(rr,b,p,v)==z for(p,v),z in want.items()):poss.append((q,b))
    if poss or len(rr)//2<196:
        ss,ins,cs=c.source(t)
        choices=[(None,rr)]+[((q,b),{(z,k):(w,d,b if n==q else n)for(z,k),(w,d,n)in rr.items()if z!=q}) for q,b in poss]
        for key,trial in choices:
            if len(trial)//2>=196:continue
            check=c.validate(trial,cs);st=x.startup(trial,ss)if check['ok']else None
            tested.append({'fold':key,'states':len(trial)//2,'contracts':check,'startup':st})
            if check['ok']and st['ok']:
                x.export(x.ROOT/'research/joint_success',t,trial,ch,ss,tested[-1]);print('ACCEPTED',tested[-1],flush=True)
    return {'file':str(path.relative_to(x.AX)),'opportunities':len(ops),'folds':len(ch),'states':len(rr)//2,'fixed_reuse':poss,'trials':tested}

if __name__=='__main__':
    files=[x.AX/'diagonal196/grammar.json',x.AX/'separate196/grammar.json']+sorted((x.AX/'search/ties').glob('*.json'))+[x.AX/'search/scanner_6.grammar.json']
    rs=[];start=time.time()
    for i,p in enumerate(files):
        r=screen(p);rs.append(r)
        if i%10==0 or r.get('trials'):print(i,json.dumps(r),flush=True)
    (x.ROOT/'research/joint_readers.json').write_text(json.dumps({'seconds':time.time()-start,'grammars':len(rs),'results':rs},indent=2)+'\n')
