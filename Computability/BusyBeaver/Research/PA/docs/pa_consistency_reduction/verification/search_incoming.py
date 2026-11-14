#!/usr/bin/env python3
"""Eliminate a state by collapsing every incoming transition with its tail."""
import symbolic as S
from pathlib import Path
import json,itertools,time

def actions(m,p,b,patterns,r,forbidden,bound=21):
    common=None
    for orig in patterns:
        t=orig;x=r;s=p;out=set()
        for k in range(bound):
            if x<0 or x>2*r or (s,(t>>x)&1) not in m:break
            w,d,s=m[s,(t>>x)&1]
            t=(t&~(1<<x))|(w<<x);x+=d
            if s!=forbidden and abs(x-r)==1 and ((t^orig)&~(1<<r))==0:
                out.add(((t>>r)&1,x-r,s))
        common=out if common is None else common&out
        if not common:return set()
    return common or set()

def main():
    m=S.load_machine();r=4
    contextpath=Path(__file__).parents[1]/'reduction196/site_contexts.json'
    ctx={int(q):v for q,v in json.loads(contextpath.read_text()).items()}
    states=sorted(set(q for q,b in m))
    protected={q for q,b in S.ENGINE_ROWS}|{0,S.ROOT}
    count=0
    for q in states:
        if q in protected:continue
        incoming=[(p,b) for (p,b),a in m.items() if a[2]==q and p!=q]
        if any(k in S.ENGINE_ROWS for k in incoming):continue
        alternatives=[]
        for p,b in incoming:
            patterns=[t for t in ctx[p] if ((t>>r)&1)==b]
            if not patterns:break
            alts=actions(m,p,b,patterns,r,q)
            if not alts:break
            alternatives.append(sorted(alts))
        else:
            print('CANDIDATE',q,incoming,alternatives,flush=True)
            for seq in itertools.product(*alternatives):
                nm={k:a for k,a in m.items() if k[0]!=q}
                nm.update(zip(incoming,seq));count+=1
                try:info,_=S.verify(nm)
                except Exception as e:print('failed',q,str(e),flush=True);continue
                print('SUCCESS',q,seq,info,flush=True)
                Path(__file__).with_name(f'incoming_{q}.tm').write_text(''.join(f'{s} {b} {w} {"R" if d==1 else "L"} {t}\n' for (s,b),(w,d,t) in sorted(nm.items())))
    print('DONE',count,flush=True)

if __name__=='__main__':main()
