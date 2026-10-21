#!/usr/bin/env python3
"""Independent source/refill/credit and literal blank-run audit. Standard library only."""
from pathlib import Path
from math import isqrt
import json,hashlib,argparse

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def cfg(rows):
    # Independently resolve every outward branch by intervals of the full prefix tree.
    index={r[0]:i for i,r in enumerate(rows)}; intervals={}
    def visit(p):
        if p in index:v=(index[p],index[p]+1)
        else:
            l=visit(p+'0');r=visit(p+'1');assert l[1]==r[0];v=l[0],r[1]
        intervals[p]=v;return v
    assert visit('')==(0,len(rows))
    def escape(p,bit,n):
        while p:
            b,p=p[-1],p[:-1]
            if b==bit:
                n-=1
                if n==0:return (intervals[p][1]%len(rows))if bit=='0'else intervals[p][0]
        return 0
    g=[]
    for i,(p,op,a)in enumerate(rows):
        after=(i+1)%len(rows)
        if op=='CI':v=[after]
        elif op=='CD':v=[escape(p,'0',1),after]
        elif op=='CB':v=[escape(p,'0',a)]
        elif op=='CC':v=[escape(p,'1',a)]
        elif op=='CH':v=[]
        else:raise ValueError(op)
        g.append(v)
    return g

def parse_table(p):
    out={}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert(q,b)not in out and b in (0,1)and w in(0,1)and d in('L','R')
        out[q,b]=(w,1 if d=='R'else -1,t)
    assert len(out)==430 and len({q for q,b in out})==215
    return out

def right(n):
    s=(isqrt(8*n+1)-1)//2;return n-s*(s+1)//2

def main():
    p=argparse.ArgumentParser();p.add_argument('--candidate',type=Path,required=True);p.add_argument('--parent',type=Path,required=True);p.add_argument('--startup',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    old=json.loads((a.parent/'sites215.json').read_text());new=json.loads((a.candidate/'source/zc215.sites.json').read_text());go,gn=cfg(old),cfg(new)
    assert len(old)==4751 and len(new)==4752 and new[9][1:]==['CB',1]and gn[9]==[0]
    j=lambda i:i+(i>=9)
    for i,row in enumerate(old):
        assert row[1:]==new[j(i)][1:]
        wanted=[j(x)for x in go[i]]
        if i==7:wanted[0]=9
        assert gn[j(i)]==wanted,(i,go[i],gn[j(i)])
    assert old[7][1:]==['CD',6]
    # Literal two-row table difference from accepted commands120.
    oldT=parse_table(a.parent/'k215.native.tm');newT=parse_table(a.candidate/'machine/zc215.native.tm')
    delta={k:(oldT[k],v)for k,v in newT.items()if oldT[k]!=v}
    assert delta=={(8,1):((1,1,13),(1,1,103)),(198,0):((1,-1,40),(0,-1,40))},delta
    # Independent blank run, and whole frame built directly from the format.
    receipt=json.loads(a.startup.read_text());ones=set();q,h=74,0
    for _ in range(receipt['steps']):
        b=int(h in ones);w,d,q=newT[q,b]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
    assert(q,h)==(84,-4)and receipt['steps']==117004
    assert ones==set(receipt['one_cells'])
    regs=[1,0,5,0,0,0,0,0,0];phys=[None]*9
    for i,k in enumerate((6,2,0,4,3,7,8,5,1)):phys[k]=regs[i]
    expected={h-1,h+64+20};pos=h+64+20+1
    for v in phys+receipt['spares']:
        pos+=1;expected.update(range(pos,pos+v+1));pos+=v+1
    assert expected==ones and receipt['registers']==regs and receipt['gap']==20
    # Exact finite corroboration of the unbounded written credit theorem.
    M=500000;balance=[];minimum=[];commands=[];cumulative=0;global_min=0
    for n in range(M):
        y=right(n);s=(isqrt(8*n+1)-1)//2;tag=s-y
        if tag<2:r=y;cost=1 if tag==0 else -1
        elif tag==2:r=right(y);cost=0
        else:r=right(right(y));cost=10
        ix=r-1 if r else None
        assert ix is None or ix<n
        b=cost+(balance[ix]if ix is not None else 0)
        m=min(0,cost+(minimum[ix]if ix is not None else 0))
        length=1+(commands[ix]if ix is not None else 0)
        assert length<=n+1
        global_min=min(global_min,cumulative+m);cumulative+=b
        assert global_min==0 and cumulative>=0
        balance.append(b);minimum.append(m);commands.append(length)
    out={'status':'INDEPENDENT_CB120_SOURCE_BLANK_CREDIT_PASS','source_sha256':sha(a.candidate/'source/zc215.sites.json'),'table_sha256':sha(a.candidate/'machine/zc215.native.tm'),'source_leaves':len(new),'transported_old_leaves':len(old),'new_CB1_ordinal':9,'new_CB1_target':0,'table_changes':[[q,b,*newT[q,b]]for q,b in sorted(delta)],'blank_steps':receipt['steps'],'blank_state':q,'blank_head':h,'blank_one_cells':len(ones),'logical_seed':regs,'physical_spares':len(receipt['spares']),'credit_corrob_candidate_count':M,'credit_cumulative_balance':cumulative,'credit_prefix_minimum':global_min,'checker_sha256':sha(Path(__file__)),'scope':'Source CFG/refill, literal blank and full-frame audit, and finite corroboration of written all-natural credit proof; separate quantified runtime remains required.'}
    a.out.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must be enabled')
    main()
