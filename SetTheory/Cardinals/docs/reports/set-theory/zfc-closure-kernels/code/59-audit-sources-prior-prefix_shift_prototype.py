#!/usr/bin/env python3
"""Reconstruct the frozen 250-state table and run literal instruction examples.

The mathematical proof is in prefix_carry_lemmas.tex. These bounded literal
examples are regression checks, not a proof of the universal runtime theorem.
"""
from pathlib import Path
import json,re,sys,hashlib,time,random

HERE=Path(__file__).resolve().parent
BASE=HERE/'baseline252.tm'
PROG=HERE.parent/'busy-beaver/ZF/m254/coq/tm/Prog254.v'
PHYS=(6,2,0,4,3,7,8,5,1)

def read(path):
    T={}
    for l in path.read_text().splitlines():
        if not l or l.startswith('#'):continue
        q,b,w,d,t=l.split();T[int(q),int(b)]=(int(w),d,int(t))
    return T

def build(pulse=True):
    assert hashlib.sha256(BASE.read_bytes()).hexdigest()=='939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
    T=read(BASE)
    T={k:(w,d,95 if t==43 else t) for k,(w,d,t) in T.items() if k[0] not in (43,59,85)}
    T[109,0]=(0,'R',75)
    T[75,0]=(0,'R',255)
    T[75,1]=(1,'L',63)
    T[255,0]=(1,'L',112)
    T[255,1]=(1,'L',97)
    T[131,0]=(0,'L',48)
    T[97,1]=(1,'R',97) # Never used in the new recurrent contract.
    if pulse:
        # The temporary bit written at 75 distinguishes the runtime return
        # into 97 from the all-zero blank start at that same state.
        T[75,0]=(1,'R',255)
        T[255,0]=(1,'L',97)
        T[255,1]=(1,'L',131)
        T[97,1]=(1,'L',131)
        T[97,0]=(1,'R',83)
    assert len(T)==500
    assert all(t==254 or (t,0) in T for w,d,t in T.values())
    return T

def encode(T,start=97):
    return '#! start %d\n'%start+''.join('%s %s %s %s %s\n'%(q,b,w,d,t) for (q,b),(w,d,t) in sorted(T.items()))

def inc(p):
    if '0' not in p:return None
    return p[:p.rindex('0')]+'1'

def strip(p,b,k):
    while p and k:
        k-=p[-1]==b;p=p[:-1]
    return p

def sites():
    local=HERE/'instruction-sites.json'
    if local.exists():
        assert hashlib.sha256(local.read_bytes()).hexdigest()=='dc6853f57bc48b834c2a635a82dfad8e344dd324ca11ef8e70ae2f36d66be357'
        out=json.loads(local.read_text())
        assert len(out)==6460
        return out
    text=PROG.read_text().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',text)
    out=[]
    def visit(n,p):
        for b,e in enumerate(nodes[n]):
            kind,*arg=e.split();r=int(arg[0]) if arg else None
            if kind=='CN':visit(r,p+str(b))
            else:out.append((p+str(b),kind,PHYS[r] if kind in ('CI','CD') else r))
    visit(0,'')
    assert len(out)==6460
    return out

def paint(pc,gap,vs,head=0):
    ones={head-1,head+gap}|{head+i for i,b in enumerate(pc) if b=='1'}
    c=head+gap+1
    for v in vs:
        c+=1;ones.update(range(c,c+v+1));c+=v+1
    return ones

def parseframe(q,h,ones,p,gap,regs):
    if q!=96:return None
    # Permit arbitrary valid spare suffix. All other cells exact.
    expected=paint(p or '',gap,regs,h)
    limit=h+gap+1+sum(v+2 for v in regs)
    if {i for i in ones if i<limit}!=expected:return None
    c=limit;end=max(ones);spare=[]
    while c<=end:
        if c in ones or c+1 not in ones:return None
        c+=1;v=0
        while c in ones:v+=1;c+=1
        spare.append(v-1)
    return spare

def case(T,p,op,r,zero,vs,spare,gap=40,fuel=100000,debug=False):
    regs=vs.copy()
    if op=='CD':regs[r]=0 if zero else max(1,regs[r])
    ones=paint(p,gap,regs+spare);original=ones.copy()
    if op=='CI' or op=='CD' and not zero:succ=inc(p)
    elif op=='CD':succ=inc(strip(p,'0',1))
    elif op=='CB':succ=inc(strip(p,'0',r))
    elif op=='CC':succ=strip(p,'1',r)
    else:succ=''
    want=regs.copy()
    if op=='CI':want[r]+=1
    if op=='CD' and not zero:want[r]-=1
    wantgap=gap+(op=='CD' and not zero)+(succ is None)
    q=96;h=0
    trace=[];visits=[]
    for tick in range(fuel):
        if q==254:return (op=='CH'),dict(ticks=tick,outcome='halt',trace=trace[-100:])
        if q==96 and tick:
            visits.append((tick,h,sorted(ones)))
            s=parseframe(q,h,ones,succ,wantgap,want)
            if s is not None:
                return True,dict(ticks=tick,gap=wantgap,spares=s,visits=len(visits))
        b=int(h in ones)
        if debug:trace.append((tick,q,h,b))
        if (q,b) not in T:return False,dict(outcome='missing',state=q,head=h,trace=trace[-100:])
        w,d,q=T[q,b]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    return False,dict(outcome='fuel',state=q,head=h,initial=sorted(original),final=sorted(ones),succ=succ,wantgap=wantgap,want=want,visits=visits[:10],trace=trace[-100:])

def main():
    T=build();(HERE/'zfc_prefix250_old.tm').write_text(encode(T))
    states=[97]+sorted({q for q,b in T}-{97})
    relabel={q:i for i,q in enumerate(states)};relabel[254]=250
    canonical={(relabel[q],b):(w,d,relabel[t]) for (q,b),(w,d,t) in T.items()}
    (HERE/'zfc_prefix250.tm').write_text(encode(canonical,0))
    (HERE/'prefix250-renumbering.json').write_text(json.dumps(dict(start_old=97,halt_old=254,halt_canonical=250,canonical_to_old=states,old_to_canonical=relabel),indent=2)+'\n')
    ss=sites();rows=[];began=time.monotonic()
    for i,(p,op,r) in enumerate(ss):
        for zero in (True,False) if op=='CD' else (None,):
            ok,result=case(T,p,op,r,zero,[0]*9,[0,1],fuel=20000)
            rows.append(dict(site=i,path=p,operation=op,register=r,zero=zero,ok=ok,**result))
            if not ok:
                ok,result=case(T,p,op,r,zero,[0]*9,[0,1],fuel=2000,debug=True)
                print(json.dumps(dict(site=i,path=p,operation=op,register=r,zero=zero,ok=ok,**result),indent=2))
                (HERE/'prototype-failure.json').write_text(json.dumps(rows[-1],indent=2))
                raise SystemExit(1)
    out=dict(passed=len(rows),elapsed=time.monotonic()-began,max_ticks=max(x['ticks'] for x in rows),
             scope='Finite literal instruction examples: gap40, primary0 except positive decrement selected1, spares[0,1].',
             table_sha256=hashlib.sha256(encode(T).encode()).hexdigest())
    print(json.dumps(out,indent=2));(HERE/'prototype-results.json').write_text(json.dumps(out,indent=2))

if __name__=='__main__':main()
