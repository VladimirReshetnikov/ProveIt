#!/usr/bin/env python3
"""Collect universal finite windows from the literal affine/list interpreter.

Uses the attributed independent symbolic arithmetic checker. No box oracle.
Run lengths and finite arbitrary-list languages are enumerated up to the window
radius; parameter correlations are forgotten, which is an overapproximation.
All accelerated run interiors are included. Generic one-block lemmas expose
list-traversal interiors. The complete exact startup prefix is added separately.
This is executable mathematical evidence, not a proof-assistant certificate.
"""
from pathlib import Path
import argparse,functools,itertools,json,sys,time
p=argparse.ArgumentParser()
p.add_argument('machine',type=Path);p.add_argument('--checker',type=Path,required=True)
p.add_argument('--radius',type=int,default=6);p.add_argument('--output',type=Path,required=True)
p.add_argument('--startup-steps',type=int,required=True)
a=p.parse_args();sys.path.insert(0,str(a.checker))
import symbolic_runtime as s
import independent_runtime as r
s.HEADER_BASE=48;K=a.radius
mapping={int(k):v for k,v in json.loads((a.checker/'legacy_mapping.json').read_text()).items()}
rows=r.table(a.machine/'machine.native.tm')
states={q for q,b in rows}
for q in states|{254}:mapping.setdefault(q,q+10000)
inverse={v:k for k,v in mapping.items()};assert len(inverse)==len(mapping)
table={(mapping[q],b):(w,d,mapping[n])for (q,b),(w,d,n) in rows.items()}
BOX={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}
patterns={q:set()for q in BOX};observed=set();list_seen=set();window_seen=set();n_observe=0;n_scans=0;n_steps=0;active=False

@functools.lru_cache(maxsize=None)
def list_words(family,rev,k):
    # All prefixes of length k, and every complete word shorter than k,
    # of (01+)^*, (101*)^*, or the reversed languages.
    done={''};front=[''];full=set()
    blocks=[('0'+'1'*(i+1))if family=='B'else('10'+'1'*i) for i in range(k+1)]
    if rev:blocks=[b[::-1]for b in blocks]
    for word in front:
        for block in blocks:
            nxt=word+block
            if len(nxt)>=k:full.add(nxt[:k])
            elif nxt not in done:done.add(nxt);front.append(nxt)
    return tuple(tuple(map(int,x))for x in done),tuple(tuple(map(int,x))for x in full)

def lengths(coeff,k):
    constant=coeff[0];terms=coeff[1:]
    assert min(coeff)>=0
    out={min(constant,k)}
    for c in terms:
        if not c:continue
        for x in tuple(out):
            for n in range((k-x+c-1)//c+1):out.add(min(x+c*n,k))
    return out

@functools.lru_cache(maxsize=300000)
def prefixes(atoms,k):
    if k==0:return ((),)
    assert atoms,'unrepresented tape exterior'
    x,*rest=atoms;rest=tuple(rest)
    if x[0]=='blank':return ((0,)*k,)
    if x[0]=='opaque':return tuple(itertools.product((0,1),repeat=k))
    out=set()
    if x[0]=='run':
        for n in lengths(x[2],k):
            if n>=k:out.add((x[1],)*k)
            else:
                for t in prefixes(rest,k-n):out.add((x[1],)*n+t)
    elif x[0]=='list':
        short,full=list_words(x[1],x[3],k);out.update(full)
        for z in short:
            for t in prefixes(rest,k-len(z)):out.add(z+t)
    else:raise ValueError(x)
    return tuple(out)

def add(q,d,left,right):
    onl=d==-1
    lp=prefixes(tuple(left),K+1 if onl else K)
    rp=prefixes(tuple(right),K if onl else K+1)
    key=(q,d,lp,rp)
    if key in window_seen:return
    window_seen.add(key)
    dest=patterns[inverse[q]]
    for l,rgt in itertools.product(lp,rp):
        w=tuple(reversed(l[1:]))+(l[0],)+rgt if onl else tuple(reversed(l))+rgt
        assert len(w)==2*K+1
        dest.add(sum(b<<i for i,b in enumerate(w)))

def observe(st):
    global n_observe,n_scans
    if inverse[st.q] not in BOX:return
    q,d,left,right=st.key();key=(q,d,tuple(left),tuple(right))
    if key in observed:return
    observed.add(key);n_observe+=1
    add(q,d,left,right)
    src,dst=(right,left)if d==1 else(left,right)
    if not src or src[0][0]!='run':return
    atom=src[0];w,dd,nn=table[q,atom[1]]
    if dd!=d or nn!=q:return
    n_scans+=1
    for length in lengths(atom[2],2*K+1):
        for used in range(length):
            ss=[s.run(atom[1],length-used)]+src[1:]
            tt=[s.run(w,used)]+dst
            add(q,d,tt,ss)if d==1 else add(q,d,ss,tt)

orig=s.State.step
def expand_list(st,lemmas):
    q,d,left,right=st.key()
    src,dst=(right,left)if d==1 else(left,right)
    if not src or src[0][0]!='list':return
    atom=src[0];before=atom[1];after=lemmas[q,d,before,atom[3]]
    key=q,d,tuple(left),tuple(right)
    if key in list_seen:return
    list_seen.add(key)
    # Split an arbitrary traversed list into an already consumed prefix,
    # one arbitrary block, and an unconsumed suffix. Empty prefix/suffix allowed.
    prefix=('list',after,'consumed_prefix',d==1)
    suffix=('list',before,'unconsumed_suffix',d==-1)
    v=s.var(2)
    if d==1:
        a=s.State(q,[prefix]+left,s.block(v,before)+[suffix]+right[1:])
        target=s.State(q,s.rev(s.block(v,after))+[prefix]+left,[suffix]+right[1:])
    else:
        a=s.State(q,s.rev(s.block(v,before))+[suffix]+left[1:],[prefix]+right,-1)
        target=s.State(q,[suffix]+left[1:],s.block(v,after)+[prefix]+right,-1)
    clock=s.ZERO;motion=s.ZERO
    for i in range(50):
        if a.key()==target.key():return
        observe(a)
        clock,motion,event=orig(a,table,{},clock,motion)
    raise AssertionError(('List-interior block did not close',q,d,before,after))

def step(st,table,lemmas,clock,motion):
    global n_steps
    n_steps+=1
    if active:
        observe(st)
        if lemmas:expand_list(st,lemmas)
    return orig(st,table,lemmas,clock,motion)
s.State.step=step
began=time.monotonic()
lemmas,blocks=s.prove_blocks(table)
active=True
names={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
sites=json.loads((a.machine/'sites.json').read_text());contracts=0
for i,(pc,op,arg)in enumerate(sites):
    if not isinstance(pc,str):pc=''.join(map(str,pc))
    for pos in([False,True]if op=='dec'else[False]):
        s.case(table,lemmas,(pc,names[op],arg),pos);contracts+=1
    if(i+1)%200==0:print(json.dumps({'sites':i+1,'contracts':contracts,'symbolic_windows':n_observe,'contexts':sum(map(len,patterns.values())),'seconds':time.monotonic()-began}),flush=True)
# Exact full-tape startup; retain all contexts before the source entry.
q=74;h=0;ones=set()
for i in range(a.startup_steps):
    pp=sum((h+z in ones)<<(z+K)for z in range(-K,K+1))
    if q in BOX:patterns[q].add(pp)
    w,d,q=rows[q,int(h in ones)]
    (ones.add if w else ones.discard)(h);h+=d
assert(q,h)==(84,-2)
missing=sorted(q for q,ps in patterns.items()if not ps)
assert not missing,missing
a.output.parent.mkdir(parents=True,exist_ok=True)
a.output.write_text(''.join(f'{q} {p}\n'for q in sorted(patterns)for p in sorted(patterns[q])))
receipt={'machine':a.machine.name,'radius':K,'source_outcomes':contracts,'literal_symbolic_steps':n_steps,'distinct_symbolic_states':n_observe,'accelerated_scan_states':n_scans,'contexts':sum(map(len,patterns.values())),'state_counts':{str(q):len(ps)for q,ps in sorted(patterns.items())},'startup_steps':a.startup_steps,'list_sweep_lemmas':len(blocks),'list_interiors':len(list_seen),'seconds':time.monotonic()-began,'scope':'Universal literal symbolic source cases, contextual list-sweep interiors, and exact whole-tape startup; affine correlations forgotten; all run interiors included.'}
a.output.with_suffix('.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
