#!/usr/bin/env python3
"""Derive conservative source windows plus exact blank-startup windows.

Adapted from the supplied PA196 source_contexts.py. Uses the inherited
symbolic arithmetic-box contracts. The input is an exact source graph and
table supplied by its packet; this is a search precondition, not a new
proof-assistant endpoint. Self-loop and box controls use the coarse closure.
"""
import argparse,hashlib,importlib.util,json,sys,time
from pathlib import Path
from collections import defaultdict,deque
from functools import lru_cache


def read_table(p):
    out={}
    for line in p.read_text().splitlines():
        if not line.strip() or line.startswith('#'):continue
        q,b,w,d,n=line.split();out[int(q),int(b)]=(int(w),d=='R',int(n))
    return out


def closure(rows,R):
    mask=(1<<(2*R+1))-1;mid=1<<R
    todo=deque([(0,0)]);seen={(0,0)};ctx=defaultdict(set)
    while todo:
        q,a=todo.popleft();b=(a>>R)&1;ctx[q,b].add(a)
        w,d,n=rows[q,b];a=a|mid if w else a&~mid
        if n==194:continue
        for newbit in (0,1):
            z=(a>>1)|(newbit<<(2*R)) if d else ((a<<1)&mask)|newbit
            if (n,z) not in seen:seen.add((n,z));todo.append((n,z))
    return ctx,len(seen)


@lru_cache(None)
def prefixes(atoms,n):
    if not n:return frozenset({()})
    if not atoms:return frozenset({(0,)*n})
    x,*tail=atoms;tail=tuple(tail)
    if x[0]=='b':return frozenset((x[1],)+r for r in prefixes(tail,n-1))
    if x[0]=='x':return frozenset(tuple((w>>j)&1 for j in range(n)) for w in range(1<<n))
    _,bit,a,c=x
    counts=[min(c,n)] if not a else range(min(c,n),n+1)
    return frozenset((bit,)*k+r for k in counts for r in prefixes(tail,n-k))


def main():
    p=argparse.ArgumentParser();p.add_argument('--machine-dir',type=Path,required=True)
    p.add_argument('--runtime',type=Path,required=True);p.add_argument('--radius',type=int,default=4)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--physical',default='6,2,0,4,3,7,8,5,1')
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);begin=time.monotonic();R=a.radius
    spec=importlib.util.spec_from_file_location('symbolic_runtime_search',a.runtime);s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
    sites=json.loads((a.machine_dir/'sites.json').read_text());ins=json.loads((a.machine_dir/'instructions.json').read_text())
    paths=[tuple(map(int,x[0])) for x in sites];physical=list(map(int,a.physical.split(',')))
    rows=read_table(a.machine_dir/'machine.native.tm');dense=read_table(a.machine_dir/'machine.tm')
    labels=json.loads((a.machine_dir/'labels.json').read_text());inv={q:i for i,q in enumerate(labels)}
    assert inv[74]==0 and inv[254]==194 and len(rows)==388
    assert all(dense[inv[q],b]==(w,d,inv[n]) for (q,b),(w,d,n) in rows.items())
    contracts=[]
    for i,code in enumerate(ins):
        st=s.frame(paths[i]);op=code[0]
        if op=='inc':
            _,r,n=code;contracts.append((i,None,st,s.canonical(s.frame(paths[n],0,('x','inc',physical[r])))))
        elif op=='dec':
            _,r,z,n=code
            contracts.append((i,(physical[r],True),st,s.canonical(s.frame(paths[z]))))
            contracts.append((i,(physical[r],False),st,s.canonical(s.frame(paths[n],1,('x','dec',physical[r])))))
        elif op=='jump':contracts.append((i,None,st,s.canonical(s.frame(paths[code[1]]))))
        elif op=='halt':contracts.append((i,None,st,None))
        else:raise ValueError(code)
    protected=set(s.BOXSTATES)|{q for (q,b),(w,d,n) in rows.items() if q==n}
    ctx=defaultdict(set)
    seen_symbolic=set()
    def visit(st):
        q,on,l,r=st
        if q in protected or on or not r or r[0][0]=='r':return
        # Literal bit steps are the only non-box transitions, except a
        # read-zero/left step at an opaque file boundary, conservatively
        # included by expanding the opaque atom to all local bit words.
        key=(q,l,r)
        if key in seen_symbolic:return
        seen_symbolic.add(key)
        for left in prefixes(tuple(l),R):
            for right in prefixes(tuple(r),R+1):
                bits=left[::-1]+right;mask=sum(b<<j for j,b in enumerate(bits))
                ctx[inv[q],right[0]].add(mask)
    validation=s.validate(rows,contracts,observe=visit);assert validation['ok'],validation
    full,full_count=closure(dense,R)
    for key,words in full.items():
        if labels[key[0]] in protected:ctx[key].update(words)
    expected={-3,46}|{-2+i for i,b in enumerate(paths[25]) if b}
    file=[0]*9;file[physical[0]]=2;file += [1]*26
    x=47
    for value in file:
        x+=1;expected.update(range(x,x+value+1));x+=value+1
    ones=set();q=0;head=0;steps=0
    while not(q==inv[84] and head==-2 and ones==expected):
        assert q!=194 and steps<100000,'did not reach exact startup frame'
        bits=[int(head+j in ones) for j in range(-R,R+1)]
        ctx[q,bits[R]].add(sum(b<<i for i,b in enumerate(bits)))
        w,d,q=dense[q,bits[R]];(ones.add if w else ones.discard)(head);head+=1 if d else -1;steps+=1
    # Intersecting with a second sound invariant preserves overapproximation
    # and avoids counting impossible combinations introduced by opaque atoms.
    ctx={key:words & full[key] for key,words in ctx.items()}
    count=sum(map(len,ctx.values()))
    out=dict(radius=R,source_sites=len(ins),source_contracts=validation,startup_steps=steps,
       source_context_count=count,coarse_context_count=full_count,protected_native_states=sorted(protected),
       machine_sha256=hashlib.sha256((a.machine_dir/'machine.tm').read_bytes()).hexdigest(),
       runtime_sha256=hashlib.sha256(a.runtime.read_bytes()).hexdigest(),seconds=time.monotonic()-begin,
       contexts={f'{q},{b}':sorted(ctx.get((q,b),set())) for q in range(194) for b in (0,1)})
    (a.output/'contexts.json').write_text(json.dumps(out,indent=2)+'\n')
    with (a.output/'contexts.txt').open('w') as f:
        f.write(str(R)+'\n')
        for key,words in out['contexts'].items():
            q,b=key.split(',');f.write(f'{q} {b} {len(words)} '+' '.join(map(str,words))+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='contexts'},indent=2),flush=True)


if __name__=='__main__':main()
