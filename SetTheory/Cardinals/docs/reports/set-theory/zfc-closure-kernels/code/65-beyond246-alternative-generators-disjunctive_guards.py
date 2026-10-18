#!/usr/bin/env python3
"""Finite relational guard analysis: sets of complete abstract register vectors."""
from pathlib import Path
from collections import deque,Counter
import json,time,itertools,zlib,sys
import reachable_guards as r
HERE=Path(__file__).resolve().parent

def analyze(arity,output):
    width=arity**9;powers=[arity**i for i in range(9)]
    # Constant categories: 0, positive (arity2); 0,1,>=2 (arity3).
    root=r.decode('');vals=[0]*len(r.SITES);pending=[0]*len(vals)
    initial=sum((arity-1)*powers[i] for i in (0,4))
    vals[root]=pending[root]=1<<initial
    queue=deque([root]);queued={root};seen=updates=0;began=time.monotonic()
    def transfer(p,op,k,zero):
        if op not in ('CI','CD'):return (p,)
        value=(p//powers[k])%arity
        if op=='CI':
            return (p+(int(value<arity-1))*powers[k],)
        if zero:return (p,) if value==0 else ()
        if value==0:return ()
        if value==arity-1:return p-powers[k],p
        return (p-powers[k],)
    while queue:
        i=queue.popleft();queued.remove(i);bits=pending[i];pending[i]=0
        pc,op,k=r.SITES[i];updates+=1
        while bits:
            bit=bits&-bits;bits-=bit;p=bit.bit_length()-1;seen+=1
            for zero in ((True,False) if op=='CD' else (None,)):
                j=r.EDGES[i,zero]
                if j is None:continue
                for s in transfer(p,op,k,zero):
                    new=1<<s
                    if not vals[j]&new:
                        vals[j]|=new;pending[j]|=new
                        if j not in queued:queue.append(j);queued.add(j)
        if updates%100000==0:print('progress',arity,updates,seen,len(queue),time.monotonic()-began,flush=True)
    rejected=[];allowed=[]
    for i,(pc,op,k) in enumerate(r.SITES):
        for zero in ((True,False) if op=='CD' else (None,)):
            bits=vals[i];anyallowed=False;j=r.EDGES[i,zero]
            while bits:
                bit=bits&-bits;bits-=bit;p=bit.bit_length()-1
                for s in transfer(p,op,k,zero):
                    anyallowed=True
                    if j is not None:assert vals[j]&(1<<s)
            (allowed if anyallowed else rejected).append([pc,op,k,zero])
    assert vals[root]&(1<<initial)
    print('RESULT',arity,'allowed',len(allowed),'rejected',len(rejected),'seen',seen,'seconds',time.monotonic()-began,flush=True)
    out=dict(status='PASS',arity=arity,initial_abstract_vector=[arity-1 if i in (0,4) else 0 for i in range(9)],
        initial_scope='N,D positive (arity2), or N,D>=2 (arity3); all other registers zero; contains actual N=D=3 root',
        domain='complete vectors with categories0,positive' if arity==2 else 'complete vectors with categories0,1,>=2',
        reachable_site_vectors=seen,reachable_sites=sum(bool(v) for v in vals),allowed_cases=len(allowed),rejected_cases=len(rejected),
        rejected=rejected,seconds=time.monotonic()-began,iterations=updates)
    r.write_json(output/f'disjunctive-guards-{arity}.json',out)
    packed=b''.join(v.to_bytes((width+7)//8,'little') for v in vals)
    with (output/f'disjunctive-invariant-{arity}.zlib').open('xb') as f:f.write(zlib.compress(packed,9))
    return out

def main():
    parser=r.arguments(__doc__)
    parser.add_argument('--arity',type=int,choices=(2,3),nargs='+',default=[3],
        help='Number of value categories; default 3 reproduces the supplied certificate.')
    args=parser.parse_args();arities=list(dict.fromkeys(args.arity))
    names=[f'disjunctive-{kind}-{arity}.{suffix}' for arity in arities
        for kind,suffix in [('guards','json'),('invariant','zlib')]]
    output=r.prepare_output(args,parser,names)
    if output is None:return
    for arity in arities:print(json.dumps(analyze(arity,output),indent=2),flush=True)

if __name__=='__main__':main()
