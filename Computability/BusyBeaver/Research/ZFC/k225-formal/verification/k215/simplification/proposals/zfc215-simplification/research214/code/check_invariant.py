#!/usr/bin/env python3
"""Independent finite checker of a source-register product invariant.

It does not import the generator or its arithmetic CFG resolver. Source targets
are recovered by independently walking ancestor intervals. No bounded source
execution is used. The proof of the finite abstraction is in README.md.
"""
import argparse,hashlib,json
if not __debug__: raise RuntimeError('Run with assertions enabled, without -O.')
from pathlib import Path

def validate(source,certificate):
    raw=Path(source).read_bytes();rows=json.loads(raw);c=json.loads(Path(certificate).read_text())
    assert hashlib.sha256(raw).hexdigest()==c['source_sha256']
    K=c['cutoff'];I=c['invariants'];assert isinstance(K,int)and 1<=K<=32 and len(I)==len(rows)
    allmask=(1<<(K+1))-1;lookup={p:(i,op,arg)for i,(p,op,arg)in enumerate(rows)}
    assert len(lookup)==len(rows)
    ranges={};order=[]
    def walk(p):
        low=len(order)
        if p in lookup:
            i,o,a=lookup[p];assert i==low
            assert o in ['CI','CD','CB','CC','CH']
            assert (a is None if o=='CH'else isinstance(a,int))
            if o in ['CI','CD']:assert 0<=a<9
            if o in ['CB','CC']:assert a>0
            order.append(p)
        else:
            assert any(x.startswith(p)for x in lookup),('missing branch',p)
            walk(p+'0');walk(p+'1')
        ranges[p]=(low,len(order))
    walk('');assert len(order)==len(rows)
    for x in I:
        assert x is None or(len(x)==9 and all(isinstance(m,int)and 0<m<=allmask for m in x))
    def abstract(n):return min(n,K)
    init=[4,0,0,0,0,0,0,0,0]
    assert I[0]is not None and all(I[0][r]>>abstract(n)&1 for r,n in enumerate(init))
    def target(p,bit,k):
        while p:
            last,p=p[-1],p[:-1]
            if last==bit:
                k-=1
                if k==0:return ranges[p][int(bit=='0')]%len(rows)
        return 0
    def post(mask,operation,guard=None):
        # For the infinite atom >=K, K and K+1 realize all abstraction
        # outcomes of both x+1 and x-1. Other atoms are singletons.
        out=0
        for atom in range(K+1):
            if mask>>atom&1:
                for n in([atom]if atom<K else[K,K+1]):
                    if guard is False and n!=0:continue
                    if guard is True and n==0:continue
                    v=n+1 if operation=='CI'else max(n-1,0)if operation=='CD'else n
                    out|=1<<abstract(v)
        return out
    verified_edges=0;dead=[];zero_facts=[]
    def check_edge(i,j,r=None,newmask=None):
        nonlocal verified_edges
        if r is not None and newmask==0:return
        assert I[j]is not None,('reachable successor marked unreachable',i,j)
        for k,m in enumerate(I[i]):
            if k==r:m=newmask
            assert m&~I[j][k]==0,('not inductive',i,j,k,m,I[j][k])
        verified_edges+=1
    for i,(p,o,a)in enumerate(rows):
        if I[i]is None:
            dead.extend([[i,b]for b in([False,True]if o=='CD'else[False])]);continue
        zero_facts.extend([i,r]for r,m in enumerate(I[i])if m==1)
        if o=='CI':check_edge(i,(i+1)%len(rows),a,post(I[i][a],'CI'))
        elif o=='CD':
            for positive,j in [(False,target(p,'0',1)),(True,(i+1)%len(rows))]:
                mask=post(I[i][a],'CD',positive)
                if not mask:dead.append([i,positive])
                else:check_edge(i,j,a,mask)
        elif o=='CB':check_edge(i,target(p,'0',a))
        elif o=='CC':check_edge(i,target(p,'1',a))
    assert dead==c['unreachable_cases']
    return {'status':'INDUCTIVE_INVARIANT_PASS','source_sha256':c['source_sha256'],'cutoff':K,'source_sites':len(rows),'verified_abstract_edges':verified_edges,'unreachable_sites':[i for i,x in enumerate(I)if x is None],'unreachable_guarded_cases':dead,'known_zero_register_facts':len(zero_facts),'scope':'Every source run from ordinal0 and registers[4,0,0,0,0,0,0,0,0]; checked inductive abstraction, not a bounded trace and not a physical machine certificate.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('certificate',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
    result=validate(a.source,a.certificate)
    if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
