"""Sound interval abstraction of the exact expanded register source.

The finite lattice contains lower endpoints0..CAP and upper endpoints0..CAP
or infinity. Every output certificate is checked afresh for seed inclusion
and closure under every feasible guarded source step.
"""
from pathlib import Path
from collections import deque
import argparse,json,hashlib

def main():
    a=argparse.ArgumentParser();a.add_argument('sites',type=Path);a.add_argument('--cap',type=int,default=3);a.add_argument('--output',type=Path,required=True);arg=a.parse_args()
    ss=json.loads(arg.sites.read_text());leaf={x[0]:i for i,x in enumerate(ss)};cap=arg.cap;inf=cap+1
    prefixes={p[:i] for p in leaf for i in range(len(p))}
    assert len(leaf)==len(ss) and len(prefixes)==len(leaf)-1 and not prefixes.intersection(leaf)
    assert all(p+b in prefixes or p+b in leaf for p in prefixes for b in '01')
    def contract(p):
        assert p in prefixes or p in leaf,p
        while p not in leaf:p+='0'
        return leaf[p]
    def inc(p):return p[:p.rindex('0')]+'1' if '0' in p else ''
    def strip(p,b,k):
        while k and p:k-=p[-1]==b;p=p[:-1]
        return p
    edges=[]
    for p,o,r in ss:
        if o=='CH':edges.append([])
        elif o=='CI':edges.append([('inc',contract(inc(p)))])
        elif o=='CD':edges.append([('zero',contract(inc(strip(p,'0',1)))),('positive',contract(inc(p)))])
        elif o=='CB':edges.append([('control',contract(inc(strip(p,'0',r))))])
        else:assert o=='CC';edges.append([('control',contract(strip(p,'1',r)))])
    def transfer(box,o,r,guard):
        if box is None:return None
        b=list(box)
        if o=='CI':
            l,h=b[r];b[r]=(min(l+1,cap),h+1 if h<cap else inf)
        elif o=='CD':
            l,h=b[r]
            if guard=='zero':
                if l>0:return None
                b[r]=(0,0)
            else:
                if h==0:return None
                b[r]=(max(l,1)-1,h-1 if h<inf else inf)
        return tuple(b)
    def join(a,b):
        if a is None:return b
        if b is None:return a
        return tuple((min(x[0],y[0]),max(x[1],y[1])) for x,y in zip(a,b))
    seed=(3,0,0,0,3,0,0,0,0);initial=tuple((min(n,cap),n if n<=cap else inf) for n in seed)
    values=[None]*len(ss);root=contract('');values[root]=initial;todo=deque([root]);pending={root};updates=0
    while todo:
        i=todo.popleft();pending.remove(i);p,o,r=ss[i]
        for guard,j in edges[i]:
            out=transfer(values[i],o,r,guard);merged=join(values[j],out)
            if merged!=values[j]:
                values[j]=merged;updates+=1
                if j not in pending:pending.add(j);todo.append(j)
    assert join(values[root],initial)==values[root]
    excluded=[];admitted=0;facts=0
    for i,(p,o,r) in enumerate(ss):
        if values[i] is not None:facts+=sum(x!=(0,inf) for x in values[i])
        if o=='CH':
            if values[i] is None:excluded.append([i,False])
            else:admitted+=1
        for guard,j in edges[i]:
            out=transfer(values[i],o,r,guard)
            if out is None:excluded.append([i,guard=='positive'])
            else:
                assert join(values[j],out)==values[j],(i,guard,j)
                admitted+=1
    arg.output.mkdir(parents=True,exist_ok=True)
    rows=[]
    for i,(p,o,r) in enumerate(ss):
        if values[i] is None:continue
        for positive in ([False,True] if o=='CD' else [False]):
            if o=='CD':
                lo,hi=values[i][r]
                if (positive and hi==0) or (not positive and lo>0):continue
            rows.append(f'{p} {o} {r if r is not None else -1} {int(positive)} '+' '.join(f'{lo} {hi if hi<inf else -1}' for lo,hi in values[i])+'\n')
    (arg.output/'guarded_sites.txt').write_text(''.join(rows))
    payload={'status':'CHECKED_SEED_AND_GUARDED_CLOSURE','source_sha256':hashlib.sha256(arg.sites.read_bytes()).hexdigest(),'cap':cap,'infinity_code':inf,'initial_seed':seed,'root':root,'sites':len(ss),'updates':updates,'admitted_guards':admitted,'excluded_guards':excluded,'unreachable_sites':[i for i,x in enumerate(values) if x is None],'nontrivial_interval_facts':facts,'invariants':values}
    (arg.output/'certificate.json').write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps({k:v for k,v in payload.items() if k!='invariants'},indent=2))

if __name__=='__main__':main()
