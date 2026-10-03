#!/usr/bin/env python3
"""Preferred canonical quartic: positive reachability makes root-distinctness redundant."""
from pathlib import Path
from copy import deepcopy
import json
import hashlib
from tree_kernel import Evaluation, Exhausted, RepeatedActiveCall, Circuit, polynomial, valid_domain
from canonical import canonical_certificate as baseline_certificate


def canonical_certificate(ev,root):
    b=baseline_certificate(ev,root)
    return dict(rows=b['rows'],kappa=b['kappa'][1:],flow_slack=b['flow_slack'],order_slack=b['order_slack'])


def domain(c,p,n,o):
    if type(c) is not dict or set(c)!=set(['rows','kappa','flow_slack','order_slack']):return False
    if not valid_domain(c['rows'],p,n,o):return False
    N=len(c['rows'])
    for name,size in [('kappa',N-1),('flow_slack',N),('order_slack',max(N-2,0))]:
        if type(c[name]) is not list or len(c[name])!=size or any(type(x) is not int or x<0 for x in c[name]):return False
    return True


def canonical_polynomial(cert,p,n,o):
    if not domain(cert,p,n,o):raise ValueError('malformed natural projected certificate')
    rows=cert['rows'];N=len(rows);gap=max(N-2,0);core=polynomial(rows,p,n,o);C=Circuit();rs=[]
    keys=[C.var(x) for x in cert['kappa']];m=[C.var(x)+1 for x in cert['flow_slack']]
    gaps=[C.var(x) for x in cert['order_slack']]
    lifted=[{k:C.var(r[k]) for k in ['x','y','a','b','c','u','v']} for r in rows]
    tags=[[C.var(x) for x in r['t']] for r in rows]
    ptr=[[[C.var(x) for x in slot] for slot in r['pointers']] for r in rows]
    def pair(a,b):
        s=a+b;return s*(s+1)+2*b+2
    for i in range(1,N):rs.append(keys[i-1]-pair(lifted[i]['x'],lifted[i]['y']))
    for i in range(gap):rs.append(keys[i+1]-keys[i]-1-gaps[i])
    for i in range(N):rs.append(m[i]-int(i==0)-C.sum(m[j]*ptr[j][s][i] for j in range(N) for s in range(3)))
    for i,r in enumerate(lifted):
        t0,t1,t2,t3,t4=tags[i]
        rs.extend([r['a']*(t0+t2),r['b']*(t0+t1),r['c']*(t0+t1+t2+t3),
                   r['u']*(t0+t1+t2),r['v']*(t0+t1+t2+t4)])
    assert len(rs)==7*N-1+gap and max(r.degree for r in rs)==2
    assert (C.M,C.A)==(3*N*N+7*N-2,3*N*N+17*N-5+3*gap)
    value=C.var(core['value']);value.degree=4
    for r in rs:value=value+r*r
    M=core['polynomial_gates']['M']+C.M;A=core['polynomial_gates']['A']+C.A
    assert (M,A)==(15*N*N+70*N+gap,18*N*N+93*N-1+4*gap)
    return dict(value=value.value,degree_bound=4,witnesses=3*N*N+21*N-1+gap,
                residual_count=30*N+2+gap,polynomial_gates=dict(M=M,A=A),
                core_residuals=core['residuals'],extra_residuals=[r.value for r in rs])


def paths(obj,prefix=()):
    if type(obj) is int:yield prefix
    elif type(obj) is dict:
        for k,v in obj.items():yield from paths(v,prefix+(k,))
    else:
        assert type(obj) is list
        for i,v in enumerate(obj):yield from paths(v,prefix+(i,))


def main():
    count=cycles=0
    for x in range(32):
        for y in range(24):
            ev=Evaluation(budget=250,max_bits=4096)
            try:z=ev.app(x,y)
            except RepeatedActiveCall:cycles+=1;continue
            except (Exhausted,RecursionError):raise AssertionError('unexpected inconclusive test')
            c=canonical_certificate(ev,(x,y));r=canonical_polynomial(c,x,y,z);assert r['value']==0;count+=1
    ev=Evaluation();ev.app(10,10);c=canonical_certificate(ev,(10,10));r=canonical_polynomial(c,10,10,10)
    mutated=0
    for path in paths(c):
        bad=deepcopy(c);obj=bad
        for p in path[:-1]:obj=obj[p]
        original=obj[path[-1]]
        for v in [original+1]+([original-1] if original else []):
            obj[path[-1]]=v;assert canonical_polynomial(bad,10,10,10)['value']!=0;mutated+=1
    ev1=Evaluation();ev1.app(0,0);c1=canonical_certificate(ev1,(0,0));r1=canonical_polynomial(c1,0,0,1)
    assert (r1['witnesses'],r1['residual_count'])==(23,32)
    # Include a core-valid duplicate of the root as a new, unreachable row.
    # It has a legal position in the strict nonroot key ordering; positive flow rejects it.
    from canonical import canonical_polynomial as base_poly
    from tree_kernel import F
    duplicate=deepcopy(c);N=len(duplicate['rows']);root=deepcopy(duplicate['rows'][0])
    for row in duplicate['rows']:
        for p in row['pointers']:p.append(0)
    for p in root['pointers']:p.append(0)
    # Insert duplicate among nonroot rows using a complete index permutation.
    raw=duplicate['rows']+[root];oldkeys=[F(row['x'],row['y']) for row in raw]
    order=[0]+sorted(range(1,N+1),key=lambda i:oldkeys[i]);inv={old:new for new,old in enumerate(order)}
    newrows=[]
    for old in order:
        row=deepcopy(raw[old]);row['pointers']=[[p[j] for j in order] for p in row['pointers']];newrows.append(row)
    k=[oldkeys[i] for i in order[1:]]
    # Recompute path counts from the root, then replace the unreachable zero by one.
    m=[0]*(N+1);m[0]=1
    for i in sorted(range(N+1),key=lambda i:newrows[i]['h'],reverse=True):
        for slot in newrows[i]['pointers']:
            for j,a in enumerate(slot):m[j]+=m[i]*a
    assert m[inv[N]]==0;m[inv[N]]=1
    bad=dict(rows=newrows,kappa=k,flow_slack=[x-1 for x in m],
             order_slack=[k[i+1]-k[i]-1 for i in range(len(k)-1)])
    rr=canonical_polynomial(bad,10,10,10)
    assert all(x==0 for x in rr['core_residuals']) and rr['value']>0
    receipt=dict(status='finite exact projected-canonical checks passed',complete_zeros=count,cycles=cycles,
        identity_example={k:v for k,v in r.items() if not k.endswith('residuals')},
        N1_example={k:v for k,v in r1.items() if not k.endswith('residuals')},
        single_coordinate_mutations_rejected=mutated,duplicate_root_rejected_without_key_test=True,
        duplicate_root_sos=rr['value'],script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    here=Path(__file__).resolve().parent
    (here/'canonical_projected_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (here/'canonical_projected_identity.json').write_text(json.dumps(dict(p=10,n=10,o=10,certificate=c),indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
