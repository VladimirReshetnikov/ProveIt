#!/usr/bin/env python3
"""Canonical single-witness size-indexed quartics over the frozen eager kernel.
Own standard-library implementation; imports only this packet's core checker.
"""
from pathlib import Path
from copy import deepcopy
import json
import hashlib
from tree_kernel import Evaluation, Exhausted, RepeatedActiveCall, F, Circuit, finalize_row, polynomial, valid_domain


def canonical_certificate(ev, root):
    needed=set()
    def visit(k):
        if k in needed:return
        needed.add(k)
        for p in ev.records[k]['premises']:visit(p)
    visit(root)
    keys=[root]+sorted(needed-{root},key=lambda p:F(*p))
    indices={k:i for i,k in enumerate(keys)};N=len(keys)
    rows=[finalize_row(ev.records[k],indices,N) for k in keys]
    # The evaluator's unused decomposition fields are zero; state this explicitly.
    for r in rows:
        t=r['t'].index(1)
        for field,active in [('a',{1,3,4}),('b',{2,3,4}),('c',{4}),('u',{3,4}),('v',{3})]:
            assert t in active or r[field]==0
    kappa=[F(*k) for k in keys]
    multiplicities=[0]*N;multiplicities[0]=1
    for key in sorted(keys,key=lambda p:ev.records[p]['h'],reverse=True):
        i=indices[key]
        for p in ev.records[key]['premises']:
            multiplicities[indices[p]]+=multiplicities[i]
    assert all(m>=1 for m in multiplicities)
    return dict(rows=rows,kappa=kappa,flow_slack=[m-1 for m in multiplicities],
                distinct_slack=[(kappa[i]-kappa[0])**2-1 for i in range(1,N)],
                order_slack=[kappa[i+1]-kappa[i]-1 for i in range(1,N-1)])


def canonical_domain(cert,p,n,o):
    if type(cert) is not dict or set(cert)!=set(['rows','kappa','flow_slack','distinct_slack','order_slack']):return False
    if not valid_domain(cert['rows'],p,n,o):return False
    N=len(cert['rows'])
    for name,size in [('kappa',N),('flow_slack',N),('distinct_slack',N-1),('order_slack',max(N-2,0))]:
        v=cert[name]
        if type(v) is not list or len(v)!=size or any(type(x) is not int or x<0 for x in v):return False
    return True


def canonical_polynomial(cert,p,n,o):
    if not canonical_domain(cert,p,n,o):raise ValueError('malformed natural canonical certificate')
    rows=cert['rows'];N=len(rows);gap=max(N-2,0)
    core=polynomial(rows,p,n,o);C=Circuit();rs=[]
    keys=[C.var(x) for x in cert['kappa']]
    m=[C.var(x)+1 for x in cert['flow_slack']]
    D=[C.var(x) for x in cert['distinct_slack']]
    G=[C.var(x) for x in cert['order_slack']]
    lifted=[{k:C.var(r[k]) for k in ['x','y','a','b','c','u','v']} for r in rows]
    tags=[[C.var(x) for x in r['t']] for r in rows]
    ptr=[[[C.var(x) for x in slot] for slot in r['pointers']] for r in rows]
    def pair(a,b):
        s=a+b
        return s*(s+1)+2*b+2
    for i,r in enumerate(lifted):rs.append(keys[i]-pair(r['x'],r['y']))
    for i in range(1,N):
        diff=keys[i]-keys[0]
        rs.append(diff*diff-1-D[i-1])
    for i in range(1,N-1):rs.append(keys[i+1]-keys[i]-1-G[i-1])
    for i in range(N):
        rs.append(m[i]-int(i==0)-C.sum(m[j]*ptr[j][s][i] for j in range(N) for s in range(3)))
    for i,r in enumerate(lifted):
        t0,t1,t2,t3,t4=tags[i]
        rs.extend([r['a']*(t0+t2),r['b']*(t0+t1),r['c']*(t0+t1+t2+t3),
                   r['u']*(t0+t1+t2),r['v']*(t0+t1+t2+t4)])
    assert len(rs)==8*N-1+gap and max(r.degree for r in rs)==2
    residual_gates=dict(M=C.M,A=C.A)
    # Start at already evaluated P_N; one addition per extra residual square.
    value=C.var(core['value']);value.degree=4
    for r in rs:value=value+r*r
    M=core['polynomial_gates']['M']+C.M;A=core['polynomial_gates']['A']+C.A
    assert M==15*N*N+72*N+1+gap
    assert A==18*N*N+97*N+1+4*gap
    assert residual_gates==dict(M=3*N*N+8*N-1,A=3*N*N+20*N-3+3*gap)
    return dict(value=value.value,degree_bound=value.degree,
                witnesses=3*N*N+22*N-1+gap,residual_count=31*N+2+gap,
                polynomial_gates=dict(M=M,A=A),
                core_residuals=core['residuals'],extra_residuals=[r.value for r in rs])


def all_coordinates(cert):
    for i,r in enumerate(cert['rows']):
        for k,v in r.items():
            if k=='t':
                for j in range(5):yield ('rows',i,k,j)
            elif k=='pointers':
                for j in range(3):
                    for h in range(len(r[k][j])):yield ('rows',i,k,j,h)
            else:yield ('rows',i,k)
    for k in ['kappa','flow_slack','distinct_slack','order_slack']:
        for i in range(len(cert[k])):yield(k,i)


def main():
    trials=checked=cycles=exhausted=0;maxN=0
    for x in range(32):
        for y in range(24):
            trials+=1;ev=Evaluation(budget=250,max_bits=4096)
            try:z=ev.app(x,y)
            except RepeatedActiveCall:cycles+=1;continue
            except (Exhausted,RecursionError):exhausted+=1;continue
            c=canonical_certificate(ev,(x,y));r=canonical_polynomial(c,x,y,z)
            assert r['value']==0
            maxN=max(maxN,len(c['rows']));checked+=1
            # A reused evaluator may contain unrelated successful calls. They must be omitted.
            before=c;ev.app(0,12345)
            assert canonical_certificate(ev,(x,y))==before
    ev=Evaluation();ev.app(10,10)
    example=canonical_certificate(ev,(10,10));result=canonical_polynomial(example,10,10,10)
    # Mutating every single witness coordinate must leave the unique fiber.
    mutations=0
    for path in all_coordinates(example):
        changed=deepcopy(example);a=changed
        for part in path[:-1]:a=a[part]
        old=a[path[-1]]
        for v in [old+1]+([old-1] if old else []):
            a[path[-1]]=v
            assert canonical_polynomial(changed,10,10,10)['value']!=0
            mutations+=1
        a[path[-1]]=old
    # Canonical rows and complete local data are invariant under evaluator record order.
    ev.records=dict(reversed(list(ev.records.items())))
    assert canonical_certificate(ev,(10,10))==example
    # Exact N=1 boundary case and nontrivial repeated-premise flow.
    leaf=Evaluation();leaf.app(0,0);lc=canonical_certificate(leaf,(0,0));lr=canonical_polynomial(lc,0,0,1)
    assert lr['witnesses']==24 and lr['residual_count']==33
    dup=Evaluation();dup.app(1014,10);dc=canonical_certificate(dup,(1014,10))
    assert canonical_polynomial(dc,1014,10,10)['value']==0
    ii=next(i for i,r in enumerate(dc['rows']) if (r['x'],r['y'])==(10,10))
    assert dc['flow_slack'][ii]+1==3
    # Construct one core-valid but unreachable padding row. Its positive flow fails.
    bad=deepcopy(example);N=len(bad['rows'])
    for r in bad['rows']:
        for p in r['pointers']:p.append(0)
    padding_ev=Evaluation();padding_ev.app(0,12345)
    pr=finalize_row(padding_ev.records[(0,12345)],{},N+1)
    bad['rows'].append(pr);k=F(0,12345)
    assert k>bad['kappa'][-1]
    bad['kappa'].append(k);bad['flow_slack'].append(0)
    bad['distinct_slack'].append((k-bad['kappa'][0])**2-1)
    bad['order_slack'].append(k-bad['kappa'][-2]-1)
    bp=canonical_polynomial(bad,10,10,10)
    assert all(v==0 for v in bp['core_residuals'])
    assert [v for v in bp['extra_residuals'] if v]==[1]
    receipt=dict(status='finite exact checks passed; mathematical uniqueness proof is separate',
                 bounded_pair_trials=trials,complete_canonical_zeros=checked,detected_cycles=cycles,
                 budget_or_size_inconclusive=exhausted,largest_test_D=maxN,
                 identity_example={k:v for k,v in result.items() if not k.endswith('residuals')},
                 N1_example={k:v for k,v in lr.items() if not k.endswith('residuals')},
                 single_coordinate_mutations_rejected=mutations,unreachable_padding_sos=bp['value'],
                 duplicate_premise_occurrences=dc['flow_slack'][ii]+1,
                 script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    here=Path(__file__).resolve().parent
    (here/'canonical_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (here/'canonical_identity.json').write_text(json.dumps(dict(p=10,n=10,o=10,certificate=example),indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
