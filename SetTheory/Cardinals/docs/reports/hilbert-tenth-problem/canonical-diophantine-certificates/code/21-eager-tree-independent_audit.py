#!/usr/bin/env python3
"""Independent small-step/constraint audit. Uses producer snapshot only to supply candidate certificates."""
import copy, hashlib, importlib.util, json, random
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('candidate',HERE/'tree_kernel.py')
candidate=importlib.util.module_from_spec(spec)
import sys
sys.modules[spec.name]=candidate
spec.loader.exec_module(candidate)

# Encoding inversion by binary search, not the producer's square-root routine.
def pair(a,b): return a*a+2*a*b+b*b+a+3*b+2
def stem(a): return 2*a+1
@lru_cache(None)
def tree(n):
    if n==0: return ()
    if n%2: return (tree(n//2),)
    q=n//2-1
    lo,hi=0,q+1
    while lo+1<hi:
        m=(lo+hi)//2
        if m*(m+1)//2<=q: lo=m
        else: hi=m
    b=q-lo*(lo+1)//2
    a=lo-b
    assert a>=0 and b>=0 and pair(a,b)==n and max(a,b)<n
    return tree(a),tree(b)
def code(t):
    if len(t)==0: return 0
    if len(t)==1: return stem(code(t[0]))
    return pair(code(t[0]),code(t[1]))
@dataclass(frozen=True)
class App:
    f:object
    a:object

def step(e):
    # Literal weak left-to-right CBV context closure on an expression AST.
    if not isinstance(e,App): raise ValueError('already a value')
    if isinstance(e.f,App):
        f,key=step(e.f); return App(f,e.a),key
    if isinstance(e.a,App):
        a,key=step(e.a); return App(e.f,a),key
    f,a=e.f,e.a
    key=(code(f),code(a))
    if len(f)==0: return (a,),key
    if len(f)==1: return (f[0],a),key
    if len(f[0])==0: return f[1],key
    if len(f[0])==1:
        return App(App(f[1],a),App(f[0][0],a)),key
    return App(App(a,f[0][0]),f[0][1]),key

def smallstep(x,y,budget=100000):
    expr=App(tree(x),tree(y)); calls=Counter(); seen=set()
    while isinstance(expr,App):
        if expr in seen: return {'cycle':True,'cost':sum(calls.values())}
        seen.add(expr)
        if len(seen)>budget: return {'inconclusive':True}
        expr,key=step(expr); calls[key]+=1
    return {'z':code(expr),'h':sum(calls.values()),'keys':set(calls),'counts':calls}

FIELDS=['x','y','z','h','a','b','c','u','v','d','e','q','j','k']
def residuals(rows,p,n,o):
    N=len(rows); out=[]
    for i,r in enumerate(rows):
        t=r['t']; A=t[3]+t[4]
        x,y,z,h,a,b,c,u,v,d,e,q,j,k=[r[f] for f in FIELDS]
        out += [sum(t)-1,d-pair(a,b),e-pair(a,y),q-pair(0,b),j-pair(stem(a),b),k-pair(d,c)]
        out += [x-t[1]*stem(a)-t[2]*q-t[3]*j-t[4]*k,t[0]*(z-stem(y)),t[1]*(z-e),t[2]*(z-b)]
        out += [sum(r['pointers'][0])-A,sum(r['pointers'][1])-A,sum(r['pointers'][2])-t[3]]
        target=((t[3]*b+t[4]*y,t[3]*y+t[4]*a,A*u),
                (t[3]*a+t[4]*u,t[3]*y+t[4]*b,t[3]*v+t[4]*z),
                (t[3]*u,t[3]*v,t[3]*z))
        for slot in range(3):
            for col,f in enumerate(('x','y','z')):
                out.append(sum(r['pointers'][slot][j]*rows[j][f] for j in range(N))-target[slot][col])
        out.append(h-1-sum(r['pointers'][slot][j]*rows[j]['h'] for slot in range(3) for j in range(N)))
    out += [rows[0]['x']-p,rows[0]['y']-n,rows[0]['z']-o]
    return out

def check(rows,p,n,o):
    N=len(rows)
    if not N:return False
    for r in rows:
        if set(r)!=set(FIELDS+['t','pointers']):return False
        if len(r['t'])!=5 or len(r['pointers'])!=3 or any(len(a)!=N for a in r['pointers']):return False
        vs=[r[f] for f in FIELDS]+r['t']+sum(r['pointers'],[])
        if any(type(v)!=int or v<0 for v in vs):return False
    if any(type(v)!=int or v<0 for v in (p,n,o)):return False
    return all(r==0 for r in residuals(rows,p,n,o))

def independent_graph_check(rows,p,n,o):
    # Separate semantic checker: recurse through selected edges and re-evaluate the active rule.
    active=set(); memo={}
    def walk(i):
        if i in active: raise AssertionError('cycle')
        if i in memo:return memo[i]
        active.add(i);r=rows[i];f=tree(r['x']);y=r['y']
        idx=[[j for j,v in enumerate(slot) if v] for slot in r['pointers']]
        if len(f)<2 or len(f[0])==0:
            assert all(not x for x in idx)
            z=stem(y) if len(f)==0 else pair(code(f[0]),y) if len(f)==1 else code(f[1]);h=1
        else:
            assert len(idx[0])==len(idx[1])==1
            p1,p2=rows[idx[0][0]],rows[idx[1][0]]
            u,h1=walk(idx[0][0]);v,h2=walk(idx[1][0])
            if len(f[0])==1:
                assert len(idx[2])==1
                p3=rows[idx[2][0]];z,h3=walk(idx[2][0])
                assert (p1['x'],p1['y'])==(code(f[1]),y)
                assert (p2['x'],p2['y'])==(code(f[0][0]),y)
                assert (p3['x'],p3['y'])==(u,v)
                h=1+h1+h2+h3
            else:
                assert not idx[2]
                assert (p1['x'],p1['y'])==(y,code(f[0][0]))
                assert (p2['x'],p2['y'])==(u,code(f[0][1]))
                z=v;h=1+h1+h2
        assert (r['z'],r['h'])==(z,h)
        active.remove(i);memo[i]=(z,h);return memo[i]
    for i in range(len(rows)):walk(i)
    assert rows[0]['x']==p and rows[0]['y']==n and memo[0][0]==o
    return memo

def refresh(r):
    a,b,c,y=r['a'],r['b'],r['c'],r['y']
    r.update(d=pair(a,b),e=pair(a,y),q=pair(0,b),j=pair(stem(a),b),k=pair(pair(a,b),c))

def permutation(rows,perm):
    return [{**copy.deepcopy(rows[i]),'pointers':[[rows[i]['pointers'][s][j] for j in perm] for s in range(3)]} for i in perm]

def main():
    rng=random.Random(20261002); receipt={}
    for n in range(100000):assert code(tree(n))==n
    for _ in range(1000):
        a,b=rng.getrandbits(rng.randrange(1,2049)),rng.getrandbits(rng.randrange(1,2049))
        # Compare constructor inversion with producer on large integers without fully decoding huge trees.
        assert candidate.split(pair(a,b))==(2,a,b)
    receipt['natural_code_roundtrips']=100000;receipt['large_pair_roundtrips']=1000
    tested=cycles=cycle_confirmed=cycle_reference_limited=limited=0;tags=Counter();maxcost=maxrows=0
    for x in range(64):
      for y in range(24):
        ev=candidate.Evaluation(budget=500,max_bits=4096)
        try:z=ev.app(x,y)
        except candidate.RepeatedActiveCall:
            try:ref=smallstep(x,y,budget=2000)
            except RecursionError:ref={'inconclusive':True}
            assert ref.get('cycle') or ref.get('inconclusive'),(x,y,ref)
            cycle_confirmed+=int(bool(ref.get('cycle')))
            cycle_reference_limited+=int(bool(ref.get('inconclusive')))
            cycles+=1;continue
        except (candidate.Exhausted,RecursionError): limited+=1;continue
        rows=candidate.certificate(ev,(x,y))
        assert check(rows,x,y,z)
        independent_graph_check(rows,x,y,z)
        ref=smallstep(x,y)
        assert ref.get('z')==z and ref['h']==rows[0]['h'],(x,y,ref)
        assert ref['keys']=={(r['x'],r['y']) for r in rows}
        for r in rows: tags[r['t'].index(1)]+=1
        tested+=1;maxcost=max(maxcost,ref['h']);maxrows=max(maxrows,len(rows))
        if tested%29==0:
            perm=[0]+rng.sample(list(range(1,len(rows))),len(rows)-1)
            assert check(permutation(rows,perm),x,y,z)
    receipt['bounded_grid']={'pairs':64*24,'terminating_checked':tested,'producer_active_call_cycles':cycles,'independent_repeated_states':cycle_confirmed,'cycle_reference_budget_inconclusive':cycle_reference_limited,'budget_or_size_inconclusive':limited,'max_unfolded_calls':maxcost,'max_rows':maxrows,'all_five_tags':dict(tags)}
    ident=json.loads((HERE/'identity_certificate.json').read_text());rs=ident['rows']
    assert check(rs,10,10,10) and smallstep(10,10)['h']==4
    attempted=rejected=accepted=0;free=[]
    for i,r in enumerate(rs):
      coords=[(f,None,None) for f in FIELDS]+[('t',j,None) for j in range(5)]+[('pointers',s,j) for s in range(3) for j in range(len(rs))]
      for f,a,b in coords:
        changed=copy.deepcopy(rs)
        if a is None:changed[i][f]+=1
        elif b is None:changed[i][f][a]+=1
        else:changed[i][f][a][b]+=1
        attempted+=1
        if check(changed,10,10,10):
            independent_graph_check(changed,10,10,10);accepted+=1;free.append([i,f,a,b])
        else: rejected+=1
    receipt['single_coordinate_plus_one']={'attempted':attempted,'rejected':rejected,'accepted_semantically_inactive':accepted,'accepted_coordinates':free}
    # Natural domain is mandatory; booleans, floats and negative values fail.
    for bad in (True,1.0,-1):
        rr=copy.deepcopy(rs);rr[0]['a']=bad;assert not check(rr,10,10,10)
    # Genuine infinite fiber at one leaf row, including freely varying large inactive fields.
    ev=candidate.Evaluation();ev.app(0,5);leaf=candidate.certificate(ev,(0,5))
    for m in (0,1,5,10,10**100):
        rr=copy.deepcopy(leaf)
        rr[0].update(a=m,b=m+1,c=m+2,u=m+3,v=m+4);refresh(rr[0])
        assert check(rr,0,5,11)
    receipt['infinite_fiber_witness']='For every natural m choose (a,b,c,u,v)=(m,m+1,m+2,m+3,m+4) at the single-row leaf certificate; refresh five lifts.'
    # Valid unused rows accepted; bad unreachable row still rejected.
    padded=candidate.certificate(ev,(0,5),pad=2);assert check(padded,0,5,11)
    padded[2]['z']+=1;assert not check(padded,0,5,11)
    cf=json.loads((HERE/'cyclic_counterfeit.json').read_text())['rows']
    cycle_checks=0
    for out in (0,1,2,10,100,1014,10**50):
      for h in (0,1,2,10,10**50):
        rr=copy.deepcopy(cf);rr[0].update(z=out,h=h)
        res=residuals(rr,1014,1014,out)
        assert [(i,r) for i,r in enumerate(res) if r]!=[]
        assert [r for r in res if r]==[-9]
        assert sum(r*r for r in res)==81
        assert not check(rr,1014,1014,out)
        cycle_checks+=1
    receipt['cyclic_counterfeit']={'outputs_and_heights_tested':cycle_checks,'only_nonzero_residual':'root height = -9','sum_of_squares':81,'independent_small_step_cycle':smallstep(1014,1014,budget=2000)['cycle']}
    # A returning arbitrary term which equationally discards omega but diverges under eager evaluation.
    # F(S(omega), F(0, F(0,0))) applied to omega evaluates omega omega before discarding it.
    omega=1014;erase=pair(stem(omega),pair(0,pair(0,0)))
    assert smallstep(erase,omega,budget=2000)['cycle']
    receipt['cbv_not_equational_normalization']={'function':erase,'argument':omega,'equational_result':0,'eager_cycle':True}
    # The supplied compression example is row-compressed but not bit-efficient.
    a=10;bl=[]
    for level in range(12):
        ev=candidate.Evaluation(budget=1000,max_bits=100000)
        assert ev.app(a,10)==10
        rows=candidate.certificate(ev,(a,10));assert check(rows,a,10,10)
        assert len(rows)==level+4 and rows[0]['h']==9*2**level-5
        bl.append({'level':level,'rows':len(rows),'root_h':rows[0]['h'],'input_bits':a.bit_length(),'scalar_bits':sum(max(1,r[f].bit_length()) for r in rows for f in FIELDS)})
        a=pair(stem(a),a)
    receipt['compression_bits']=bl
    receipt['snapshot_sha256']=hashlib.sha256((HERE/'tree_kernel.py').read_bytes()).hexdigest()
    receipt['audit_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (HERE/'independent_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
