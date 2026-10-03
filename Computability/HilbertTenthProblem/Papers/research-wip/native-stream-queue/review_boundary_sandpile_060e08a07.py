"""Portable independent review checks for two frozen incoming reports.

Sources are authenticated before import. Only an explicit CLI output is written.
Author CLI replays are separate; this helper checks independent identities,
domains, closed graphs, actual sparse-source transfers and a focused repair.
"""
import argparse
from collections import Counter
from contextlib import contextmanager
from copy import deepcopy
from fractions import Fraction
import hashlib
import importlib.util
from itertools import combinations, product
import json
from pathlib import Path
import random
import sys

ARCHIVES = {
 'Linear_Boundary_Transport_Research.zip':'7b2b3505fe36d9f01777bd198742cc1206f1232e0951964d1ee30681c6c5e096',
 'no_borrowed_firings.zip':'390c4c9a6dbe9a7701de8e0b6689a21d60b35c577aa11a9977989c088a8d0d45'}
PINS = {'linear':{'code/boundary_transport.py':'6e35bbf8d574651d644bd0de728d02cd5569b668bf4bcb23d12f10ba4438f248',
 'code/verify.py':'85b9fab3229edae30fea94b66e01ad95762d3286939d51f7706657e3b99cbb96'},
 'sandpile':{'sandpile_certificates.py':'2e1d8c20678a1bfcec352c9dc047cc1ab8afb3dd93b3559f0ddad2977baf0519',
 'verify.py':'c8bbf4ceb38e484f1fbfa9d912201cdc562aab1e83a05bc5eea20c3e7c77c7ea'}}
PATCHED_SHA = 'a77ae4cf4412435f06d5fe331bca2d46f655d00c1c5bc0abed8d91b2ad1b03b1'


@contextmanager
def loaded(path,name):
    before=sys.modules.get(name)
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec)
    sys.modules[name]=m
    try:spec.loader.exec_module(m);yield m
    finally:
        if before is None:sys.modules.pop(name,None)
        else:sys.modules[name]=before


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def reject(call,counts,key='guard_rejections'):
    try:call()
    except (ValueError,TypeError,KeyError):counts[key]+=1;return
    raise AssertionError('Malformed object accepted')


def addpoly(a,b,scale=1):
    out=dict(a)
    for e,c in b.items():out[e]=out.get(e,0)+scale*c
    return {e:c for e,c in out.items() if c}


def shifted(p,delta):return {tuple(a+b for a,b in zip(e,delta)):c for e,c in p.items()}


def boundary_checks(m):
    counts=Counter();rng=random.Random(60081)
    programs=[]
    opts=[m.Instruction('HALT')]+[m.Instruction('INC',j,q) for j in (0,1) for q in (0,1)]+[m.Instruction('TEST',j,q,r) for j in (0,1) for q in (0,1) for r in (0,1)]
    programs.extend(m.Program(ins) for ins in product(opts,repeat=2))
    for q in (1,3,4):
        for case in range(10):
            programs.append(m.Program(tuple(m.Instruction(rng.choice(('HALT','INC','TEST')),rng.randrange(2),rng.randrange(q),rng.randrange(q)) for _ in range(q))))
    for p in programs:
        q=len(p.instructions);d=sum(i.op=='TEST' for i in p.instructions)
        for clock in (False,True):
            s=m.compile_system(p,(0,1,0),clock)
            assert len(s.rows)==q+d and len(s.sorts)==q+2*d
            uses=Counter()
            for row in s.rows:
                for name,coef in row.items():
                    uses[name]+=len(coef)
                    assert all(c in (-1,1) and sum(e)<=2 for e,c in coef.items())
            assert max(uses.values())<=2;counts['literal_arity_sparsity_forms']+=1
            h=[]
            for i in range(q):
                h.append({(rng.randrange(3),rng.randrange(3),rng.randrange(3) if clock else 0):rng.randrange(-3,4) for _ in range(6)})
            h=[{e:c for e,c in v.items() if c} for v in h]
            # Direct monomial successor arithmetic, without transport/step.
            out=[dict(v) for v in h]
            for i,ins in enumerate(p.instructions):
                for (a,b,t),c in h[i].items():
                    if ins.op=='HALT':continue
                    pos=[a,b];nxt=ins.target
                    if ins.op=='INC':pos[ins.counter]+=1
                    elif pos[ins.counter]:pos[ins.counter]-=1
                    else:nxt=ins.zero
                    out[nxt]=addpoly(out[nxt],{(*pos,t+int(clock)):c},-1)
            out[0]=addpoly(out[0],{(1,0,0):1},-1)
            w=s.witness(h);actual=s.evaluate(w)
            assert actual[:q]==out and all(not x for x in actual[q:])
            counts['signed_monomial_transport_identities']+=1
            for modulus in (2,3,6):
                reduced=[{e:c%modulus for e,c in row.items() if c%modulus} for row in out]
                result=s.evaluate(w,modulus)
                assert result[:q]==reduced and all(not x for x in result[q:])
                counts['modular_transport_identities']+=1
    # Exact rational taper identities are independent finite telescoping sums.
    endless=m.Program((m.Instruction('INC',0,0),))
    for n in range(20):
        h=[{(t,0,t):Fraction(n+1-t,n+2) for t in range(n+1)}]
        rr=m.residual(endless,(0,0,0),h)
        assert rr==[{(t,0,t):Fraction(-1,n+2) for t in range(n+2)}]
        assert m.energy(endless,(0,0,0),h)==Fraction(1,n+2)
        counts['rational_taper_and_spill_cases']+=1
    for n in range(5):
        rank,columns,ok=m.gf2_bounded_solve(endless,(0,0,0),n,0,n)
        assert rank==columns and not ok;counts['nonhalting_spill_rejections']+=1
    # Reproduce the actual malformed-clock defect, not a change of the theorem.
    p=m.Program((m.Instruction('HALT'),m.Instruction('TEST',0,0,1)))
    s=m.compile_system(p,(0,0,0),clocked=0.5)
    a=s.witness([{(0,0,0):1},{}]);b=s.witness([{(0,0,0):1},{(0,3,0):7}])
    assert a!=b and s.accepts(a) and s.accepts(b) and s.clocked
    counts['reproduced_truthy_clock_uniqueness_failure']+=1
    p=m.TRANSFER;path,halted=p.run((0,0,0),2)
    s=m.compile_system(p,(0,0,0),2)
    assert halted and not s.accepts(s.witness(m.history(p,path,2)))
    counts['reproduced_integer_clock_self_inconsistency']+=1
    for bad in (True,0.5,-1):
        reject(lambda bad=bad:m.Program((m.Instruction('TEST',bad,0,0),)),counts)
        reject(lambda bad=bad:m.clean({(0,0,0):1},bad),counts)
    return dict(counts)


def repair_checks(m):
    counts=Counter();p=m.TRANSFER;path,halted=p.run((0,2,0),20)
    for clock in (False,True):
        s=m.compile_system(p,(0,2,0),clock);h=m.history(p,path,clock)
        assert halted and s.accepts(s.witness(h)) and not any(m.residual(p,(0,2,0),h,clock))
        counts['valid_boolean_mode_cases']+=1
    h=m.history(p,path);s=m.compile_system(p,(0,2,0));w=s.witness(h)
    for flag in (0,1,2,0.5,1.0,None,'True',[],{}):
        reject(lambda flag=flag:m.compile_system(p,(0,2,0),flag),counts)
        reject(lambda flag=flag:m.history(p,path,flag),counts)
        reject(lambda flag=flag:m.residual(p,(0,2,0),h,flag),counts)
        reject(lambda flag=flag:s.evaluate(w,enforce_sorts=flag),counts)
    return dict(counts)


def graph_family(m):
    for n in (1,2,3):
        edges=list(combinations(range(n),2))
        for present in product((0,1),repeat=len(edges)):
            a=[[0]*n for _ in range(n)]
            for (i,j),v in zip(edges,present):a[i][j]=a[j][i]=v
            for sink in product((0,1),repeat=n):
                if any(sum(a[i])+sink[i]==0 for i in range(n)):continue
                yield m.Graph(tuple(map(tuple,a)),sink)


def legal_simulation(graph,chips):
    a=graph.adjacency;d=graph.degree;c=tuple(chips);seen=set();u=[0]*graph.n
    while c not in seen:
        seen.add(c);unstable=[i for i in range(graph.n) if c[i]>=d[i]]
        if not unstable:return tuple(u),c
        i=unstable[0];n=list(c);n[i]-=d[i]
        for j in range(graph.n):n[j]+=a[i][j]
        c=tuple(n);u[i]+=1
    return None


def no_forbidden(graph,u,s):
    active=[i for i,v in enumerate(u) if v]
    for size in range(1,len(active)+1):
        for subset in combinations(active,size):
            if all(s[i]<sum(graph.adjacency[i][j] for j in subset) for i in subset):return False
    return True


def manual_residuals(graph,chips,w):
    out=[]
    for i in range(graph.n):
        v={key:w[f'v{i}.{key}'] for key in ('u','s','sigma','z','alpha','r','k','e','beta','lam','mu')};K=H=0
        for j,a in enumerate(graph.adjacency[i]):
            if not a:continue
            for prefix,offset in (('a',0),('b',1)):
                B,p,q=(w[f'{prefix}{i}_{j}.{name}'] for name in ('b','p','q'))
                diff=w[f'v{j}.r']-v['r']+offset
                out.extend([B*(B-1),diff-B*p+(1-B)*(q+1),(1-B)*p,B*q])
                if prefix=='a':K+=a*B
                else:H+=a*B
        u,s,sigma,z,alpha,r,k,e,beta,lam,mu=(v[x] for x in ('u','s','sigma','z','alpha','r','k','e','beta','lam','mu'))
        out.extend([s-chips[i]+graph.degree[i]*u-sum(a*w[f'v{j}.u'] for j,a in enumerate(graph.adjacency[i])),s+sigma-graph.degree[i]+1,
                    z*(z-1),u-z*(alpha+1),(1-z)*alpha,r-z-k,(1-z)*k,
                    e*(e-1),k-e*(beta+1),(1-e)*beta,lam-z*(s-K),mu-e*(H-s-1)])
    return out


def actual_sparse_projection(m,cert,graph,counts):
    """Eliminate u,k,r from the actual source with a natural-zero bijection.

    Section: every retained natural tuple restores u=z+alpha, k=e+beta,
    r=z+e+beta to naturals. Under this section the three deleted rows become
    retained active.inactive, retained later.inactive, and zero, respectively.
    Hence a retained zero restores a complete parent zero. Inverse: in every
    parent zero, (1-z)*alpha=0 changes u=z*(alpha+1) into u=z+alpha;
    (1-e)*beta=0 similarly changes k=e*(beta+1) into k=e+beta; rank gives
    r=z+k. Erasing these coordinates and restoring is therefore the identity.
    Retained coordinates are not changed by restoration/erasure, so the maps
    are two-sided inverses on complete natural zero sets, preserving the
    parent's canonical uniqueness. No arithmetic-operation saving is inferred.
    """
    removed={f'v{i}.{name}' for i in range(graph.n) for name in ('u','k','r')}
    kept=[name for name in cert.variables if name not in removed]
    variables={name:m.Poly.var(i) for i,name in enumerate(kept)}
    for i in range(graph.n):
        v=lambda n:variables[f'v{i}.{n}']
        variables[f'v{i}.u']=v('z')+v('alpha')
        variables[f'v{i}.k']=v('e')+v('beta')
        variables[f'v{i}.r']=v('z')+v('e')+v('beta')
    transformed={}
    for label,row in zip(cert.labels,cert.residuals):
        out=m.Poly.const(0)
        for mon,c in row.terms.items():
            term=m.Poly.const(c)
            for index in mon:term*=variables[cert.variables[index]]
            out+=term
        transformed[label]=out
    deleted={f'v{i}.{name}' for i in range(graph.n) for name in ('active.value','later.value','rank')}
    for i in range(graph.n):
        assert transformed[f'v{i}.rank'].terms=={}
        for part in ('active','later'):
            assert transformed[f'v{i}.{part}.value'].terms==transformed[f'v{i}.{part}.inactive'].terms
            counts['source_projection_duplicate_row_identities']+=1
        counts['source_projection_zero_row_identities']+=1
    newrows=[p for label,p in transformed.items() if label not in deleted]
    assert len(kept)==8*graph.n+12*graph.m and len(newrows)==9*graph.n+16*graph.m
    assert max(row.degree for row in newrows)==2
    counts['actual_source_projection_forms']+=1
    return kept,newrows


def sandpile_checks(m,root):
    counts=Counter();rng=random.Random(60082)
    for g in graph_family(m):
        counts['graphs_including_closed_components']+=1
        for chips in product(range(3),repeat=g.n):
            actual=legal_simulation(g,chips);counts['independent_legal_simulations']+=1
            counts['repeated_state_nontermination_cases']+=actual is None
            for u in product(range(4),repeat=g.n):
                s=tuple(chips[i]-g.degree[i]*u[i]+sum(g.adjacency[i][j]*u[j] for j in range(g.n)) for i in range(g.n))
                if all(0<=s[i]<g.degree[i] for i in range(g.n)):
                    assert no_forbidden(g,u,s)==(actual is not None and u==actual[0])
                    counts['stable_candidate_support_theorem_checks']+=1
                counts['candidate_odometer_vectors']+=1
        chips=tuple(2 for _ in range(g.n));cert=m.compile_graph(g,chips)
        assert len(cert.variables)==11*g.n+12*g.m and len(cert.residuals)==12*g.n+16*g.m
        kept,newrows=actual_sparse_projection(m,cert,g,counts)
        if legal_simulation(g,chips) is not None:
            original=m.graph_assignment(g,chips)
            small={n:original[n] for n in kept};restored=dict(small)
            for i in range(g.n):
                get=lambda n:small[f'v{i}.{n}']
                restored[f'v{i}.u']=get('z')+get('alpha')
                restored[f'v{i}.k']=get('e')+get('beta')
                restored[f'v{i}.r']=get('z')+get('e')+get('beta')
            assert restored==original and all(type(v) is int and v>=0 for v in restored.values())
            assert all(row.evaluate([small[n] for n in kept])==0 for row in newrows)
            assert all(v==0 for v in cert.evaluate(cert.vector(restored)))
            assert {n:restored[n] for n in kept}==small
            counts['natural_zero_section_inverse_cases']+=1
        for signed in (False,True):
            for case in range(3):
                w={n:rng.randrange(-2,4) if signed else rng.randrange(4) for n in cert.variables}
                values=[w[n] for n in cert.variables]
                assert manual_residuals(g,chips,w)==[p.evaluate(values) for p in cert.residuals]
                counts['complete_signed_or_natural_source_comparisons']+=1
                # Exact off-zero SOS correction after the deletion/restoration.
                small={n:w[n] for n in kept};full=dict(small)
                for i in range(g.n):
                    get=lambda n:small[f'v{i}.{n}']
                    full[f'v{i}.u']=get('z')+get('alpha');full[f'v{i}.k']=get('e')+get('beta');full[f'v{i}.r']=get('z')+get('e')+get('beta')
                vv=[small[n] for n in kept];ff=[full[n] for n in cert.variables]
                old=sum(p.evaluate(ff)**2 for p in cert.residuals);new=sum(p.evaluate(vv)**2 for p in newrows)
                correction=sum(((1-small[f'v{i}.z'])*small[f'v{i}.alpha'])**2+((1-small[f'v{i}.e'])*small[f'v{i}.beta'])**2 for i in range(g.n))
                assert old-new==correction;counts['complete_source_projection_SOS_corrections']+=1
    g=m.Graph(((0,1),(1,0)),(1,1));cert=m.compile_graph(g,(3,1));quartic=cert.quartic()
    assert quartic.degree==4 and len(quartic.terms)==201
    saved=json.loads((root/'examples/two_vertex_certificate.json').read_text())
    assert saved==cert.serialize(expand_quartic=True);counts['complete_quartic_exports']+=1
    values=cert.vector(m.graph_assignment(g,(3,1)))
    for index in range(len(values)):
        for val in (float(values[index]),bool(values[index]),-1):
            bad=list(values);bad[index]=val;reject(lambda bad=bad:cert.evaluate(bad),counts)
    for bad in (True,1.0,-1):
        reject(lambda bad=bad:m.Graph(((0,bad),(bad,0)),(1,1)),counts)
        reject(lambda bad=bad:m.PeriodicInput((1,),(bad,)),counts)
        reject(lambda bad=bad:m.compile_periodic_cube(m.PeriodicInput((1,),(0,)),bad),counts)
    document=json.loads((root/'examples/three_dimensional_field_certificate.json').read_text())
    data,w=m.read_field_witness(document);assert m.verify_field_witness(data,w)
    assert len(w)==57 and len(m.field_names(3))==47;counts['field_export_roundtrips']+=1
    x=next(iter(w))
    for i in range(47):
        for val in (True,1.0,-1,w[x][i]+1):
            bad=deepcopy(w);v=list(bad[x]);v[i]=val;bad[x]=tuple(v)
            assert not m.verify_field_witness(data,bad);counts['field_coordinate_rejections']+=1
    # Infinite tail can never repair a missed leaking boundary.
    leak=m.PeriodicInput((1,1,1),(5,),(((0,0,0),1),))
    reject(lambda:m.field_witness_from_cube(leak,0),counts)
    reject(lambda:m.compile_periodic_cube(m.PeriodicInput((1,),(0,),(((2,),1),)),1),counts)
    for d in (1,2,3):
        tail=m.PeriodicInput((2,)+(1,)*(d-1),(0,2*d-1))
        assert m.verify_field_witness(tail,{})
        assert len(m.field_residuals_at(tail,{},(-1,)+(0,)*(d-1)))==12+16*d
        counts['periodic_empty_field_cases']+=1
    return dict(counts)


def verify(linear_root,sandpile_root,patched_linear_root=None):
    linear_root=Path(linear_root);sandpile_root=Path(sandpile_root)
    for kind,root in (('linear',linear_root),('sandpile',sandpile_root)):
        for name,wanted in PINS[kind].items():assert sha(root/name)==wanted,(kind,name)
    with loaded(linear_root/'code/boundary_transport.py','_review_boundary060') as m:linear=boundary_checks(m)
    with loaded(sandpile_root/'sandpile_certificates.py','_review_sandpile060') as m:sandpile=sandpile_checks(m,sandpile_root)
    answer={'status':'PASS_WITH_REPRODUCED_BOUNDARY_MODE_DEFECT','archive_sha256':ARCHIVES,'source_pins':PINS,'linear':linear,'sandpile':sandpile,
            'sandpile_projection':{'witness_count':'8*n+12*m','residual_count':'9*n+16*m','dimension3_field_count':44,'dimension3_local_residual_count':57,'complete_natural_zero_bijection':True,'operation_count_claim':False},
            'scope':'Proof and actual-source checks for finite-support polynomial/field witnesses, not a fixed finite scalar universal equation. No arithmetic-operation claim for the source projection.'}
    if patched_linear_root is not None:
        path=Path(patched_linear_root)/'code/boundary_transport.py';assert sha(path)==PATCHED_SHA
        with loaded(path,'_review_boundary060_fixed') as m:answer['repair']=repair_checks(m)
        answer['patched_source_sha256']=PATCHED_SHA
        answer['status']='PASS_WITH_REPRODUCED_AND_REPAIRED_BOUNDARY_MODE_DEFECT'
    return answer


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--linear-root',type=Path,required=True);parser.add_argument('--sandpile-root',type=Path,required=True);parser.add_argument('--patched-linear-root',type=Path);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();result=verify(args.linear_root,args.sandpile_root,args.patched_linear_root);args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
