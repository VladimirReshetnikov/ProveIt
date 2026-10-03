"""Asymmetric X=wq in the frozen linear-input and positive auxiliary-gap families.

Exact same-parent positive-zero bijections; ten explicit disjoint-factor
families, with an independently enumerated finite cost/degree objective.
"""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
import json
from math import prod
from pathlib import Path
import random

import sympy as sp
import complete75_linear_input_modulus89 as linear
import complete75_linear_input_degree_tradeoffs as linear_plans
import complete75_auxiliary_gap_degree_tradeoffs as gap
import complete75_asymmetric_scale_tradeoffs as scale
import complete75_asymmetric_factor_partitions as groups
import neary_woods_universal_joint_and_coupled_partitions as optimizer

DIRECT=('linear89',)+tuple('linear_'+n for n in linear_plans.VARIANTS)+tuple('gap_'+n for n in gap.VARIANTS)
DIRECT_DEGREES=dict(zip(DIRECT,(113,112,92,62,60,50,48,109,108,44,44)))
TREATMENTS=('coupled_units','uncoupled_units','coupled_comparison','uncoupled_comparison','six')
KINDS=tuple(f'{coordinate}_{t}' for coordinate in ('linear','gap') for t in TREATMENTS)
EXPECTED=[(89,113),(90,109),(91,108),(92,92),(93,84),(94,62),(95,60),(96,50),(97,48),(98,44)]
COMBINED=[(87,169),(88,125),(89,113),(90,109),(91,104),(92,92),(93,72),(94,62),(95,60),(96,50),(97,48),(98,44)]


def frozen(name):
    assert name in DIRECT
    if name=='linear89':
        _,certificate,pairs,rows=linear.sources();out='polynomial';aux=linear.RETAINED
    elif name.startswith('linear_'):
        _,certificate,pairs,rows,out=linear_plans.sources(name[7:]);aux=linear.RETAINED
    else:
        _,certificate,pairs,rows,out=gap.sources(name[4:]);aux=gap.RETAINED
    return dict(name=name,source=rows,output=out,certificate=certificate,comparisons=pairs,auxiliaries=list(aux))


def rewrite(old,name):
    assert old==frozen(name),'complete canonical selected frozen packet required'
    nodes={n:(o,a,b) for n,o,a,b in old['source']}
    assert nodes['wn2']==('*','w','n2') and nodes['sn2']==('*','s','n2')
    assert nodes['n2']==('*','Lbig','q')
    change=lambda rows:[(n,o,a,'q' if n=='wn2' else b) for n,o,a,b in rows]
    return dict(old,source=change(old['source']),certificate=change(old['certificate']))


def source(name='linear89'):
    return rewrite(frozen(name),name)


def run(rows,values,fixed):
    return scale.run(rows,values,fixed)


def base(kind):
    assert kind in KINDS
    coordinate,treatment=kind.split('_',1);isgap=coordinate=='gap';unc=treatment.startswith('uncoupled')
    if isgap:
        name='gap_'+('98_degree54' if treatment=='six' else '91_degree128' if unc else '90_degree131')
    else:
        name='linear_95_degree72' if treatment=='six' else 'linear_90_degree132' if unc else 'linear89'
    direct=source(name);factors=list(linear.FACTOR_NAMES)
    weights=[12,18,20,20 if isgap else 24,7,3,22,6 if unc else 7];pairs=[]
    if 'comparison' in treatment or treatment=='six':
        factors.pop(6);weights.pop(6);pairs=[('ic22','R16')]
    if treatment=='six':
        factors.pop();weights.pop();pairs.append(('H17','aux_u_rhs'))
    rows=groups.ancestors(direct['source'],factors+[v for pair in pairs for v in pair])
    core=dict(coupled_units=81,uncoupled_units=82,coupled_comparison=79,uncoupled_comparison=80,six=78)[treatment]+isgap
    assert len(rows)==core
    return dict(kind=kind,direct_parent=name,source=rows,factors=factors,weights=weights,
                ordinary_comparisons=pairs,residual_degree=22 if pairs else 0,
                auxiliaries=direct['auxiliaries'],input='x',
                scope='All supplied positive zeros equal within this base. The w/q^2 map is rational off zero, positive integral at zeros; the full actual fixed-compiler contract is retained.')


def grouped(original,partition,anchor):
    assert original==base(original['kind']),'complete canonical asymmetric linear/gap base required'
    partition=[list(g) for g in partition];n=len(original['factors'])
    assert partition and all(partition) and all(type(i) is int for g in partition for i in g)
    assert sorted(i for g in partition for i in g)==list(range(n))
    assert anchor is None or (type(anchor) is int and 0<=anchor<len(partition))
    rows=list(original['source']);products=[];names={n for n,*_ in rows}|set(original['auxiliaries']+['x'])
    for j,g in enumerate(partition):
        value=original['factors'][g[0]]
        for k,i in enumerate(g[1:]):
            name=f'linear_gap_group_{j}_{k}';assert name not in names;names.add(name)
            rows.append((name,'*',value,original['factors'][i]));value=name
        products.append(value)
    return dict(original,source=rows,partition=partition,anchor=anchor,group_products=products)


def checked(packet):
    assert packet==grouped(base(packet['kind']),packet['partition'],packet['anchor']),'complete canonical grouped packet required'


def polynomial_source(packet):
    checked(packet);rows=list(packet['source']);anchor=packet['anchor'];products=packet['group_products']
    pairs=list(packet['ordinary_comparisons'])+[(v,1) for j,v in enumerate(products) if j!=anchor]
    last=None
    for i,(a,b) in enumerate(pairs):
        r=f'linear_gap_residual_{i}';s=f'linear_gap_square_{i}';rows.extend([(r,'-',a,b),(s,'*',r,r)])
        if last is None:last=s
        else:
            add=f'linear_gap_sum_{i}';rows.append((add,'+',last,s));last=add
    if anchor is None:return rows,last
    if last is None:rows.append(('linear_gap_output','-',products[anchor],1))
    else:rows.extend([('linear_gap_positive','+',last,1),('linear_gap_anchored','*',products[anchor],'linear_gap_positive'),('linear_gap_output','-','linear_gap_anchored',1)])
    return rows,'linear_gap_output'


def exact_degree(packet):
    checked(packet);ds=[sum(packet['weights'][i] for i in g) for g in packet['partition']];a=packet['anchor'];r=packet['residual_degree']
    d=2*max([r]+ds) if a is None else ds[a]+2*max([r]+[v for i,v in enumerate(ds) if i!=a])
    return dict(exact_degree=d,group_degrees=ds)


def closure(rows,out,aux):
    available=set(aux+linear.eliminated.baseline.prior.CONSTANTS+['x','Bm1','Kconstant','twice_cell_bits'])
    for n,o,a,b in rows:
        assert n not in available and o in ('+','-','*')
        assert all(type(v) is int or v in available for v in (a,b));available.add(n)
    assert len(groups.ancestors(rows,[out]))==len(rows)


def record(packet):
    rows,out=polynomial_source(packet);counts=Counter(o for _,o,_,_ in rows)
    core=len(base(packet['kind'])['source']);n=len(packet['factors']);g=len(packet['partition']);m=len(packet['ordinary_comparisons'])
    special=m==0 and g==1 and packet['anchor']==0
    assert len(rows)==core+n+3*m+2*g-1-int(special)
    closure(rows,out,packet['auxiliaries'])
    return dict(kind=packet['kind'],partition=packet['partition'],anchor=packet['anchor'],core_operations=core,
                operations=len(rows),multiplications=counts['*'],additions_subtractions=counts['+']+counts['-'],
                certificate_operations=len(packet['source']),equations=m+g,witnesses=19,
                empty_residual_finalizer=special,**exact_degree(packet))


@lru_cache(None)
def search(kind):
    b=base(kind);plans,statistics=optimizer.optimal_partitions(b['weights'],b['residual_degree']);records=[]
    for plan in plans:
        r=record(grouped(b,plan['partition'],plan['anchor']));assert r['exact_degree']==plan['degree_upper_bound'];records.append(r)
    return dict(kind=kind,weights=b['weights'],statistics=statistics,best_by_group_count=records)


def nondominated(candidates):
    answer=[];bound=float('inf')
    for r in sorted(candidates,key=lambda r:(r['operations'],r['exact_degree'],r['kind'])):
        if r['exact_degree']<bound:answer.append(r);bound=r['exact_degree']
    return answer


def frontier(combined=False):
    candidates=[r for k in KINDS for r in search(k)['best_by_group_count']]
    if combined:candidates+=groups.frontier()
    answer=nondominated(candidates)
    assert [(r['operations'],r['exact_degree']) for r in answer]==(COMBINED if combined else EXPECTED)
    return deepcopy(answer)


def build(operations=98):
    r=next(r for r in frontier() if r['operations']==operations)
    return grouped(base(r['kind']),r['partition'],r['anchor'])


def independent_objectives():
    answer=[]
    for kind in KINDS:
        b=base(kind);w=b['weights'];r=b['residual_degree'];best={};count=choices=0
        for p in groups.bell_partitions(len(w)):
            ds=[sum(w[i] for i in g) for g in p]
            values=[2*max([r]+ds)]+[d+2*max([r]+[e for j,e in enumerate(ds) if j!=i]) for i,d in enumerate(ds)]
            g=len(p);best[g]=min(best.get(g,float('inf')),min(values));count+=1;choices+=len(values)
        assert best=={len(p['partition']):p['exact_degree'] for p in search(kind)['best_by_group_count']}
        floor=2*max([r]+w);assert min(best.values())==floor
        for mask in range(1,1<<len(w)):
            a=sum(v for i,v in enumerate(w) if mask>>i&1);other=max([r]+[v for i,v in enumerate(w) if not mask>>i&1])
            assert a+2*other>=floor
        answer.append(dict(kind=kind,bell_partitions=count,objective_choices=choices,best=best,family_floor=floor,anchor_subsets=(1<<len(w))-1))
    return answer


def fixed(B):
    return dict(B=B,DC=3,DR=5,MC=B-2,MF=4,cell_bits=B.bit_length()-1,inner_bits=3)


def direct_audit():
    rng=random.Random(891139044);result=[]
    for name in DIRECT:
        p=source(name);old=frozen(name);counts=Counter();closure(p['source'],p['output'],p['auxiliaries'])
        for case in range(64):
            signed=case>=32;v={n:rng.randrange(-5,6) if signed else rng.randrange(1,6) for n in p['auxiliaries']+['x']};B=(16,32,64,256)[case%4];f=fixed(B)
            e=run(p['source'],v,f);restored=scale.to_parent(v,B);o=run(old['source'],restored,f)
            assert all(e[n]==o[n] for n,*_ in p['source']);assert scale.from_parent(restored,B)==v
            forward=scale.from_parent(v,B);e2=run(p['source'],forward,f);o2=run(old['source'],v,f)
            assert all(e2[n]==o2[n] for n,*_ in p['source']);assert scale.to_parent(forward,B)==v
            allvalues={**restored,**f}
            if name=='linear89':manual=prod(linear.manual_factors(allvalues))-1
            elif name.startswith('linear_'):manual=linear_plans.expected_polynomial(name[7:],allvalues)
            else:manual=gap.expected_polynomial(name[4:],allvalues)
            assert e[p['output']]==manual
            counts['whole_register_two_way_identities']+=2;counts['signed_identities']+=2*signed;counts['manual_outputs']+=1
            counts['nonintegral_inverse']+=restored['w'].denominator!=1
            if name.startswith('gap_'):counts['negative_offzero_y']+=e['y_aux']<0
        assert len(p['source'])==len(old['source'])
        result.append(dict(name=name,operations=len(p['source']),certificate_operations=len(p['certificate']),equations=len(p['comparisons']),source=p['source'],output=p['output'],**counts))
    return result


def grouped_audit():
    rng=random.Random(984449);counts=Counter()
    for kind in KINDS:
        b=base(kind);old=frozen(b['direct_parent'])
        for choice in search(kind)['best_by_group_count']:
            p=grouped(b,choice['partition'],choice['anchor']);rows,out=polynomial_source(p)
            for case in range(16):
                signed=case>=8;v={n:rng.randrange(-4,5) if signed else rng.randrange(1,5) for n in p['auxiliaries']+['x']};B=(16,32,64,256)[case%4];f=fixed(B)
                e=run(rows,v,f);pv=scale.to_parent(v,B);pe=run(old['source'],pv,f)
                assert all(e[n]==pe[n] for n,*_ in b['source'])
                values={**pv,**f};manual=list(linear.manual_factors(gap.restored_values(values) if kind.startswith('gap_') else values))
                if 'uncoupled' in kind:manual[-1]=manual[-1]-manual[4]+1
                if kind.endswith('_six'):manual=manual[:6]
                elif 'comparison' in kind:manual.pop(6)
                assert manual==[e[n] for n in b['factors']]
                gs=[prod(manual[i] for i in g) for g in p['partition']]
                assert gs==[e[n] for n in p['group_products']]
                get=lambda n:e[n] if isinstance(n,str) else n
                R=sum((get(a)-get(bb))**2 for a,bb in p['ordinary_comparisons'])
                R+=sum((v-1)**2 for j,v in enumerate(gs) if j!=p['anchor'])
                assert e[out]==(R if p['anchor'] is None else gs[p['anchor']]*(1+R)-1)
                counts['complete_parent_manual_identities']+=1;counts['signed_identities']+=signed
    return dict(counts)


def leading_forms(v,B,d,isgap=False):
    Q=(B-1)*v['Jrep'];k=v['eta']+v['zeta'];gamma=v['rho']+v['sigma'];w=v['w'];s=v['s']
    C=Q-v['F']-v['Z']-v['alpha']-2*d*v['x']
    N3=(2*v['aux_gap']*v['f']**2*k*w*w*s**3*Q**11 if isgap else v['f']**2*k*k*w*w*s**4*Q**14)
    return [w*s*s*k*Q**7*(2*v['tau_gap']-k),8*gamma*k*w*w*s**3*Q**11,
            4*v['delta']*(2*v['rho']-v['delta'])*w**3*s**3*Q**12,N3,
            -v['h']*w*s*Q**4,w*Q*C,v['i']**2*k**4*s**4*Q**12,
            -v['h']*w*s*Q**4,-v['j']*k*s*Q**3]


def degree_audit():
    z=sp.Symbol('z');answer=[]
    plans=[('direct',name,source(name)) for name in DIRECT]+[('group',k,base(k)) for k in KINDS]
    plans += [('winner',str(r['operations']),build(r['operations'])) for r in frontier()]
    for mode,name,p in plans:
        for B,shift in ((16,0),(128,1)):
            v={n:1+(i+shift)%4 for i,n in enumerate(p['auxiliaries']+['x'])};v.update(delta=2+shift,rho=5+shift,tau_gap=7+shift)
            vals={n:sp.Poly(v[n]*z+i+1,z) for i,n in enumerate(p['auxiliaries']+['x'])}
            rows,out=(p['source'],p['output']) if mode=='direct' else (p['source'],None) if mode=='group' else polynomial_source(p)
            e=run(rows,vals,fixed(B));forms=leading_forms(v,B,B.bit_length()-1,'aux_gap' in p['auxiliaries'])
            if mode=='direct':
                assert e[out].degree()==DIRECT_DEGREES[name]
                is_unc='90_degree132' in name or '91_degree128' in name
                fs=[n for n in linear.FACTOR_NAMES if n in e]
                expected={n:forms[i] for i,n in enumerate(linear.FACTOR_NAMES)}
                if is_unc:expected['norm_linear']=forms[8]
                for n in fs:assert e[n].LC()==expected[n]
            else:
                expected=dict(zip(linear.FACTOR_NAMES,forms))
                if 'uncoupled' in p['kind']:expected['norm_linear']=forms[8]
                assert [e[n].degree() for n in p['factors']]==p['weights']
                assert [e[n].LC() for n in p['factors']]==[expected[n] for n in p['factors']]
                for a,b in p['ordinary_comparisons']:
                    assert (e[a]-e[b]).degree()==(22 if a=='ic22' else 6)
                if mode=='winner':assert e[out].degree()==record(p)['exact_degree']
            answer.append(dict(mode=mode,name=name,B=B,degree=e[out].degree() if out else None,leading_coefficient=str(e[out].LC()) if out else None))
    return answer


def wrap_audit():
    count=0
    for q in (16,17,32,64,257):
      for w in (1,3):
       for s in (1,2):
        E=w*s*q**4
        for R in ((2*q-1)*(q*q-1)+1,q**4-q**3-1):
         assert E>R+q**3
         for epsilon in (-1,1):
          assert 0<R+epsilon<E
          for lam in (-1,1):
           for coupled in (False,True):
            p=R+(epsilon if coupled else 1)-lam
            assert R-2<=p<=R+2
            for v in (-2,-1,0,1,2):
             n2=R+epsilon+v*E
             if 0<n2<2*p:assert v==0
             count+=1
    return dict(coupled_uncoupled_index_wrap_cases=count,
                scope='Exact boundary implications, not Pell or compiler-zero fixtures.')


def guard_audit():
    count=0
    def reject(f):
        nonlocal count
        try:f()
        except (AssertionError,KeyError):count+=1
        else:raise AssertionError('bad caller accepted')
    for name in DIRECT:
        p=frozen(name)
        reject(lambda:rewrite(dict(p,source=p['source'][:-1]),name))
        reject(lambda:rewrite(dict(p,auxiliaries=p['auxiliaries'][:-1]),name))
    for kind in KINDS:
        b=base(kind);n=len(b['factors']);p=grouped(b,[list(range(n))],0)
        for key,val in [('source',b['source'][:-1]),('weights',[1]*n),('auxiliaries',[])]:reject(lambda key=key,val=val:grouped(dict(b,**{key:val}),[list(range(n))],0))
        for part,a in [([[0],[0]+list(range(1,n))],None),([list(range(n-1))],0),([list(range(n))],True),([list(range(n))],1)]:reject(lambda part=part,a=a:grouped(b,part,a))
        for key,val in [('source',p['source'][:-1]),('group_products',['q']),('ordinary_comparisons',[('q',1)])]:reject(lambda key=key,val=val:polynomial_source(dict(p,**{key:val})))
    return count


def verify():
    emitted=[]
    for r in frontier():
        p=build(r['operations']);rows,out=polynomial_source(p)
        emitted.append(dict(r,source=rows,output=out,source_sha256=hashlib.sha256(json.dumps(rows).encode()).hexdigest()))
    return dict(status='PASS_COMPLETE75_ASYMMETRIC_LINEAR_GAP_TRADEOFFS',direct_transfers=direct_audit(),
                searches=[search(k) for k in KINDS],frontier=frontier(),combined_frontier=frontier(True),emitted=emitted,
                independent_objectives=independent_objectives(),grouped_audit=grouped_audit(),degree_audit=degree_audit(),
                wrap_audit=wrap_audit(),rejected_callers=guard_audit(),scope='Ten explicit factor/comparison bases only; no all-circuit optimum. Full positive-zero bijections to the selected frozen linear-input and gap parents; off-zero rational w maps. All nineteen witnesses and the actual compiler contract are retained. Frozen normalized87/ordinary88 grouping sources are used only for the displayed union frontier.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert result==json.loads(path.read_text()),'receipt mismatch'
    print(result['status']);print([(r['operations'],r['exact_degree']) for r in result['frontier']]);print(result['grouped_audit'])
