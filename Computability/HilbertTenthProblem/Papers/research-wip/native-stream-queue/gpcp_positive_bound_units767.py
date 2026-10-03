"""Four signed positive-bound units in the complete instantiated GPCP compiler.

Paired AND/geometry options project positively onto canonical771, with an
explicit positive section. Signs need not be positive; no tuple bijection
or arbitrary-point polynomial identity is claimed.
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

import gpcp_checksum_global_units771 as parent

SPECS=(
 ('and','and_X_bound_unit','and__bs_X_bound','and__wn2','and__bound_beta'),
 ('and','history_X_bound_unit','hist__and__bs_X_bound','hist__and__wn2','hist__and__bound_beta'),
 ('geometry','geometry_X_bound_unit','geo__geometry_X_bound','geo__wn2','geo__bound_beta'),
 ('geometry','geometry_index_bound_unit','geo__geometry_index_bound','J','geo__index_beta'))


def chosen(and_bounds,geometry_bounds):
    assert type(and_bounds)is bool and type(geometry_bounds)is bool
    return [row for row in SPECS if (and_bounds if row[0]=='and' else geometry_bounds)]


def rewrite(old,*,and_bounds=True,geometry_bounds=True):
    assert type(and_bounds)is bool and type(geometry_bounds)is bool
    inline=old.get('inline_initial');assert type(inline)is bool
    assert old==parent.build(inline_initial=inline,global_unit=True),'complete canonical771 global-unit parent required'
    source=list(old['source']);pairs=list(old['comparisons'][:-1]);unit=old['unit_register'];factors=list(old['unit_factors'])
    by={n:(o,a,b) for n,o,a,b in source};selected=chosen(and_bounds,geometry_bounds)
    assert by['input_bound']==('+','x','input_slack') and by['B']==('*',2**63,'Q')
    powers={'input_bound':1}
    for n,o,a,b in source:
        if o=='*' and a in powers and b in powers:powers[n]=powers[a]+powers[b]
    assert powers['Q']==64
    lhs_bases=('and__bs_packed','hist__and__bs_packed','J','B')
    for index,(_,name,lhs,rhs,beta) in enumerate(SPECS):
        assert by[lhs]==('+',lhs_bases[index],beta) and (lhs,rhs) in old['comparisons']
        assert {n for n,o,a,b in source if beta in (a,b)}=={lhs}
        assert not any(lhs in (a,b) for n,o,a,b in source)
        assert beta in old['auxiliaries'] and name not in by
        assert not any(beta in pair for pair in old['comparisons'])
    for index,(_,name,lhs,rhs,beta) in enumerate(selected):
        product=f'positive_bound_product_{index}';assert product not in by
        source.extend([(name,'-',rhs,lhs),(product,'*',unit,name)])
        pairs.remove((lhs,rhs));factors.append(name);unit=product
    pairs.append((unit,1));counts=Counter(o for n,o,a,b in source)
    p=deepcopy(old)
    p.update(source=source,comparisons=pairs,unit_factors=factors,unit_register=unit,
        operations=len(source),multiplications=counts['*'],additions_subtractions=counts['+']+counts['-'],equations=len(pairs),
        positive_bound_parent=old,and_bounds=and_bounds,geometry_bounds=geometry_bounds,
        bound_unit_specs=selected,positive_bound_units=True,
        identical_complete_integer_polynomial=not selected,identical_positive_zero_set=not selected,
        positive_zero_bijection=not selected,positive_zero_surjection=True,
        projection='Full positive surjection to771: enabled native beta_parent=beta_new+H, global beta_parent=beta_new+G-1; all other coordinates retained.',
        positive_section='Add1 to every enabled native bound slack, retaining global slack and every other coordinate. Each enabled pair has both signs-1.')
    assert p['operations']==old['operations']+2*len(selected) and p['equations']==old['equations']-len(selected)
    return p


@lru_cache(None)
def _build(inline_initial,and_bounds,geometry_bounds):
    return rewrite(parent.build(inline_initial=inline_initial,global_unit=True),and_bounds=and_bounds,geometry_bounds=geometry_bounds)


def build(*,inline_initial=True,and_bounds=True,geometry_bounds=True):
    assert all(type(v)is bool for v in (inline_initial,and_bounds,geometry_bounds))
    return _build(inline_initial,and_bounds,geometry_bounds)


def checked(packet):
    flags=[packet.get(n) for n in ('inline_initial','and_bounds','geometry_bounds')]
    assert all(type(v)is bool for v in flags)
    assert packet==build(inline_initial=flags[0],and_bounds=flags[1],geometry_bounds=flags[2]),'complete canonical positive-bound packet required'


def polynomial_source(packet=None):
    if packet is None:packet=build()
    checked(packet);return parent.parent.parent.polynomial_source(packet)


def degree_dictionary(packet=None):
    if packet is None:packet=build()
    checked(packet);return parent.parent.raw_degrees(packet)


def degree_audit(packet=None):
    if packet is None:packet=build()
    checked(packet);old=packet['positive_bound_parent'];prior=parent.degree_audit(old)
    degrees=degree_dictionary(packet);d=lambda n:degrees[n] if isinstance(n,str) else 0
    assert all(degrees[n]==v for n,v in parent.degree_dictionary(old).items())
    added=0;leaders={}
    for _,name,lhs,rhs,beta in packet['bound_unit_specs']:
        assert d(lhs)!=d(rhs)
        lead=rhs if d(rhs)>d(lhs) else lhs
        leaders[name]=dict(degree=d(name),sign=1 if lead==rhs else -1,leading_register=lead)
        assert d(name)==max(d(lhs),d(rhs));added+=d(name)
    # A remaining maximal residual has strict highest part -r_history.
    assert ('hist__and__R10b','hist__and__R11') in packet['comparisons']
    by={n:(o,a,b) for n,o,a,b in packet['source']}
    assert by['hist__and__R11']==('+','hist__and__r1','hist__and__hpm1')
    assert by['hist__and__r1']==('+','hist__and__bs_packed',1)
    maximum=prior['maximum_outer_degree']
    assert d('hist__and__bs_packed')==maximum>d('hist__and__hpm1')
    assert maximum>d('hist__and__R10b')
    assert max(max(d(a),d(b)) for a,b in packet['comparisons'][:-1])==maximum
    assert d(packet['unit_register'])==prior['unit_degree']+added
    rows,out=polynomial_source(packet)
    for n,o,a,b in rows:
        if n not in degrees:degrees[n]=d(a)+d(b) if o=='*' else max(d(a),d(b))
    assert degrees[out]==prior['exact_degree']+added
    return dict(exact_degree=degrees[out],parent_exact_degree=prior['exact_degree'],degree_increment=added,
        unit_degree=prior['unit_degree']+added,maximum_outer_degree=maximum,
        factor_degrees={n:d(n) for n in packet['unit_factors']},new_bound_leaders=leaders,
        nonzero_maximal_residual=['hist__and__R10b','hist__and__R11'],
        exactness_reason='Each new bound has a strict nonzero leading side; retained history first-index residual has strict nonzero leader -r. The parent unit leader and all three guarded main-norm cancellations are unchanged.')


def ledger(packet=None):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet);counts=Counter(o for n,o,a,b in rows)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(rows),multiplications=counts['*'],additions_subtractions=counts['+']+counts['-'],output=out),degree=degree_audit(packet))


execute=parent.execute


def project_to_parent(packet,values):
    """Formal integer map; positivity is proved only on positive zeros."""
    checked(packet);env=execute(packet['source'],values);result=dict(values)
    for _,name,lhs,rhs,beta in packet['bound_unit_specs']:result[beta]+=env[name]
    result[parent.BETA]+=env[parent.GLOBAL]-1
    return result


def section_from_parent(packet,values):
    """Positive section on parent zeros: paired new unit signs are both-1."""
    checked(packet);result=dict(values)
    for _,name,lhs,rhs,beta in packet['bound_unit_specs']:result[beta]+=1
    return result


def source_audit(cases=12):
    rng=random.Random(767771);counts=Counter()
    for inline in (False,True):
      for and_bounds in (False,True):
       for geometry_bounds in (False,True):
        p=build(inline_initial=inline,and_bounds=and_bounds,geometry_bounds=geometry_bounds);old=p['positive_bound_parent']
        rows,out=polynomial_source(p);before,target=parent.polynomial_source(old)
        for case in range(cases):
            signed=case>=cases//2
            values={n:rng.randrange(-2,3) if signed else rng.randrange(1,3) for n in p['parameters']+p['auxiliaries']}
            if case%6==0:values.update({f'hist__Shat{i}':1 for i in range(57)});counts['zero_selector_cases']+=1
            e=execute(rows,values);lift=project_to_parent(p,values);past=execute(before,lift)
            changed={parent.GLOBAL,parent.GLOBAL_PAIR[0],old['unit_register']}|{lhs for _,_,lhs,_,_ in p['bound_unit_specs']}
            assert all(e[n]==past[n] for n,o,a,b in old['source'] if n not in changed)
            assert past[parent.GLOBAL]==1
            for _,name,lhs,rhs,beta in p['bound_unit_specs']:assert past[lhs]==past[rhs]
            multiplier=e[parent.GLOBAL]*prod(e[name] for _,name,_,_,_ in p['bound_unit_specs'])
            assert e[out]+1==multiplier*(past[target]+1)
            at=lambda v:e[v] if isinstance(v,str) else v
            square=sum((at(a)-at(b))**2 for a,b in p['comparisons'][:-1])
            assert e[out]==prod(e[n] for n in p['unit_factors'])*(1+square)-1
            counts['complete_projection_output_and_register_maps']+=1;counts['signed_projection_cases']+=signed
            # Formal section identity, without assuming parent comparisons.
            oldenv=execute(before,values);section=section_from_parent(p,values);newenv=execute(rows,section)
            altered={lhs for _,_,lhs,_,_ in p['bound_unit_specs']}
            for n,o,a,b in old['source']:
                assert newenv[n]==oldenv[n]+(1 if n in altered else 0)
            residuals=[oldenv[rhs]-oldenv[lhs] for _,_,lhs,rhs,_ in p['bound_unit_specs']]
            at=lambda v:newenv[v] if isinstance(v,str) else v
            S=sum((at(a)-at(b))**2 for a,b in p['comparisons'][:-1]);W=oldenv[old['unit_register']]
            assert newenv[out]==W*prod(r-1 for r in residuals)*(1+S)-1
            assert oldenv[target]==W*(1+S+sum(r*r for r in residuals))-1
            counts['complete_formal_section_output_and_register_maps']+=1
    return dict(counts)


def boundary_audit():
    counts=Counter()
    for q in (16,32,48,64,256):
      for C in (-1,1):
       for r in (2-C+16*k+q**3 for k in (1,2,17)):
        assert r%16 in (1,3)
        X=((r+q-1)//q)*q;gap=X-r
        assert gap>= (15 if C==1 else 13)
        for H in (-1,1):
            beta=gap-H;assert beta>0 and X-r-beta==H and beta+H==gap
            counts['AND_residue_gap_branches']+=1
    for q in (2,3,4,7,16):
        B=2**63*q**64
        for J in (B,B+1,B+17):
          for X in (J,J+1,2*J):
            assert J>=B>=2**127 and J>q and X>=J
            assert X*3*q>2*J+1 and 3*q*(X+1)>2*J+1
            assert J>=8
            counts['weak_geometry_bootstrap_contexts']+=1
    # Paired negative sections, including the real odd/even index gap1.
    for old_gap in (1,3,15,31,255):
      for other_gap in (1,15,1023):
        section=(old_gap+1,other_gap+1);signs=(-1,-1)
        assert all(v>0 for v in section) and prod(signs)==1
        assert tuple(v+h for v,h in zip(section,signs))==(old_gap,other_gap)
        counts['paired_negative_positive_sections']+=1
    q=4;B=2**63*q**64;J=B+1
    assert J.bit_count()==2 and q==2**J.bit_count() and J-B==1
    counts['canonical_geometry_index_gap_one']=1
    # Both signs of global unit restore the same positive771 global gap.
    for D in (4,8,32):
      for J in (1,2,7):
        oldgap=(131068*D+3)*J-8
        assert oldgap>0
        for G in (-1,1):
            newgap=oldgap+1-G;assert newgap>0 and newgap+G-1==oldgap
            counts['global_parent771_positive_branches']+=1
    return dict(counts)


def guards():
    rejected=0
    def reject(fn):
        nonlocal rejected
        try:fn()
        except (AssertionError,KeyError,TypeError):rejected+=1
        else:raise AssertionError('malformed caller accepted')
    for inline in (False,True):
        old=parent.build(inline_initial=inline)
        for key,value in [('source',old['source'][:-1]),('comparisons',[]),('unit_factors',[]),('auxiliaries',[]),('program_code','bad'),('history_global_unit',False)]:
            reject(lambda key=key,value=value:rewrite(dict(old,**{key:value})))
        for a in (False,True):
          for g in (False,True):
            p=build(inline_initial=inline,and_bounds=a,geometry_bounds=g)
            for key,value in [('source',p['source'][:-1]),('comparisons',[]),('positive_zero_bijection',not p['positive_zero_bijection']),('and_bounds',int(a)),('geometry_bounds',int(g))]:
              for api in (polynomial_source,degree_audit,ledger):
                reject(lambda key=key,value=value,api=api:api(dict(p,**{key:value})))
    for name in ('inline_initial','and_bounds','geometry_bounds'):reject(lambda name=name:build(**{name:1}))
    return rejected


def verify():
    forms=[]
    for inline in (False,True):
      for a in (False,True):
       for g in (False,True):
        p=build(inline_initial=inline,and_bounds=a,geometry_bounds=g);rows,out=polynomial_source(p);record=ledger(p)
        by={n:(u,v) for n,o,u,v in rows};need=set();todo=[out]
        while todo:
            n=todo.pop()
            if isinstance(n,str) and n in by and n not in need:need.add(n);todo.extend(by[n])
        assert need==by.keys()
        assert len(rows)==(771 if inline else 774)-2*a-2*g
        assert record['degree']['exact_degree']==(209782 if inline else 8672)+a*(18491 if inline else 746)+66*g
        record.update(inline_initial=inline,and_bounds=a,geometry_bounds=g,source=rows,output=out,
                      parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
                      source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest())
        forms.append(record)
    return dict(status='PASS_GPCP_POSITIVE_BOUND_UNITS767',forms=forms,source_audit=source_audit(),boundaries=boundary_audit(),
                rejected_callers=guards(),scope='Full positive surjection to771 with explicit paired-negative positive section. No bijection or off-zero polynomial identity. Complete programs/inputs and all supplied domains retained; finite tests do not materialize full Pell zeros.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print({k:v for k,v in result.items() if k not in ('forms','status')})
