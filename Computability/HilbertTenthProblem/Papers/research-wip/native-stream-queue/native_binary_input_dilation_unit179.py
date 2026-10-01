#!/usr/bin/env python3
"""Paid norm-unit finalizers and positive projections for complete recoders.

The default radix-four source costs135 gates/15 comparisons/36 positive
witnesses; its integer-product polynomial costs179 operations.  The
positive graph is identical to the129 parent after explicit coordinate
bijections.  This is not an identity between the two old/new polynomials.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import native_binary_input_dilation129 as radix4
import native_binary_input_dilation130 as radix16
import gpcp_fixed_program_input_bridge as generic

execute=radix4.execute


def sort_source(source,inputs):
    known=set(inputs);pending=list(source);answer=[]
    assert len({r[0] for r in source})==len(source)
    while pending:
        following=[]
        for row in pending:
            name,_,a,b=row
            if all(not isinstance(v,str) or v in known for v in (a,b)):
                assert name not in known
                answer.append(row);known.add(name)
            else:following.append(row)
        assert len(following)<len(pending),'cyclic or missing source dependency'
        pending=following
    return answer


def rewrite(old,core_prefixes=('geo__','and__'),*,root_gaps=True,
            project_definitions=True,compute_length=True,strong_auxiliary=True):
    """Accept a literal compatible recoder or GPCP-boundary packet.

    The two prefixes identify geometry and prescribed-AND cores.  Keeping
    all three options false preserves the supplied positive coordinates.
    Projection includes q; compute_length additionally projects P.
    """
    assert len(core_prefixes)==2
    assert not compute_length or project_definitions
    assert not project_definitions or root_gaps
    gp,ap=core_prefixes
    rows={n:(n,op,a,b) for n,op,a,b in old['source']}
    deleted=set();changes={};added=[];removed_pairs=[];factors=[]
    renamed={};aliases={};factor_residuals=[];auxiliary_corrections={}
    for prefix in core_prefixes:
        n=lambda value:prefix+value
        norm_rows={
            'a_square':('*',n('a'),n('a')),'a4':('*',4,n('a')),
            'a4m5':('+',n('a4'),3),'A':('+',n('a_square'),n('a4m5')),
            'c2':('*',n('c'),n('c')),'Ac2':('*',n('A'),n('c2')),
            'L15':('*',n('d'),n('d')),'ic2':('*',n('i'),n('c2')),
            'ic22':('*',n('ic2'),n('ic2')),'H2':('*',n('H17'),n('H17')),
            'aux_y2':('*',n('y_aux'),n('y_aux')),
            'aux_square_gap':('-',n('H2'),n('aux_y2')),
            'L17':('*',n('ic22'),n('aux_square_gap'))}
        assert all(rows[n(key)][1:]==value for key,value in norm_rows.items())
        main=(n('L15'),n('R15'));aux=(n('L17'),n('P17'))
        assert rows[n('R15')]==(n('R15'),'+',n('Ac2'),1)
        assert rows[n('P17')]==(n('P17'),'-',1,n('aux_y2'))
        for private in (n('R15'),n('P17')):
            assert not any(private in (a,b) for _,_,a,b in old['source'])
        changes[n('R15')]=(n('R15'),'-',n('L15'),n('Ac2'))
        changes[n('P17')]=(n('P17'),'+',n('L17'),n('aux_y2'))
        if strong_auxiliary:
            assert rows[n('L16')]==(n('L16'),'*',n('f'),n('f'))
            assert rows[n('f_square_minus_one')]==(n('f_square_minus_one'),'-',n('L16'),1)
            assert rows[n('R16')]==(n('R16'),'*',n('A'),n('f_square_minus_one'))
            assert (n('ic22'),n('R16')) in old['comparisons']
            changes[n('L17')]=(n('L17'),'*',n('R16'),n('aux_square_gap'))
            auxiliary_corrections[n('P17')]=dict(pair=(n('ic22'),n('R16')),gap=n('aux_square_gap'))
        removed_pairs += [main,aux];factors += [n('R15'),n('P17')]
        factor_residuals += [(main,1),(aux,1)]
        if root_gaps:
            expected={
                n('tauplus1'):('+',n('tau'),1),
                n('R9'):('*',n('tau'),n('tauplus1')),
                n('UM2'):('*',n('UM'),n('UM')),
                n('scaled_norm_coefficient'):('+',n('UM2'),n('wn2')),
                n('ratio_product2'):('*',n('ksn2'),n('ksn2')),
                n('L9'):('*',n('scaled_norm_coefficient'),n('ratio_product2'))}
            assert all(rows[key][1:]==value for key,value in expected.items())
            private=set(expected)
            assert all({name for name,_,a,b in old['source'] if key in (a,b)}<=private for key in private)
            deleted |= private
            renamed[n('tau')]=n('tau_gap')
            added += [(n('gap_square'),'*',n('tau_gap'),n('tau_gap')),
                      (n('root_base'),'*',n('UM'),n('ksn2')),
                      (n('signed_gap'),'-',n('tau_gap'),n('k')),
                      (n('gap_cross'),'*',n('root_base'),n('signed_gap')),
                      (n('four_cross'),'*',4,n('gap_cross')),
                      (n('first_unit'),'+',n('gap_square'),n('four_cross'))]
            first=(n('L9'),n('R9'))
            removed_pairs.append(first);factors.append(n('first_unit'))
            factor_residuals.append((first,-4))
    checksum=(ap+'bs_q',ap+'q')
    assert rows[ap+'bs_q']==(ap+'bs_q','+',ap+'bs_Q',1)
    assert not any(ap+'bs_q' in (a,b) for _,_,a,b in old['source'])
    changes[ap+'bs_q']=(ap+'bs_q','-',ap+'q',ap+'bs_Q')
    removed_pairs.append(checksum);factors.append(ap+'bs_q')
    factor_residuals.append((checksum,-1))
    if project_definitions:
        for prefix in core_prefixes:
            odd='geometry_odd' if prefix==gp else 'bs_odd'
            n=lambda value:prefix+value
            positive_rows={
                'R10b':('+',n('eta'),n('zeta')),
                'R10a':('+',n('ksn2'),n('eta')),
                'R12':('+',n('UM'),n('sn2')),
                'R14':('+',n('D1'),n('gam')),
                'D1':('+',n('wn2'),n('cam2')),
                'cam2':('*',n('c'),n('a')),
                'gam':('*',n('ga'),n('a4m5'))}
            assert all(rows[n(key)][1:]==value for key,value in positive_rows.items())
            aliases.update({prefix+'k':prefix+'R10b',prefix+'c':prefix+'R10a',
                            prefix+'a':prefix+'R12',prefix+'d':prefix+'R14',
                            prefix+'s':prefix+odd})
        aliases[ap+'r']=ap+'bs_packed'
        aliases['q']='input_bound'
        if compute_length:aliases['P']='repunit_P'
        for var,value in aliases.items():
            pair=(var,value) if (var,value) in old['comparisons'] else (value,var)
            assert pair in old['comparisons']
            removed_pairs.append(pair)
    assert len(set(removed_pairs))==len(removed_pairs)
    assert all(pair in old['comparisons'] for pair in removed_pairs)
    source=[changes.get(n,(n,op,a,b)) for n,op,a,b in old['source'] if n not in deleted]+added
    for i,factor in enumerate(factors[1:]):
        left=factors[0] if i==0 else f'recoder_unit_product{i-1}'
        source.append((f'recoder_unit_product{i}','*',left,factor))
    unit=source[-1][0]
    resolve=lambda value:aliases.get(value,value)
    source=[(n,op,resolve(a),resolve(b)) for n,op,a,b in source]
    pairs=[(resolve(a),resolve(b)) for a,b in old['comparisons'] if (a,b) not in removed_pairs]
    pairs.append((unit,1))
    aux=[renamed.get(n,n) for n in old['auxiliaries'] if n not in aliases]
    source=sort_source(source,old['parameters']+aux)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(source)==old['operations']+len(factors)-1
    assert counts=={'M':old['multiplications']+len(factors)-1,'A':old['additions_subtractions']}
    assert len(pairs)==len(old['comparisons'])-len(removed_pairs)+1
    return dict(old,source=source,comparisons=pairs,auxiliaries=aux,operations=len(source),
                multiplications=counts['M'],additions_subtractions=counts['A'],
                equations=len(pairs),witnesses=len(aux),core_prefixes=list(core_prefixes),
                root_gaps=root_gaps,project_definitions=project_definitions,
                compute_length=compute_length,strong_auxiliary=strong_auxiliary,
                auxiliary_strong_corrections=auxiliary_corrections,
                projection_aliases=aliases,renamed_coordinates=renamed,
                unit_factors=factors,unit_register=unit,
                factor_residuals=[dict(pair=pair,multiplier=k) for pair,k in factor_residuals],
                removed_parent_comparisons=removed_pairs,
                parent_parameters=old['parameters'],parent_auxiliaries=old['auxiliaries'],
                parent_operations=old['operations'],parent_equations=len(old['comparisons']))


def build(width=2,**options):
    old=radix4.build() if width==2 else generic.recoder(width)
    return rewrite(dict(old,width=width),**options)


def polynomial_source(packet,*,sum_of_squares=False):
    source=list(packet['source']);unit=packet['unit_register'];last=None
    pairs=packet['comparisons'] if sum_of_squares else [p for p in packet['comparisons'] if p!=(unit,1)]
    for i,(a,b) in enumerate(pairs):
        r,s=f'unit_residual{i}',f'unit_square{i}'
        source += [(r,'-',a,b),(s,'*',r,r)]
        if last is None:last=s
        else:
            nxt=f'unit_sum{i}';source.append((nxt,'+',last,s));last=nxt
    assert last is not None
    if not sum_of_squares:
        source += [('unit_outer_positive','+',last,1),
                   ('unit_outer_product','*',unit,'unit_outer_positive'),
                   ('unit_output','-','unit_outer_product',1)]
        last='unit_output'
    assert len(source)==packet['operations']+3*packet['equations']-1
    return source,last


def lift(packet,values):
    """New to old coordinates; tau may be half-integral away from zeros."""
    env=execute(packet['source'],values)
    old={name:values[name] for name in packet['parent_parameters']+packet['parent_auxiliaries']
         if name in values}
    old.update({var:env[target] for var,target in packet['projection_aliases'].items()})
    for before,after in packet['renamed_coordinates'].items():
        prefix=before[:-3]
        old[before]=env[prefix+'root_base']+Fraction(values[after]-1,2)
    return old


def project(packet,old,oldenv):
    """Old to new coordinates; positivity of each gap is proved at zeros."""
    values={name:old[name] for name in packet['parameters']+packet['auxiliaries'] if name in old}
    for before,after in packet['renamed_coordinates'].items():
        prefix=before[:-3]
        values[after]=2*old[before]+1-2*oldenv[prefix+'UM']*oldenv[prefix+'ksn2']
    return values


def audit_identity(old,packet,values):
    source,out=polynomial_source(packet);env=execute(source,values)
    restored=lift(packet,values);before=execute(old['source'],restored)
    rr={(a,b):before[a]-before[b] for a,b in old['comparisons']}
    product=1
    for record,name in zip(packet['factor_residuals'],packet['unit_factors']):
        expected=1+record['multiplier']*rr[tuple(record['pair'])]
        if name in packet['auxiliary_strong_corrections']:
            correction=packet['auxiliary_strong_corrections'][name]
            expected-=rr[tuple(correction['pair'])]*before[correction['gap']]
        assert env[name]==expected
        product*=expected
    assert env[packet['unit_register']]==product
    omitted=set(map(tuple,packet['removed_parent_comparisons']))
    other=[r for pair,r in rr.items() if pair not in omitted]
    assert [env[a]-env[b] for a,b in packet['comparisons'][:-1]]==other
    assert env[out]==product*(1+sum(r*r for r in other))-1
    factors=set(packet['unit_factors'])
    if packet['strong_auxiliary']:factors.update(prefix+'L17' for prefix in packet['core_prefixes'])
    assert all(env[name]==before[name] for name,_,_,_ in packet['source']
               if name in before and name not in factors)
    assert project(packet,restored,before)==values
    if all(v>0 for v in values.values()):assert all(v>0 for v in restored.values())


def degree_audit(packet):
    t=sp.Symbol('t');names=packet['parameters']+packet['auxiliaries']
    weights={n:1+i%3 for i,n in enumerate(names)}
    for n in packet['renamed_coordinates'].values():weights[n]=1
    for prefix in packet['core_prefixes']:
        if prefix+'k' in weights:weights[prefix+'k']=3
    values={n:sp.Poly(weights[n]*t+i+1,t) for i,n in enumerate(names)}
    # Evaluate separate factors, not the expensive expanded final product.
    source=[r for r in packet['source'] if not r[0].startswith('recoder_unit_product')]
    env=execute(source,values)
    factors=[env[n] for n in packet['unit_factors']]
    outer=[env[a]-(env[b] if isinstance(b,str) else b) for a,b in packet['comparisons'][:-1]]
    ud=sum(p.degree() for p in factors);ut=1
    for p in factors:ut*=p.LC()
    od=max(p.degree() for p in outer);ot=sum(p.LC()**2 for p in outer if p.degree()==od)
    assert ut and ot
    width=packet.get('width',4)
    expected=(27*width+140 if packet['compute_length'] else
              104+2*max(18,width+1) if packet['project_definitions'] else
              49+2*max(7,width+1) if packet['root_gaps'] else
              30+2*max(20,width+1))
    if packet['strong_auxiliary']:expected-=8 if packet['project_definitions'] else 4
    assert ud+2*od==expected,(width,ud,od,expected)
    top=int(ut*ot);encoded=str(top).encode()
    return dict(exact_degree=ud+2*od,unit_degree=ud,outer_residual_degree=od,
                alternative_SOS_degree=2*max(ud,od),
                unit_factor_degrees=[p.degree() for p in factors],
                nonzero_top_sign=1 if top>0 else -1,
                top_sha256=hashlib.sha256(encoded).hexdigest())


def sign_checks():
    count=0
    for a in range(8):
      for d in range(4):
       for c in range(4):
        assert (d*d-(a*a+4*a+3)*c*c)%4!=3;count+=1
    for T in range(8):
      for u in range(4):
       for y in range(4):
        assert (T*T*(u*u-y*y)+y*y)%4!=3;count+=1
    for g in range(8):
      for V in range(4):
       for k in range(4):
        assert (g*g+4*V*k*(g-k))%4!=3;count+=1
    for a in range(4):
      for f in range(4):
       for u in range(4):
        for y in range(4):
         K=(a*a+4*a+3)*(f*f-1)
         assert K%4 in (0,1) and (K*(u*u-y*y)+y*y)%4!=3;count+=1
    pell_cases=0
    for V in range(1,17):
      for index in range(1,9):
        chi,k=radix4.geometry.pell(2*V+1,index)
        tau=(chi-1)//2;g=chi-2*V*k
        assert tau>0 and g>0 and g%2==1
        assert V*(V+1)*k*k==tau*(tau+1)
        assert g*g+4*V*k*(g-k)==1
        assert V*k+(g-1)//2==tau;pell_cases+=1
    return dict(modulo_four_cases=count,positive_first_root_bijections=pell_cases)


def verify():
    rng=random.Random(179129);records=[];cases=half=0;example=None
    options=[dict(root_gaps=False,project_definitions=False,compute_length=False),
             dict(project_definitions=False,compute_length=False),
             dict(compute_length=False),dict()]
    for width in (2,4,8,24):
      old=radix4.build() if width==2 else generic.recoder(width)
      for opt in options:
       for strong in (False,True):
        packet=rewrite(dict(old,width=width),strong_auxiliary=strong,**opt);source,out=polynomial_source(packet)
        counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
        for case in range(96):
            positive=case<64
            values={n:rng.randrange(1,6) if positive else rng.randrange(-2,4)
                    for n in packet['parameters']+packet['auxiliaries']}
            audit_identity(old,packet,values);cases+=1
            half+=any(isinstance(v,Fraction) and v.denominator==2 for v in lift(packet,values).values())
        degree=degree_audit(packet)
        records.append(dict(width=width,root_gaps=packet['root_gaps'],
            project_definitions=packet['project_definitions'],compute_length=packet['compute_length'],
            strong_auxiliary=strong,
            certificate=packet['operations'],certificate_M=packet['multiplications'],
            certificate_A=packet['additions_subtractions'],equations=packet['equations'],
            witnesses=packet['witnesses'],polynomial=len(source),M=counts['M'],A=counts['A'],**degree))
        if width==2 and packet['compute_length']:
            assert (packet['operations'],packet['equations'],packet['witnesses'],len(source),counts['M'],counts['A'])==(135,15,36,179,86,93)
            example=dict(packet,polynomial_finalizer=source[packet['operations']:],polynomial_output=out)
    boundary=generic.build(4);p=rewrite(boundary);s,o=polynomial_source(p)
    for _ in range(96):
        v={n:rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
        audit_identity(boundary,p,v);cases+=1
    assert (p['operations'],p['equations'],p['witnesses'],len(s))==(142,17,37,192)
    return dict(status='PASS_NATIVE_BINARY_INPUT_DILATION_UNIT179',records=records,
                source_example=example,arbitrary_complete_output_identities=cases,
                half_integral_offzero_lifts=half,signs=sign_checks(),
                boundary_example=dict(certificate=142,equations=17,witnesses=37,polynomial=192,
                                      **degree_audit(p)),
                scope='Exact positive graph through explicit coordinate bijections. Same-coordinate '
                      'unit option also provided. No unchanged full-polynomial identity or full '
                      'astronomical native zero is claimed; generic boundary tile history remains unpaid.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
