#!/usr/bin/env python3
"""Exact scoped counterexample to replacing n=q^4 by n=q^2 in universal89.

The actual empty-set compiler layout has huge exponents. A symbolic
base-B carry calculation proves its population count for all d>=4,
where B=2^d, including the genuine fixed-index threshold. No giant
radix or Pell witness is materialized. See EXPLORATION_BINARY_SCALE_Q2.md.
"""
from collections import defaultdict
from pathlib import Path
import json
import sympy as sp
import round37_1980_binary_product_encoding as old
import round38_1980_binary_product_certificate as certificate

OUT=Path(__file__).with_suffix('.json')

def sparse_pc(events, intervals, B, end):
    changes=defaultdict(int)
    for a,b,k in intervals:
        changes[a]+=k
        changes[b]-=k
    points=sorted(set(events)|set(changes)|{end})
    pos=carry=bg=pop=0
    digits={}
    def gap(length, carry, bg):
        pc=0
        while length:
            c,d=divmod(carry+bg*(B-2),B)
            if c==carry:
                pc+=length*d.bit_count()
                return pc,c
            pc+=d.bit_count()
            carry=c
            length-=1
        return pc,carry
    for p in points:
        pc,carry=gap(p-pos,carry,bg)
        pop+=pc
        bg+=changes[p]
        carry,digit=divmod(carry+bg*(B-2)+events.get(p,0),B)
        pop+=digit.bit_count()
        digits[p]=digit
        pos=p+1
    assert bg==0 and carry==0
    return pop,digits

def case(layout,d,x=1,g=1):
    B=1<<d
    H0=B//2
    b=B-H0-1
    ell={p:1 for p in layout['indicator']}
    e={p:c for p,c in layout['e_coeff'].items() if c}
    sigma={p:c*(x+g)**2 for p,c in layout['D'].items()}
    L=1<<(3*layout['K']+2).bit_length()
    events=defaultdict(int)
    def add(poly,shift,m):
        for p,c in poly.items():events[p+shift]+=m*c
    S={0:g}
    add(S,4*L,1);add(S,2*L,-1)
    add(sigma,5*L,1);add(sigma,3*L,-1)
    add(ell,6*L,1);add(ell,4*L,-1)
    add(e,7*L,1);add(e,5*L,-1)
    add(ell,5*L,B-2);add(ell,L,-(B-2))
    add(ell,4*L,-b);add(ell,0,b)
    pc,_=sparse_pc(events,[(2*L,4*L,-1),(6*L,8*L,1)],B,8*L)
    return dict(d=d,x=x,g=g,L=L,K=layout['K'],population=pc,threshold=4*L*d,
                margin=pc-4*L*d,parity=(-events[0])%2)

def empty_layout():
    # Substitute precisely the one ordinary zero row inside the inherited
    # compiler. Restore its function immediately; no file or global process
    # state is altered. The row checks below verify both compiled signs.
    original=old.polynomial
    def contradiction(*terms):
        if terms==((2,'zero','delta'),):
            return original((2,'delta','dc'))
        return original(*terms)
    old.polynomial=contradiction
    try:
        layout=old.make_layout()
    finally:
        old.polynomial=original
    expected=old.expand_logical(original((2,'delta','dc')),layout['groups'])
    rows=dict(layout['rows'])
    assert rows['zero+']==expected
    assert rows['zero-']=={monomial:-value for monomial,value in expected.items()}
    return layout

def formal_case(layout):
    # A digit coefficient is (a,c), denoting a*Q+c, Q=B/2=2^(d-1).
    # All carry decisions stabilize whenever Q exceeds the recorded offsets.
    L=1<<(3*layout['K']+2).bit_length()
    events=defaultdict(lambda:[0,0])
    ell={p:1 for p in layout['indicator']}
    e={p:c for p,c in layout['e_coeff'].items() if c}
    sigma={p:4*c for p,c in layout['D'].items()}
    def add(poly,shift,a,c):
        for p,v in poly.items():
            events[p+shift][0]+=a*v
            events[p+shift][1]+=c*v
    add({0:1},4*L,0,1);add({0:1},2*L,0,-1)
    add(sigma,5*L,0,1);add(sigma,3*L,0,-1)
    add(ell,6*L,0,1);add(ell,4*L,0,-1)
    add(e,7*L,0,1);add(e,5*L,0,-1)
    add(ell,5*L,2,-2);add(ell,L,-2,2)
    add(ell,4*L,-1,1);add(ell,0,1,-1)
    changes={2*L:-1,4*L:1,6*L:1,8*L:-1}
    points=sorted(set(events)|set(changes)|{8*L})
    maxoffset=0
    count=0
    category_counts=defaultdict(int)
    def digit(a,c):
        nonlocal maxoffset,count
        maxoffset=max(maxoffset,abs(c))
        count+=1
        h,odd=divmod(a,2)
        if odd:
            result=(h,0,1+c.bit_count()) if c>=0 else (h,1,-1-(-c-1).bit_count())
        else:
            result=(h,0,c.bit_count()) if c>=0 else (h-1,1,-(-c-1).bit_count())
        category_counts[str((a,c,result))]+=1
        return result
    pos=carry=bg=md=mc=0
    for p in points:
        gap=p-pos
        while gap:
            nxt,ad,ac=digit(2*bg,carry-2*bg)
            if nxt==carry:
                md+=gap*ad;mc+=gap*ac;gap=0
            else:
                md+=ad;mc+=ac;gap-=1;carry=nxt
        bg+=changes.get(p,0)
        a,c=events[p]
        carry,ad,ac=digit(a+2*bg,c+carry-2*bg)
        md+=ad;mc+=ac
        pos=p+1
    assert bg==carry==0
    return dict(L=L,K=layout['K'],population_d=md,population_constant=mc,
                excess_d=md-4*L,excess_constant=mc,maxoffset=maxoffset,steps=count,
                events=len(events),normalization_categories=dict(sorted(category_counts.items())),
                formula='popcount(r) = population_d*d + population_constant for every 2^(d-1)>maxoffset')


def verify_source():
    assert ('q4','*','q2','q2') in certificate.SCHEDULE
    schedule=[row for row in certificate.SCHEDULE if row[0]!='q4']
    equalities=[('n','q2') if row==('n','q4') else row for row in certificate.EQUALITIES]
    env=dict(certificate.SYM)
    histogram=certificate.baseline.run_schedule(schedule,env)
    source=certificate.source_residuals()
    s=certificate.SYM
    source[5]=s['n']-s['q']**2
    A,B=s['a']+2,s['H']+s['b']+2
    u=2*s['r']+1+s['j']*s['c']
    corrections={2:-s['la']*source[3],16:source[15]*(u*u-s['y_aux']**2),
                 17:source[3]*(s['ka']+s['rho']*(source[3]-2*(A-B)))}
    comparisons=[]
    for index,((left,right),residual) in enumerate(zip(equalities,source)):
        actual=sp.expand(env[left]-env[right])
        correction=corrections.get(index,0)
        if sp.expand(actual-residual-correction)==0:
            sign=1
        else:
            assert correction==0 and sp.expand(actual+residual)==0
            sign=-1
        comparisons.append(dict(index=index,equality=[left,right],sign=sign,
                                source=sp.sstr(sp.expand(residual)),correction=sp.sstr(sp.expand(correction))))
    primitives,counts=certificate.verify_primitives(schedule,env)
    assert len(primitives)==88 and counts=={'+':42,'*':46}
    assert len(equalities)==22 and len(certificate.NAMES)-len(certificate.PARAMETERS)==34
    assert all('q4' not in row[2:] for row in schedule)
    for index,(new,prior) in enumerate(zip(source,certificate.source_residuals())):
        assert sp.expand(new-prior-(s['q']**4-s['q']**2 if index==5 else 0))==0
    return dict(operations=88,multiplications=46,additions=42,positive_unknowns=34,
                equations=22,histogram=histogram,source_comparisons=comparisons,
                changed_source_indices=[5],removed_instruction=['q4','*','q2','q2'],
                replacement_equality=['n','q2'])


def dense_crosschecks():
    rows=[]
    for v,s,w in ((1,3,4),(2,5,6),(3,6,7)):
        indicator={v,s,s+1,s+2}
        D={s-1:1,s:-1,w+3:1}
        ecoeff={p:int(p in indicator)+D.get(p,0) for p in indicator|set(D)}
        toy=dict(K=max(indicator|set(D))+1,indicator=indicator,D=D,e_coeff=ecoeff)
        formal=formal_case(toy)
        for d in (4,5,8,12):
            B=1<<d
            q=B**formal['L'];n=q*q;theta=B-2;b=B//2-1
            ell=sum(B**p for p in indicator)
            ep=sum(c*B**p for p,c in ecoeff.items())
            sigma=4*sum(c*B**p for p,c in D.items())
            la=(q*q-1)//(B-1)
            S=1+q*sigma+q*q*(ell+ep*q)
            T=q*q*theta*la+ell*(theta*q-b)
            r=S*(n*n-n)+T*(n*n-1)
            concrete=case(toy,d)
            expected=formal['population_d']*d+formal['population_constant']
            assert r>0 and r.bit_count()==expected==concrete['population']
            rows.append(dict(d=d,L=formal['L'],r_bits=r.bit_length(),population=expected))
    return rows


def verify():
    layout=empty_layout()
    symbolic=old.symbolic_checks(layout)
    formal=formal_case(layout)
    assert formal['excess_d']==1201 and formal['excess_constant']==-99
    assert formal['maxoffset']==6
    d=2*formal['L']+4
    cstar=len(layout['indicator'])+1
    other_threshold=max(128*max(1,symbolic['D1'])*cstar*cstar,3*formal['L'],1024)
    assert d-1>2*formal['L']+2 and d-1>=other_threshold.bit_length()
    assert formal['excess_d']*d+formal['excess_constant']>0
    rows=[]
    for d in [4,8,16,32,64]:
        row=case(layout,d)
        assert row['population']==formal['population_d']*d+formal['population_constant']
        rows.append(row)
    return dict(status='PASS',source=verify_source(),
                scope='Full scoped unsoundness theorem for only n=q^2 replacing n=q^4 in universal89; not a lower bound on arbitrary encodings',
                empty_index_compiler=symbolic,
                contradictory_row='Both signs of 2*delta*delta_copy=0, with delta_copy=delta and forced delta=1',
                symbolic_population=formal,
                fixed_threshold=dict(d='2*L+4',H0='2^(d-1)',B='2^d',cstar=cstar,
                                     nonexponential_threshold=other_threshold,threshold_verified_symbolically=True),
                numerical_sparse_crosschecks=rows,dense_crosschecks=dense_crosschecks(),
                false_input=1,code_gap=1,coordinate_sum=2,product='sigma=4*D(B)',
                full_positive_pell_extension='Proved constructively in the note at the actual even r; no failed preliminary soundness bound is used',
                giant_radix_or_Pell_coordinates_materialized=False)


if __name__=='__main__':
    result=verify()
    OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(result['status'],result['source']['operations'],'source operations;',
          'population excess',result['symbolic_population']['excess_d'],'*d',
          result['symbolic_population']['excess_constant'])
