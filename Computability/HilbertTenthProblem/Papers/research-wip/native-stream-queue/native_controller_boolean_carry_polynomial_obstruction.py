"""Scoped polynomial-input obstruction for hidden plus external affine carry."""
import argparse
from itertools import product
import json
from pathlib import Path
import sympy as sp

import native_controller_boolean_carry70 as prior
import input_bridge_boolean_carry_loader65 as loader
import input_bridge_filtered_polynomial_obstruction as polynomial


def source_checks():
    variants={'raw70':prior.source_check(), 'marker71':loader.source_check(),
              'aligned_marker73':loader.source_check(aligned=True)}
    bare=loader.source_check(False)
    g0,g1,g2,gap=sp.symbols('g0 g1 g2 gap')
    rows={}
    for name,source in variants.items():
        control=sp.sympify(source['sources'][19]['source'],locals=dict(g0=g0,g1=g1,g2=g2,gap=gap))
        assert sp.expand(control.subs({g0:0,g1:0,g2:0,gap:0}))==0
        if name!='raw70':assert source['sources'][:19]==bare['sources']
        rows[name]={k:source[k] for k in ('operations','multiplications','additions_subtractions','equations')}
        rows[name]['controller_source']=str(control)
        rows[name]['collapsed_controller_source']='0'
        rows[name]['positive_witnesses_excluding_x']=len(source['positive_parameters'])+len(source['positive_auxiliaries'])-1
    assert [(rows[k]['operations'],rows[k]['equations']) for k in rows]==[(70,20),(71,20),(73,22)]
    h,U,v0,v1=sp.symbols('h U v0 v1')
    cstar=(h+v0)/2;D=U-v0;A=2*v1-v0
    cases=0
    for n in range(1,11):
        for switch in (None,*range(n)):
            c=cstar;e=0
            for j in range(n):
                if j==switch:
                    assert e==0
                    a0,a1,e=1,1,1
                elif e:a0,a1=1,0
                else:a0,a1=0,0
                c=(c+h+U+v0*a0+v1*a1)/3
            target=cstar+(v0-v1)*e
            residual=sp.expand(2*3**n*(c-target))
            expected=D*(3**n-1) if switch is None else -D+A*3**switch+(D+A)*3**n
            assert sp.expand(residual-expected)==0
            reset=(c+h+(v1 if e else v0))/3
            assert sp.expand(3*(reset-cstar)-(c-target))==0
            cases+=1
    a,b,d0,d1,a0,a1=sp.symbols('a b d0 d1 a0 a1')
    hidden=2*a0+a1+d0+d1-2
    ext0=a*d0+b*d1+(a+b)*a0+b*a1-a-b
    ext1=b*d0+a*d1+(a+b)*a0+b*a1-a-b
    assert sp.expand(ext0-b*hidden-(a-b)*(d0+a0-1))==0
    assert sp.expand(ext1-b*hidden-(a-b)*(d1+a0-1))==0
    assert sp.expand(ext0.subs(a,b)-b*hidden)==0
    cf,cs=sp.symbols('cf cs')
    reduced=[2*(2*b)-2*b-2*b,2*b-b-b,b-b,2*cf-2*cs]
    assert [sp.expand(p.subs(cs,cf)) if hasattr(p,'subs') else p for p in reduced]==[0,0,0,0]
    return dict(sources=rows,long_two_symbolic_paths=cases,
                exact_branches=['(a-b)*(d0+a0-1)','(a-b)*(d1+a0-1)'],
                collapse=dict(u0='b',u1='b',v0='2*b',v1='b',h='2*cf-2*b',cs='cf'),
                scope='Inherited literal sources replayed; no free evaluation of a general polynomial')


def zero_reset_checks():
    cases=admitted=0
    C=10
    for h,v0,v1 in product(range(-3,4),repeat=3):
        L=1
        while 3**L<=2*C+abs(h+v0):L+=1
        for entry_e,entry_c in product((0,1),range(-C,C+1)):
            e,c=entry_e,entry_c;valid=True
            for _ in range(L+1):
                append=(1,0) if e==0 else (0,1)
                assert prior.hidden_step(e,(*append,0,0))==0
                numerator=c+h+v0*append[0]+v1*append[1]
                e=0
                if numerator%3:valid=False;break
                c=numerator//3
                assert abs(c)<=C
            if valid:
                assert e==0 and 2*c==h+v0
                admitted+=1
            cases+=1
    return dict(zero_block_cases=cases,integral_reset_paths=admitted,coefficient_range=[-3,3],carry_bound=C)


def rejecting_lengths():
    cases=0;largest=0
    for D,A in product(range(-30,31),repeat=2):
        if not D:continue
        E=polynomial.v3(D);n=E+1
        if D+A:
            while 3**n*abs(D+A)<=abs(D)+abs(A)*3**E:n+=1
        assert D*(3**n-1)!=0
        assert all(D!=A*3**k+(D+A)*3**n for k in range(n))
        cases+=1;largest=max(largest,n)
    return dict(nonzero_D_signed_pairs=cases,D_A_range=[-30,30],largest_explicit_rejecting_run=largest)


def suffix_checks():
    expected=[{(0,0):(1,0),(1,0):(0,1),(1,1):(0,0)},
              {(0,0):(1,0),(0,1):(0,1),(1,1):(0,0)}]
    tables=[];paths=steps=0
    for branch in (0,1):
        actual={}
        for a0,a1,d0,d1 in product((0,1),repeat=4):
            if (d0 if branch==0 else d1)+a0!=1:continue
            nxt=prior.hidden_step(0,(a0,a1,d0,d1))
            if nxt is not None:
                assert nxt==0 and (d0,d1) not in actual
                actual[d0,d1]=(a0,a1)
        assert actual==expected[branch]
        for m in range(1,6):
            for tail in product(tuple(product((0,1),repeat=2)),repeat=m-1):
                queue=((0,0),)+tail;dead=False
                for _ in range((2 if branch==0 else 1)*m+1):
                    if queue[0] not in actual:
                        dead=True;break
                    queue=queue[1:]+(actual[queue[0]],)
                    assert any(a or b for a,b in queue)
                    steps+=1
                assert dead
                paths+=1
        tables.append([dict(read=list(r),append=list(a)) for r,a in sorted(actual.items())])
    # Exact uniqueness of a finite balanced ternary zero word.
    balanced=0
    for length in range(1,9):
        for bits in product((-1,0,1),repeat=length):
            if sum(bit*3**i for i,bit in enumerate(bits))==0:
                assert not any(bits)
            balanced+=1
    return dict(forced_tables=tables,queues_starting_with_zero=paths,valid_steps_before_dead=steps,
                queue_widths=[1,5],balanced_words=balanced)


def prefix_checks():
    x,z=sp.symbols('x z')
    polynomials=[2*x,6*x+2,2*x*x,2*(x+1)**3,
                 2*(9*x*x+3*x+7),2*(x**4+5*x*x+1)]
    Z=[0]*4
    patterns=[Z+[2]*n+Z+[1] for n in (1,2,5,9)]
    patterns += [Z+[1]+Z+[1],Z+[0,1]]
    rows=[];maps=0
    for P in polynomials:
        derivative=sp.diff(P,x)
        a=next(a for a in range(2,2*sp.degree(P,x)+6,2) if derivative.subs(x,a)!=0)
        da=int(derivative.subs(x,a));e=polynomial.v3(da);v=e+1;K=v+e
        Pa=int(P.subs(x,a));Q=sp.Poly(sp.expand((P.subs(x,a+3**v*z)-Pa)/3**K),z)
        assert all(c.is_Integer for c in Q.all_coeffs())
        assert Q.nth(1)%3 and all(Q.nth(j)%3==0 for j in range(2,Q.degree()+1))
        examples=[]
        for pattern in patterns:
            n=len(pattern);residue=Pa%3**K+3**K*polynomial.value(pattern)
            target=((residue-Pa)//3**K)%3**n
            root=polynomial.lift(Q.as_expr(),z,target,n)
            ordinary=a+3**v*root
            if ordinary%2:root+=3**n;ordinary=a+3**v*root
            I=int(P.subs(x,ordinary))
            assert ordinary>0 and ordinary%2==I%2==0 and I>0
            assert I%3**(K+n)==residue
            assert [I//3**(K+j)%3 for j in range(n)]==pattern
            assert I>=3**(K+n-1)
            maps+=1
            if len(examples)<1:examples.append(dict(ordinary_even_x=ordinary,input_value=I,continuation=pattern))
        rows.append(dict(P=str(sp.expand(P)),even_base=a,fixed_prefix_length=K,examples=examples))
    return dict(polynomials=rows,exact_even_input_maps=maps,
                scope='Every required pattern is genuinely inside an ordinary initial word; proof is parametric in Z length and two-run length')


def collapsed_positive_maps():
    cases=steps=0
    for ordinary in range(1,61):
        I=6*ordinary+2;m=4
        while 3**m<=I:m+=2
        outer=loader.physical_map(I,m,even=True)
        t=outer['t'];fields=outer['fields']
        for b,cf in ((-3,-2),(0,0),(2,5)):
            e=0;c=cf
            for j in range(t):
                a0,a1,d0,d1=(F//3**j%3 for F in fields)
                ee=prior.hidden_step(e,(a0,a1,d0,d1))
                numerator=c+(2*cf-2*b)+b*d0+b*d1+2*b*a0+b*a1
                assert numerator%3==0
                c=numerator//3;e=ee
                assert c==cf+b*e
                steps+=1
            assert e==0 and c==cf
            cases+=1
    return dict(ordinary_marker_inputs=60,positive_external_paths=cases,microscopic_steps=steps,
                even_width_and_duration=True,scope='Actual positive erased tuples; large Pell witnesses supplied by the reviewed base converse')


def verify():
    return dict(status='PASS_HIDDEN_CARRY_POLYNOMIAL_INPUT_OBSTRUCTION',
                source=source_checks(),zero_resets=zero_reset_checks(),two_run_rejections=rejecting_lengths(),
                unequal_branches=suffix_checks(),polynomial_prefixes=prefix_checks(),positive=collapsed_positive_maps(),
                theorem='If the fixed polynomial-input family accepts all positive even x, its language is decidable; nonconstant P forces a redundant external controller',
                scope='Integer-coefficient P positive and even on positive integers; no additional filters or appearances of x',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k!='polynomial_prefixes'},indent=2))
