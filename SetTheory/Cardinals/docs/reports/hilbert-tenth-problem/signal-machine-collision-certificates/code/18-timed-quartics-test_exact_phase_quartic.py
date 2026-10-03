#!/usr/bin/env python3
"""Finite exact regressions; the theorem, not finite testing, proves completeness."""
from dataclasses import FrozenInstanceError
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import random
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from test_binary_expanding_shuttle import step
from exact_phase_quartic import Poly,Chart,Certificate,compile_charts,binary_shuttle_charts,uniform_binary_shuttle,uniform_binary_witness


COUNTS={}
def bump(key,n=1):
    COUNTS[key]=COUNTS.get(key,0)+n


def reject(thunk):
    try:
        thunk()
    except (TypeError,ValueError):
        bump('malformed_input_rejections')
    else:
        raise AssertionError('malformed input was accepted')


def chart_value(chart,z):
    values=tuple(p(z) for p in chart.outputs)
    assert all(v.denominator==1 for v in values)
    return tuple(v.numerator for v in values)


def pooled_external(cert,w):
    # Independently evaluate constant-only homogenization, rather than using
    # the compiled expression, so full witness cube tests also audit lifting.
    out=[Fraction(0)]*cert.external_count
    for i,c in enumerate(cert.charts):
        z=tuple(w[v-cert.external_count] for v in cert.layouts[i][0])
        for k,p in enumerate(c.outputs):
            constant=p((0,)*c.parameters)
            out[k]+=p(z)-constant+constant*w[i]
    assert all(v.denominator==1 for v in out)
    return tuple(v.numerator for v in out)


def admissible_witness(cert,w):
    b=len(cert.charts)
    if sum(w[:b])!=1:
        return False
    i=w[:b].index(1)
    c=cert.charts[i]
    z=tuple(w[v-cert.external_count] for v in cert.layouts[i][0])
    try:
        return cert.witness(i,z)==w
    except ValueError:
        return False


def orbit_tests():
    for d in range(7,15):
        charts=binary_shuttle_charts(d)
        certificates=[compile_charts(charts,mode) for mode in ('products','sos')]
        for cert in certificates:
            assert len(cert.witness_names)==8
            assert cert.expression.degree==4
            assert len(cert.residuals)==(10 if cert.mode=='sos' else 8)
            assert len(cert.nonnegative_products)==(0 if cert.mode=='sos' else 2)
        c={0,3,4,d}
        time=0
        for n in range(21):
            for i,chart in enumerate(charts):
                for j in range(d+n-5):
                    value=chart_value(chart,(n,j))
                    assert value==(time,*sorted(c)),(d,n,j,value,c)
                    for cert in certificates:
                        w=cert.witness(i,(n,j))
                        assert cert.evaluate(value,w)==0
                        # Every external coordinate is actually constrained.
                        if n<2:
                            for k in range(5):
                                wrong=list(value); wrong[k]+=1
                                assert cert.evaluate(wrong,w)>0
                                bump('wrong_output_rejections')
                    c=step(c);time+=1
                    bump('binary_direct_orbit_states')
        expected=21*21+(2*d-11)*21
        assert time==expected


def full_cube_tests():
    charts=binary_shuttle_charts(7)
    for mode in ('products','sos'):
        cert=compile_charts(charts,mode)
        roots={}
        for w in product(range(3),repeat=8):
            external=pooled_external(cert,w)
            value=cert.evaluate(external,w)
            assert value>=0
            assert (value==0)==admissible_witness(cert,w)
            if value==0:
                assert external not in roots
                roots[external]=w
            bump('full_witness_cube_evaluations')
        assert len(roots)==14
    # B=0, B=1, rational time, domain equalities, and correctly cleared rational
    # affine inequality. This domain says n>=1; its canonical slack is n-1.
    n=Poly.var(1,0)
    one=Chart('triangular',1,(n*(n+1)*Fraction(1,2),n),((n-1)*Fraction(1,2),),())
    for mode in ('products','sos'):
        cert=compile_charts([one],mode)
        for w in product(range(5),repeat=3):
            z=w[1]
            external=(z*(z+1)//2,z)
            assert (cert.evaluate(external,w)==0)==(w==(1,z,z-1) and z>=1)
            bump('rational_single_chart_evaluations')
        empty=compile_charts([],mode,external_count=2)
        assert empty.evaluate((0,-1),())==1
        fixed=Chart('equalities',1,(n,),(),(n-2,))
        fixedcert=compile_charts([fixed],mode)
        assert fixedcert.evaluate((2,),fixedcert.witness(0,(2,)))==0
        reject(lambda:fixedcert.witness(0,(1,)))
    # Off-branch variables really need gates. If both chart variables are
    # allowed to contribute, one-hot output 2 would have two witnesses.
    evens=Chart('even',1,(2*n,))
    odds=Chart('odd',1,(2*n+1,))
    cert=compile_charts((evens,odds),'products')
    false=(1,0,0,1)
    assert pooled_external(cert,false)==(2,)
    assert all(r((2,)+false)==0 for r in cert.residuals)
    assert cert.evaluate((2,),false)>0
    bump('missing_gate_counterexamples')


def moving_frame_and_encoding_tests():
    for delta in (-3,2):
        charts=[]
        for c in binary_shuttle_charts(7):
            t=c.outputs[0]
            charts.append(Chart(c.name,2,(t,*(x+delta*t for x in c.outputs[1:])),c.inequalities))
        for mode in ('products','sos'):
            cert=compile_charts(charts,mode)
            for n in range(5):
                for i,c in enumerate(charts):
                    for j in range(n+2):
                        external=chart_value(c,(n,j))
                        assert cert.evaluate(external,cert.witness(i,(n,j)))==0
                        assert all(external[k]<external[k+1] for k in range(1,4))
                        bump('quadratic_moving_frame_checks')
            rng=random.Random(4181)
            for _ in range(50):
                w=tuple(rng.randrange(10**8) for _ in cert.witness_names)
                y=tuple(rng.randrange(-10**12,10**12) for _ in range(5))
                assert cert.evaluate(y,w)>0
                bump('large_exact_nonnegativity_checks')
    for mode in ('products','sos'):
        minusone=compile_charts([Chart('minus_one',0,(Poly.const(0,-1),))],mode)
        roots=[]
        for plus,minus in product(range(5),repeat=2):
            gate=plus*minus
            canonical=minusone.evaluate((plus-minus,),(1,))+(gate*gate if mode=='sos' else gate)
            if canonical==0: roots.append((plus,minus))
            bump('canonical_signed_encoding_checks')
        assert roots==[(0,1)]
        assert minusone.evaluate((-1,),(1,))==0
        # Merely substituting the difference would wrongly admit (1,2).
        assert minusone.evaluate((1-2,),(1,))==0


def mutation_and_type_tests():
    powers=[1]
    raw=[[powers,2]]
    p=Poly(1,raw)
    powers[0]=4;raw[0][1]=2.0;raw.append([[0],1])
    assert p((3,))==6 and p.degree==1
    outs=[p];ineq=[p-2]
    c=Chart('snapshot',1,outs,ineq)
    outs.append(p*p);ineq.clear()
    assert len(c.outputs)==len(c.inequalities)==1
    charts=[c];cert=compile_charts(charts);charts.clear()
    assert len(cert.charts)==1
    assert cert.evaluate((2,),cert.witness(0,(1,)))==0
    try:
        p.terms=()
    except FrozenInstanceError:
        bump('immutability_checks')
    else:
        raise AssertionError('mutable polynomial')
    bump('immutability_checks',4)
    malformed=[
      lambda:Poly(True,()),lambda:Poly(1,[([True],1)]),
      lambda:Poly(1,[([-1],1)]),lambda:Poly(1,[([1],True)]),
      lambda:Poly(1,[([1],0.5)]),lambda:Poly(1,[([1,0],1)]),
      lambda:Chart('bad',True,(p,)),lambda:Chart('bad',1,(p*p*p,)),
      lambda:Chart('bad',1,(p,),inequalities=(p*p,)),
      lambda:compile_charts([],external_count=True),
      lambda:compile_charts([c],external_count=1.0),
      lambda:cert.evaluate((True,),(1,1,0)),
      lambda:cert.evaluate((2,),(True,1,0)),
      lambda:cert.evaluate((2,),(1,1.0,0)),
      lambda:cert.evaluate((2,),(1,-1,0)),
      lambda:cert.witness(True,(1,)),lambda:cert.witness(0,(True,)),
      lambda:cert.witness(0,(1.0,)),lambda:cert.witness(0,(-1,)),
      lambda:binary_shuttle_charts(True),lambda:binary_shuttle_charts(7.0),
      lambda:binary_shuttle_charts(6),lambda:p((3.0,)),
      lambda:Certificate((),True,(),(),(),(),Poly.const(0,0),'sos'),
      lambda:Certificate((),0,(),(),(),(),Poly.const(0,Fraction(1,2)),'sos'),
    ]
    for case in malformed:
        reject(case)
    # A previously valid integer invocation cannot cause bool/float aliases
    # to bypass checking; no value-keyed memoization occurs before validation.
    assert cert.evaluate((2,),[1,1,0])==0
    reject(lambda:cert.evaluate((2.0,),[1,1,0]))


def sorting_refinement_test():
    # Two indexed sites exchange order between discrete times 0 and 1.
    # Sorting is a finite disjoint affine refinement, even without assuming
    # a permanent component order. Labels travel with source site indices.
    for n in range(10):
        sites=(n,1-n)
        accepted=[]
        if sites[1]-sites[0]-1>=0: accepted.append(((0,1),sites))
        if sites[0]-sites[1]-1>=0: accepted.append(((1,0),sites[::-1]))
        assert len(accepted)==1 and accepted[0][1]==tuple(sorted(sites))
        bump('affine_sorting_refinement_checks')


def uniform_family_tests():
    for mode in ('products','sos'):
        cert=uniform_binary_shuttle(mode)
        assert cert.expression.degree==4 and len(cert.witness_names)==8
        for x in (0,1,2,5,19):
            charts=binary_shuttle_charts(7+x)
            fixed=compile_charts(charts,mode)
            for n in range(7):
                for i,c in enumerate(charts):
                    for j in range(x+n+2):
                        y=chart_value(c,(n,j))
                        w=uniform_binary_witness(x,i,n,j)
                        assert cert.evaluate((x,)+y,w)==0
                        assert fixed.evaluate(y,w)==0
                        bump('uniform_gap_exact_comparisons')
            # Same expanded uniform polynomial, every natural witness point
            # in this bounded cube, compared with a separately compiled fixed gap.
            for w in product(range(2),repeat=8):
                y=pooled_external(fixed,w)
                assert cert.evaluate((x,)+y,w)==fixed.evaluate(y,w)
                bump('uniform_fixed_polynomial_cube_comparisons')
        for malformed in (True,0.5,-1):
            reject(lambda v=malformed:uniform_binary_witness(v,0,0,0))
            reject(lambda v=malformed:cert.evaluate((v,0,0,3,4,7),(1,0,0,0,1,0,0,0)))


def main():
    orbit_tests();full_cube_tests();mutation_and_type_tests();sorting_refinement_test();moving_frame_and_encoding_tests();uniform_family_tests()
    report={
      'status':'PASS','arithmetic':'exact int/Fraction only; no approximate zeros',
      **COUNTS,
      'binary_certificate':{'branches':2,'parameters':4,'slacks':2,'natural_witnesses':8,
        'product_form':{'squared_residuals':8,'nonnegative_products':2},
        'sos_form':{'squared_residuals':10,'nonnegative_products':0},
        'degree':4},
      'limits':'Finite checks supplement the mathematical proof. The compiler does not decide global chart injectivity.'
    }
    # Preserve one exact expanded pair of demonstration certificates. Every
    # coefficient is an integer and every exponent is a natural integer.
    artifact={'fixed_gap':7,'external_coordinates':['t','x0','x1','x2','x3'],'forms':{},'uniform_gap_forms':{}}
    for mode in ('products','sos'):
        cert=compile_charts(binary_shuttle_charts(7),mode)
        artifact['forms'][mode]={'witnesses':list(cert.witness_names),'terms':[
            {'exponents':list(powers),'coefficient':coefficient.numerator}
            for powers,coefficient in cert.expression.terms]}
    for mode in ('products','sos'):
        cert=uniform_binary_shuttle(mode)
        artifact['uniform_gap_forms'][mode]={'external_coordinates':['gap_minus_7','t','x0','x1','x2','x3'],
            'witnesses':list(cert.witness_names),'terms':[
            {'exponents':list(powers),'coefficient':coefficient.numerator}
            for powers,coefficient in cert.expression.terms]}
    Path(__file__).with_name('binary-d7-full-orbit-quartics.json').write_text(json.dumps(artifact,indent=2)+'\n')
    target=Path(__file__).with_name('phase-quartic-test-results.json')
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__': main()
