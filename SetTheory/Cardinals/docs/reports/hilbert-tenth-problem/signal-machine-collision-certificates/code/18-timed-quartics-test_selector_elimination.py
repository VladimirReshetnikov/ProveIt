#!/usr/bin/env python3
from itertools import product
from fractions import Fraction
from pathlib import Path
import json
from exact_phase_quartic import Poly,Chart,compile_charts,binary_shuttle_charts,uniform_binary_shuttle,uniform_binary_witness
from selector_elimination import eliminate_last_selector,compile_reduced_charts

counts={}
def bump(key,n=1):counts[key]=counts.get(key,0)+n

def reject(thunk):
    try:thunk()
    except (TypeError,ValueError):bump('malformed_input_rejections')
    else:raise AssertionError('malformed input accepted')

def output(c,z):
    values=tuple(p(z) for p in c.outputs)
    assert all(x.denominator==1 for x in values)
    return tuple(x.numerator for x in values)

def fullcube():
    reduced=compile_reduced_charts(binary_shuttle_charts(7))
    cert=reduced.certificate
    assert len(cert.witness_names)==7 and len(cert.residuals)==10 and cert.expression.degree==4
    roots={}
    for w in product(range(3),repeat=7):
        e,nR,jR,uR,nL,jL,uL=w
        # Pooled output with implicit last selector, including e>1 so eL<0.
        eL=1-e
        y=(nR*nR+3*nR+jR+nL*nL+4*nL+2*eL+jL,
           0,3*e+jR+3*eL+nL-jL,4*e+jR+5*eL+nL-jL,
           7*e+nR+8*eL+nL)
        value=reduced.evaluate(y,w)
        assert value>=0
        valid=(e==1 and nL==jL==uL==0 and uR==1+nR-jR and uR>=0) or (
               e==0 and nR==jR==uR==0 and uL==1+nL-jL and uL>=0)
        assert (value==0)==valid
        if not value:
            assert y not in roots
            roots[y]=w
        bump('full_seven_witness_cube_evaluations')
    assert len(roots)==14


def phase_and_uniform():
    uniform=eliminate_last_selector(uniform_binary_shuttle('sos'),2)
    assert uniform.certificate.expression.degree==4
    assert len(uniform.certificate.witness_names)==7
    assert len(uniform.certificate.residuals)==10
    for x in (0,1,2,5,19):
        charts=binary_shuttle_charts(x+7)
        fixed=compile_reduced_charts(charts)
        for n in range(8):
            for side,c in enumerate(charts):
                for j in range(x+n+2):
                    y=output(c,(n,j))
                    w=fixed.witness(side,(n,j))
                    assert fixed.evaluate(y,w)==uniform.evaluate((x,)+y,w)==0
                    assert w==uniform.drop_selector(uniform_binary_witness(x,side,n,j))
                    bump('uniform_gap_orbit_comparisons')
        # Expanded polynomial equality after specializing external x, sampled
        # on all retained natural witnesses in this cube, with negative last
        # selectors covered when the retained selector equals 2.
        for w in product(range(3),repeat=7):
            e,nR,jR,uR,nL,jL,uL=w
            d=7+x;eL=1-e
            y=(nR*nR+(2*d-11)*nR+jR+nL*nL+(2*d-10)*nL+(d-5)*eL+jL,
               0,3*e+jR+(d-4)*eL+nL-jL,4*e+jR+(d-2)*eL+nL-jL,
               d*e+nR+(d+1)*eL+nL)
            # Implicit eL may be negative off the zero set; keep the test's
            # external time in its declared natural domain.
            y=(max(0,y[0]),)+y[1:]
            assert uniform.evaluate((x,)+y,w)==fixed.evaluate(y,w)>=0
            bump('uniform_fixed_cube_comparisons')
    return uniform


def boundary_and_types():
    n=Poly.var(1,0)
    for c in (Chart('clock',1,(n,)),Chart('rational',1,(n*(n+1)*Fraction(1,2),),((n-1)*Fraction(1,2),))):
        reduced=compile_reduced_charts([c])
        assert len(reduced.certificate.witness_names)==c.parameters+len(c.inequalities)
        assert reduced.certificate.residuals[0]==Poly.const(reduced.certificate.expression.arity,0)
        for z in range(1,10):
            assert reduced.evaluate(output(c,(z,)),reduced.witness(0,(z,)))==0
            bump('single_chart_no_selector_checks')
    singleton=compile_reduced_charts([Chart('point',0,(Poly.const(0,11),))])
    assert singleton.evaluate((11,),())==0
    assert singleton.evaluate((10,),())>0
    bump('parameter_free_no_selector_checks',2)
    c=compile_reduced_charts(binary_shuttle_charts(7))
    y=(0,0,3,4,7);w=c.witness(0,(0,0))
    for bad in (True,0.5,-1):
        badw=(bad,)+w[1:]
        reject(lambda z=badw:c.evaluate(y,z))
        reject(lambda z=bad:eliminate_last_selector(c.source,z))
    reject(lambda:eliminate_last_selector(compile_charts(binary_shuttle_charts(7),'products')))
    reject(lambda:c.evaluate((0.0,0,3,4,7),w))
    reject(lambda:c.drop_selector((1,1,0,0,0,0,0,0)))
    reject(lambda:c.drop_selector((True,0,0,0,1,0,0,0)))
    reject(lambda:compile_reduced_charts([]))
    u=eliminate_last_selector(uniform_binary_shuttle('sos'),2)
    for bad in (True,0.5,-1):
        reject(lambda z=bad:u.evaluate((z,)+y,w))


def main():
    fullcube();uniform=phase_and_uniform();boundary_and_types()
    cert=uniform.certificate
    fixture={'external_coordinates':['gap_minus_7','t','x0','x1','x2','x3'],
      'witnesses':list(cert.witness_names),'degree':cert.expression.degree,
      'squared_residuals':len(cert.residuals),'terms':[
        {'exponents':list(p),'coefficient':c.numerator} for p,c in cert.expression.terms]}
    Path(__file__).with_name('binary-uniform-seven-witness-sos.json').write_text(json.dumps(fixture,indent=2)+'\n')
    receipt={'status':'PASS',**counts,'natural_witnesses':7,'squared_residuals':10,
             'degree':4,'scope':'SOS only; fixed-input general theorem and explicit uniform-gap binary family'}
    Path(__file__).with_name('selector-elimination-test-results.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
