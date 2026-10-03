#!/usr/bin/env python3
from itertools import product
from pathlib import Path
import json
import sys
from exact_phase_quartic import binary_shuttle_charts,compile_charts
from compact_binary_quartic import compact_binary_uniform_sos,compact_binary_witness
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from test_binary_expanding_shuttle import step

counts={}
def bump(key,n=1):counts[key]=counts.get(key,0)+n

def reject(thunk):
    try:thunk()
    except (TypeError,ValueError):bump('malformed_input_rejections')
    else:raise AssertionError('malformed input was accepted')


def direct_orbits(cert):
    for x in range(8):
        d=7+x;c={0,3,4,d};t=0
        for n in range(21):
            for side in (0,1):
                for j in range(d+n-5):
                    y=(x,t,*sorted(c))
                    w=compact_binary_witness(x,side,n,j)
                    assert cert.evaluate(y,w)==0,(y,w)
                    for k in range(1,6):
                        wrong=list(y);wrong[k]+=1
                        assert cert.evaluate(wrong,w)>0
                        bump('wrong_output_rejections')
                    c=step(c);t+=1
                    bump('direct_binary_orbit_states')
        assert t==21*21+(2*d-11)*21


def cubes(cert):
    for x in (0,1,2,5,19):
        d=7+x;charts=binary_shuttle_charts(d)
        roots={}
        for w in product(range(5),repeat=4):
            e,n,j,u=w
            # Independently evaluate the displayed formulas on the whole
            # natural witness cube, including e>1 and invalid domain slacks.
            T=n*n+(2*d-11)*n
            y=(x,T+j+e*(d+n-5),0,
               3+j+e*(d+n-7-2*j),4+j+e*(d+n-6-2*j),d+n+e)
            value=cert.evaluate(y,w)
            assert value>=0
            expected=e in (0,1) and u==d+n-6-j
            assert (value==0)==expected
            if not value:
                assert y not in roots
                roots[y]=w
                chart=charts[e]
                exact=tuple(p((n,j)).numerator for p in chart.outputs)
                assert y[1:]==exact
                bump('valid_cube_phase_comparisons')
            bump('full_four_witness_cube_evaluations')


def strict_types(cert):
    y=(0,0,0,3,4,7);w=(0,0,0,1)
    for bad in (True,0.5,-1):
        for k in range(4):
            wrong=list(w);wrong[k]=bad
            reject(lambda z=wrong:cert.evaluate(y,z))
        reject(lambda z=bad:cert.evaluate((z,)+y[1:],w))
        reject(lambda z=bad:compact_binary_witness(z,0,0,0))
        reject(lambda z=bad:compact_binary_witness(0,z,0,0))
        reject(lambda z=bad:compact_binary_witness(0,0,z,0))
        reject(lambda z=bad:compact_binary_witness(0,0,0,z))
    reject(lambda:compact_binary_witness(0,2,0,0))
    reject(lambda:compact_binary_witness(0,0,0,2))
    reject(lambda:cert.evaluate((0,0.0,0,3,4,7),w))
    reject(lambda:cert.evaluate(y,w[:-1]))
    assert cert.evaluate(list(y),list(w))==0
    reject(lambda:cert.evaluate(y,[False,0,0,1]))


def main():
    cert=compact_binary_uniform_sos()
    assert len(cert.witness_names)==4 and len(cert.residuals)==7 and cert.expression.degree==4
    assert all(r.degree<=2 for r in cert.residuals)
    direct_orbits(cert);cubes(cert);strict_types(cert)
    fixture={'external_coordinates':['gap_minus_7','t','x0','x1','x2','x3'],
      'witnesses':list(cert.witness_names),'degree':cert.expression.degree,
      'squared_residuals':len(cert.residuals),'terms':[
        {'exponents':list(p),'coefficient':c.numerator} for p,c in cert.expression.terms]}
    Path(__file__).with_name('binary-uniform-four-witness-sos.json').write_text(json.dumps(fixture,indent=2)+'\n')
    receipt={'status':'PASS',**counts,'natural_witnesses':4,'squared_residuals':7,
             'degree':4,'scope':'explicit binary uniform-gap family only; original generic fixtures unchanged'}
    Path(__file__).with_name('compact-binary-test-results.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
