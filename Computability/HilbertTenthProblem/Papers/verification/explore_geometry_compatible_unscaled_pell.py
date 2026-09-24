"""Retained ternary head geometry does not repair the isolated42 kernel."""
from pathlib import Path
import json
from math import comb
import sympy as sp
import explore_unscaled_pell_coordinate as kernel


def vfactorial(n,p):
    result=0
    while n:
        n//=p;result+=n
    return result


def vbinomial(n,k,p):
    assert 0<=k<=n
    return vfactorial(n,p)-vfactorial(k,p)-vfactorial(n-k,p)


def valuation(n,p):
    assert n>0
    result=0
    while n%p==0:
        n//=p;result+=1
    return result


def verify_shifted_identity():
    U=sp.Symbol('U');identities=0
    for r in range(1,25):
        direct=sum(comb(2*r,r+j)*U**j for j in range(r+1))
        shifted=sum(comb(2*r-j-1,r-1)*(U+1)**j for j in range(r+1))
        assert sp.expand(direct-shifted)==0
        identities+=1
    exact_valuations=certificates=admitted=0
    for r in range(1,65):
        for prime in (3,5,7):
            for j in range(min(r,12)+1):
                coefficient=comb(2*r-j-1,r-1)
                assert vbinomial(2*r-j-1,r-1,prime)==valuation(coefficient,prime)
                exact_valuations+=1
            for exponent in range(1,7):
                U0=2*prime-1
                Y=sum(comb(2*r,r+j)*U0**j for j in range(r+1))
                lower=min(vbinomial(2*r-j-1,r-1,prime)+j
                          for j in range(min(r+1,exponent)))
                if lower>=exponent:
                    assert Y%prime**exponent==0
                    admitted+=1
                certificates+=1
    assert admitted>0
    return dict(symbolic_polynomial_identities=identities,
                exact_small_coefficient_valuations=exact_valuations,
                finite_truncation_cases=certificates,admitted_divisibility_cases=admitted,
                scope='Small exact sums independently validate the shifted identity, '
                      'Legendre valuations and the sufficient divisibility certificate. '
                      'Failure of the sufficient condition is not asserted to imply nondivisibility.')


def verify_geometry_sources():
    C,A,k,v,r=sp.symbols('C A k v r')
    R=C*A;q=R*v;H=(q-1)/(R-1);D=R/k;Z=A*H
    scale=q**9;P=r-(scale-1)/2;betaP=scale-r
    rows=[('kD=R',k*D-R),('RH=H+q-1',R*H-H-q+1),
          ('RH=CZ',R*H-C*Z),('Rv=q',R*v-q),
          ('2r+1=q9+2P',2*r+1-scale-2*P),('r+betaP=q9',r+betaP-scale)]
    for _,residual in rows:assert sp.cancel(residual)==0
    return dict(symbolic_equations=[name for name,_ in rows],equation_count=6,
                scope='Formal rational identities only; the concrete cases separately '
                      'prove integrality and strict positivity of every defined coordinate.')


def certificate(C,R,seven_exponent,coefficient):
    assert C>=3 and R%C==0 and R>=C
    c3=valuation(R,3)
    assert R==3**c3 and C==3**valuation(C,3)
    q=R*7**seven_exponent;scale=q**9
    target3=9*c3;target7=9*seven_exponent
    r=coefficient*7**(target7-1)-1;J=2*r+1
    assert r>=27 and r%2==0 and (scale-1)//2<r<scale
    assert scale>=81 and r<2*scale and scale<r*r
    assert J>scale.bit_length() and 3**scale.bit_length()>max(scale,48*r)
    assert J%6==3 and pow(3,J,7)==6
    v3=vbinomial(2*r,r,3)
    assert target3<=v3<J
    coefficients=[vbinomial(2*r-j-1,r-1,7) for j in range(target7)]
    assert all(v+j>=target7 for j,v in enumerate(coefficients))
    # Since 7|(U+1), all higher shifted terms vanish modulo7^target7.
    # Since U=3^J and J>v3, the constant binomial coefficient fixes v3(Y).
    assert pow(7,seven_exponent,R-1)==1
    H,remainder=divmod(q-1,R-1);assert remainder==0
    k=3;D,remainder=divmod(R,k);assert remainder==0
    A=R//C;Z=A*H;v=q//R;P=r-(scale-1)//2;betaP=scale-r
    values=dict(C=C,R=R,A=A,H=H,k=k,D=D,Z=Z,v=v,q=q,D0=scale,
                r=r,P=P,betaP=betaP)
    assert all(x>0 for x in values.values())
    residuals=[k*D-R,R*H-H-q+1,R*H-C*Z,R*v-q,
               2*r+1-scale-2*P,r+betaP-scale]
    assert residuals==[0]*6
    assert q%3==0 and H%3==1 and q%7==0
    assert pow(3,J,7)!=0  # D0 cannot divide U=3^J.
    return dict(values=values,seven_exponent=seven_exponent,
                index_coefficient=coefficient,main_index=J,
                three_exponent_in_scale=target3,seven_exponent_in_scale=target7,
                exact_Y_valuation_3=v3,shifted_coefficient_valuations_7=coefficients,
                minimum_seven_certificate_margin=min(v+j-target7 for j,v in enumerate(coefficients)),
                exact_geometry_and_index_residuals=residuals,
                q_bits=q.bit_length(),r_bits=r.bit_length(),
                Y_divisible_by_scale=True,U_not_divisible_by_scale=True,
                even_index_and_all_kernel_bounds=True,
                scope='Six exact geometry/index equations plus the complete positive '
                      'isolated42 kernel. No tag fields, packing formula or content/length '
                      'transports are supplied; U,Y and the Pell auxiliaries are not materialized.')


def cases():
    small=certificate(3,3,1,68891)
    assert small['values']['q']==21 and small['values']['r']==397142905690
    assert small['values']['P']==2882400 and small['values']['betaP']==397137140891
    assert small['exact_Y_valuation_3']==11
    assert small['shifted_coefficient_valuations_7']==[13,13,13,13,13,12,12,13,13]
    compiled=certificate(3**7,3**8,40,78849398407287110441440517561704247)
    assert compiled['exact_Y_valuation_3']==385
    assert len(compiled['shifted_coefficient_valuations_7'])==360
    assert min(compiled['shifted_coefficient_valuations_7'])==381
    assert compiled['minimum_seven_certificate_margin']==24
    K=9;Li=9;a=2;Uappend=3;C=compiled['values']['C']
    assert C>max(K**3,3*K*3**a,2*K*Uappend+3,K*K*Li)
    compiled['compatible_fixed_threshold_example']=dict(beta=2,a=a,K=K,Linit=Li,
        appendant_value=Uappend,C=C,
        scope='Only the fixed numerical width/initial-domain thresholds of91 are checked. '
              'This is not a tag-history witness or a Neary specialization.')
    return [small,compiled]


def verify():
    return dict(status='PASS_GEOMETRY_COMPATIBLE_UNSCALED_PELL_OBSTRUCTION',
                review='Author and two independent complete proof/source/dependency reviews and fresh verification PASS; independent digit-carry calculations confirm all371 large coefficient valuations.',
                isolated_kernel_sources=[kernel.verify_source(sign) for sign in (1,-1)],
                shifted_identity=verify_shifted_identity(),
                geometry_sources=verify_geometry_sources(),cases=cases(),
                proof='../1980/EXPLORATION_GEOMETRY_COMPATIBLE_UNSCALED_PELL.md',
                scope='The retained3-adic geometry and exact scalar index interface do not '
                      'restore the omitted U-scale divisibility or force q to be a power3. '
                      'The complete91 tag system and any full90-operation deletion remain unrefuted.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['shifted_identity']);print(result['geometry_sources'])
    print([{k:c[k] for k in ('seven_exponent','q_bits','r_bits','exact_Y_valuation_3',
                            'minimum_seven_certificate_margin')} for c in result['cases']])
