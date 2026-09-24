"""Dropping only U=w*D0 gives an unsound42-operation power/binomial kernel."""
from pathlib import Path
import hashlib
import json
from math import comb
import os
import shutil
import subprocess
import sympy as sp
import explore_unit_two_ternary_kernel as previous

PARAMETERS=previous.PARAMETERS
AUXILIARIES=['U0' if n=='w' else n for n in previous.AUXILIARIES]
SYM={n:sp.Symbol(n) for n in PARAMETERS+AUXILIARIES}


def schedule(sign=1):
    return [tuple('U0' if x=='wn2' else x for x in row)
            for row in previous.schedule(sign) if row[0]!='wn2']


def source_residuals(sign=1):
    z=SYM
    a,c,d,f,h,i,j,k,o,r,s,tau,eta,zeta,ga,y=[z[n] for n in
        ('a','c','d','f','h','i','j','k','o','r','s','tau','eta','zeta','ga','y_aux')]
    U,Y=z['U0'],s*z['D0'];Q=U*Y*Y;disc=a*a+6*a+8
    u=j*c+sign*(2*r+1)
    return [Q*(Q+1)*k*k-tau*(tau+1),c-Y*k-eta,k-eta-zeta,
            k-r-1-h*U*Y,a-Y*(U+1),d-U-a*c-ga*(6*a+8),
            d*d-disc*c*c-1,(i*c*c)**2-disc*(f*f-1),
            disc*(f*f-1)*(u*u-y*y)-(1-y*y),u-o*f-sign*c]


def verify_source(sign=1):
    rows=schedule(sign);env=dict(SYM)
    previous.baseline.run_schedule(rows,env)
    sources=source_residuals(sign)
    u=SYM['j']*SYM['c']+sign*(2*SYM['r']+1)
    records=[]
    for index,((left,right),source) in enumerate(zip(previous.EQUALITIES,sources)):
        correction=sources[7]*(u*u-SYM['y_aux']**2) if index==8 else 0
        assert sp.expand(env[left]-env[right]-source-correction)==0
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(source),
                            correction=sp.sstr(correction)))
    primitives,counts=previous.verify_primitives(rows,env)
    assert len(primitives)==42 and counts=={'+':18,'*':24}
    assert len(AUXILIARIES)==16 and len(sources)==10
    assert not any('w' in row for row in rows)
    assert all(p.free_symbols<=set(SYM.values()) for p in sources)
    return dict(sign=sign,operations=42,multiplications=24,additions=18,
                positive_auxiliaries=AUXILIARIES,parameters=PARAMETERS,
                positive_auxiliary_count=16,equations=10,dag=rows,sources=records,
                scope='Only U=w*D0 is removed; U0 is a positive supplied coordinate. '
                      'Y=s*D0 and every other source polynomial remain.')


def canonical_y(r):
    U=3**(2*r+1)
    return U,sum(comb(2*r,r+j)*U**j for j in range(r+1))


def vfactorial(n,p):
    result=0
    while n:
        n//=p;result+=n
    return result


def y_mod_two_power(r,bits):
    """Exact Horner evaluation; maintain the odd part of binom(2r,k)."""
    modulus=1<<bits;U=pow(3,2*r+1,modulus)
    odd=1;valuation=0;result=1
    for k in range(1,r+1):
        numerator=2*r-k+1;denominator=k
        nv=(numerator&-numerator).bit_length()-1
        dv=(denominator&-denominator).bit_length()-1
        valuation+=nv-dv
        assert valuation>=0
        numerator>>=nv;denominator>>=dv
        odd=odd*numerator*pow(denominator,-1,modulus)%modulus
        coefficient=0 if valuation>=bits else (odd<<valuation)%modulus
        result=(result*U+coefficient)%modulus
    return result


def y_mod_prime_power(r,prime,exponent):
    """Independent generic implementation for native-helper cross-checks."""
    modulus=prime**exponent;U=pow(3,2*r+1,modulus)
    unit=1;valuation=0;result=1
    for k in range(1,r+1):
        numerator=2*r-k+1;denominator=k
        while numerator%prime==0:
            numerator//=prime;valuation+=1
        while denominator%prime==0:
            denominator//=prime;valuation-=1
        assert valuation>=0
        unit=unit*numerator*pow(denominator,-1,modulus)%modulus
        coefficient=0 if valuation>=exponent else unit*prime**valuation%modulus
        result=(result*U+coefficient)%modulus
    return result


def verify_modular_recurrence():
    cases=0
    for r in range(1,65):
        _,Y=canonical_y(r)
        for bits in (1,3,9,12):
            assert y_mod_two_power(r,bits)==Y%(1<<bits)
            cases+=1
    return dict(exact_direct_comparisons=cases,indices=[1,64],
                scope='Independent direct binomial sums check the modular Horner recurrence.')


def small_counterexample():
    r=28;D0=119;U,Y=canonical_y(r);J=2*r+1
    assert D0==7*17 and Y%D0==0 and U%D0!=0
    assert D0>=81 and r>=27 and r<2*D0 and D0<r*r
    assert U>D0 and Y>D0 and U>48*r
    a=Y*(U+1);A=a+3;P=2*U*Y*Y+1;disc=A*A-1;M=6*a+8
    chi,k=previous.pell_power(P,r+1)
    d,c=previous.pell_power(A,J)
    assert (chi-1)%2==0 and (k-r-1)%(U*Y)==0
    assert (d-U-a*c)%M==0
    tau=(chi-1)//2;h=(k-r-1)//(U*Y);ga=(d-U-a*c)//M
    eta=c-Y*k;zeta=k-eta
    supplied=dict(U0=U,s=Y//D0,a=a,c=c,d=d,k=k,h=h,ga=ga,
                  tau=tau,eta=eta,zeta=zeta)
    assert all(v>0 for v in supplied.values())
    # The first seven equations have no remaining unmaterialized coordinates.
    assert (U*Y*Y)*(U*Y*Y+1)*k*k==tau*(tau+1)
    assert c==Y*k+eta and k==eta+zeta and k==r+1+h*U*Y
    assert a==Y*(U+1) and d==U+a*c+ga*M and d*d-disc*c*c==1
    assert c>A**6 and c>A*disc**2 and c>J and 2*J<=c
    return dict(r=r,D0=D0,scale_factorization=[7,17],main_index=J,
                U_bits=U.bit_length(),Y_bits=Y.bit_length(),Y_mod_scale=Y%D0,
                U_mod_scale=U%D0,materialized_positive_coordinates=11,
                coordinate_bits={n:v.bit_length() for n,v in supplied.items()},
                exact_materialized_equations=7,index_parity=r%2,
                unmaterialized_positive_auxiliaries=['f','i','j','o','y_aux'],
                scope='The remaining five auxiliaries follow from the exact fixed-plus '
                      'canonical construction proved in the note.119 is not a ninth power; '
                      'this is a kernel counterexample, not a tag-history tuple.')


def ninth_power_counterexample():
    q=6;D0=q**9;r=32766;J=2*r+1
    assert r%2==0 and D0>=81 and r>=27 and r<2*D0 and D0<r*r
    assert J>=9
    v3=vfactorial(2*r,3)-2*vfactorial(r,3)
    residue=y_mod_two_power(r,20)
    v2=(residue&-residue).bit_length()-1
    assert v3==9 and residue==581632 and v2==13
    assert residue%512==0 and D0==512*3**9
    assert 3**J>D0 and 3**J>48*r
    return dict(q=q,D0=D0,r=r,main_index=J,index_parity=r%2,
                Y_mod_2_power_20=residue,exact_Y_valuation_2=v2,
                exact_central_valuation_3=v3,exact_Y_valuation_3=v3,
                Y_divisible_by_q9=True,modular_horner_steps=r,
                exact_scale_bound_checks=True,
                scope='Canonical Y is not materialized. Its divisibility follows from '
                      'the exact modular recurrence and Kummer/Legendre at3. All16 positive '
                      'auxiliaries exist by the same canonical construction. This does not '
                      'supply any tag outer tuple, compiled-width geometry or raw-input false positive.')


def odd_ninth_power_counterexample():
    root=Path(__file__).resolve().parents[2]
    source=Path(__file__).with_name('unscaled_pell_coordinate_modular.cpp')
    compiler=shutil.which('g++') or shutil.which('clang++')
    assert compiler, 'The reproducible large modular check needs g++ or clang++.'
    directory=root/'tmp'/'unscaled_pell_coordinate'
    directory.mkdir(parents=True,exist_ok=True)
    executable=directory/('modular.exe' if os.name=='nt' else 'modular')
    command=[compiler,'-O3','-std=c++17','-Wall','-Wextra','-pedantic',
             str(source),'-o',str(executable)]
    subprocess.run(command,check=True,capture_output=True,text=True,timeout=120)
    compiler_version=subprocess.run([compiler,'--version'],check=True,
        capture_output=True,text=True,timeout=20).stdout.splitlines()[0]
    cases=[];expected=[]
    for r in range(1,65):
        _,Y=canonical_y(r)
        for prime,exponent in ((2,1),(2,3),(2,9),(2,12),(7,1),(7,3),(7,5)):
            cases.append((r,prime,exponent));expected.append(Y%(prime**exponent))
    for r,prime,exponent in ((32766,2,20),(84034,7,8)):
        cases.append((r,prime,exponent))
        expected.append(y_mod_prime_power(r,prime,exponent))
    request=''.join(f'{r} {prime} {exponent}\n' for r,prime,exponent in cases)
    output=subprocess.run([str(executable),'--batch'],input=request,check=True,
        capture_output=True,text=True,timeout=120).stdout.splitlines()
    assert len(output)==len(cases)==450
    for case,wanted,line in zip(cases,expected,output):
        actual=tuple(map(int,line.split()))
        assert actual[:3]==case and actual[3]==wanted
    q=7;D0=q**9;r=5*7**8-1;J=2*r+1
    output=subprocess.run([str(executable),str(r),'7','11'],check=True,
        capture_output=True,text=True,timeout=180).stdout
    actual=tuple(map(int,output.split()))
    assert actual==(r,7,11,1856265922)
    assert actual[3]==46*7**9 and 46%7!=0
    P=r-(D0-1)//2;betaP=D0-r
    assert q==7 and D0==40353607 and r==28824004
    assert P==8647201 and betaP==11529603 and P>0 and betaP>0
    assert 2*r+1==D0+2*P and r+betaP==D0
    assert r%2==0 and D0>=81 and r>=27 and r<2*D0 and D0<r*r
    assert J>D0.bit_length() and 3**(D0.bit_length())>max(D0,48*r)
    assert q%3!=0
    return dict(q=q,D0=D0,r=r,main_index=J,index_parity=0,
                Y_mod_7_power_11=actual[3],exact_Y_valuation_7=9,
                Y_divisible_by_q9=True,packed_value=P,positive_bound_slack=betaP,
                exact_index_offset_and_bound=True,modular_horner_steps=r,
                native_direct_crosschecks=448,native_python_large_crosschecks=2,
                crosscheck_results={'32766_mod_2_power_20':expected[-2],
                                    '84034_mod_7_power_8':expected[-1]},
                compiler_version=compiler_version,
                helper_source='unscaled_pell_coordinate_modular.cpp',
                helper_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                compile_command=[Path(compiler).name,'-O3','-std=c++17','-Wall',
                                 '-Wextra','-pedantic',str(source.relative_to(root)),
                                 '-o',str(executable.relative_to(root))],
                reproduce_arguments=[str(r),'7','11'],
                scope='Odd ninth-power scale and the exact scalar index-offset equations '
                      'are both satisfied. The full positive42 kernel exists by the same '
                      'canonical formulas. No tag fields or transports are supplied; q7 '
                      'violates the retained tag geometry implication3|q.')


def verify():
    return dict(status='PASS_UNSCALED_PELL_COORDINATE_COUNTEREXAMPLES',
                review='Author and two independent complete proof/source/dependency reviews and fresh verification runs pass.',
                sources=[verify_source(sign) for sign in (1,-1)],
                recurrence=verify_modular_recurrence(),small=small_counterexample(),
                ninth_power=ninth_power_counterexample(),
                odd_ninth_power=odd_ninth_power_counterexample(),
                proof='../1980/EXPLORATION_UNSCALED_PELL_COORDINATE.md',
                scope='Rejected isolated42-operation kernel deletion, including an even-index '
                      'q9 scale. Neither the43 kernel nor the complete91 tag source is refuted.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print([{k:s[k] for k in ('sign','operations','multiplications','additions',
                            'positive_auxiliary_count','equations')} for s in result['sources']])
    print(result['recurrence']);print(result['small']);print(result['ninth_power'])
    print(result['odd_ninth_power'])
