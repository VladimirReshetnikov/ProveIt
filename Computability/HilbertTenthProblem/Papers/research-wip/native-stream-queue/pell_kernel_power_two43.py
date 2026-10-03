"""Exact power-of-two geometry in43 operations with the retained minus kernel."""
import argparse
from collections import Counter
import json
from pathlib import Path
import sympy as sp
import explore_one_field_half_mask as prior

CORE=[(name,op,'q' if left=='n2' else left,'q' if right=='n2' else right)
      for name,op,left,right in prior.CORE]
SCHEDULE=list(CORE)
NAMES=['q']+prior.CORE_NAMES
EQUALITIES=[('r1','q')]+prior.baseline.EQUALITIES[5:15]


def sources(z):
    q=z['q']
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,ya=(z[name] for name in prior.CORE_NAMES)
    X,Y=w*q,s*q;delta=a*a+4*a+3;U=j*c-(2*r+1)
    return [r-q+1,((X*Y)**2+X)*(k*Y)**2-tau*(tau+1),
            c-k*Y-eta,k-eta-zeta,k-r-1-h*X*Y,a-Y*(X+1),
            d-X-a*c-ga*(4*a+3),d*d-1-delta*c*c,
            (i*c*c)**2-delta*(f*f-1),
            delta*(f*f-1)*(U*U-ya*ya)-(1-ya*ya),U-o*f+c]


def source_check():
    z={name:sp.Symbol(name) for name in NAMES}
    env=prior.run(SCHEDULE,z);polys=sources(z)
    U=z['j']*z['c']-(2*z['r']+1);correction=polys[8]*(U*U-z['y_aux']**2)
    records=[]
    for ix,((left,right),polynomial) in enumerate(zip(EQUALITIES,polys)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if ix==9 else 0
        sign=1 if sp.expand(actual-polynomial-adjust)==0 else -1
        assert sp.expand(actual-sign*polynomial-adjust)==0,ix
        records.append(dict(equality=[left,right],source_sign=sign,
                            source=str(sp.expand(polynomial)),correction=str(sp.expand(adjust))))
    counts=Counter(row[1] for row in SCHEDULE)
    assert len(SCHEDULE)==43 and counts['*']==25 and counts['+']+counts['-']==18
    assert len(polys)==len(EQUALITIES)==11 and len(NAMES)==18
    assert set().union(*(p.free_symbols for p in polys))==set(z.values())
    assert len(CORE)==43
    return dict(operations=43,multiplications=25,additions_subtractions=18,equations=11,
                positive_parameters=['q'],positive_auxiliaries=prior.CORE_NAMES,
                instructions=[list(row) for row in SCHEDULE],sources=records,
                projection='q=2^t with integer t>=1; r=q-1 and kernel scaleq')


def pell(A,n):
    if n==0:return 1,0
    x,y=pell(A,n//2);D=A*A-1
    xx,yy=2*x*x-1,2*x*y
    return (A*xx+D*yy,xx+A*yy) if n%2 else (xx,yy)


def canonical_main(q):
    assert q>=2 and q&(q-1)==0
    r=q-1;J=2*r+1;X=2**J;den=X**r;num=(X+1)**(2*r);Y,tail=divmod(num,den)
    a=Y*(X+1);A=a+2;delta=A*A-1;P=2*X*Y*Y+1
    d,c=pell(A,J);v,k=pell(P,r+1)
    eta=c-Y*k;zeta=k-eta
    assert X%q==Y%q==0 and 0<4*tail<den and eta>0 and zeta>0
    assert (v-1)%2==0 and (k-r-1)%(X*Y)==0 and (d-X-a*c)%(4*a+3)==0
    values=dict(q=q,r=r,w=X//q,s=Y//q,a=a,c=c,d=d,k=k,eta=eta,zeta=zeta,
                tau=(v-1)//2,h=(k-r-1)//(X*Y),ga=(d-X-a*c)//(4*a+3))
    assert min(values.values())>0
    assert d*d-delta*c*c==1
    assert ((X*Y)**2+X)*(k*Y)**2==values['tau']*(values['tau']+1)
    assert c*den>k*num and c<(Y+1)*k
    return values


def small_complete():
    z=canonical_main(2);A=z['a']+2;delta=A*A-1;c=z['c'];J=3;m=2*c*J
    f,v=pell(A,m);quotient,remainder=divmod(v,c*c);assert remainder==0
    i=delta*quotient;R=i*c*c
    chi,y=pell(R,J);u,remainder=divmod(chi,R);assert remainder==0
    o,remainder=divmod(u+c,f);assert remainder==0
    j,remainder=divmod(u+J,c);assert remainder==0
    z.update(f=f,i=i,y_aux=y,o=o,j=j)
    assert set(z)==set(NAMES) and min(z.values())>0
    env=prior.run(SCHEDULE,z)
    for left,right in EQUALITIES:assert env[left]==env[right],(left,right)
    return dict(q=2,r=1,X=8,Y=10,a=z['a'],c=c,k=z['k'],eta=z['eta'],zeta=z['zeta'],
                h=z['h'],auxiliary_index=m,all_positive=True,all_eleven_equalities=True,
                witness_bit_lengths={name:value.bit_length() for name,value in z.items()})


def bootstrap():
    for q in range(5,501):
        r=q-1;X=Y=q;a=Y*(X+1);A=a+2;P=2*X*Y*Y+1
        assert X*Y>r+1 and a>2*r+1 and P>A and 2*P-1>4*A
        assert (2*A-1)**5>A*(A*A-1)**2
        assert 6*X*Y*Y>a
        assert 8*r<X**(r+1) and 2*4**r<X**(r+1)
    # The q3 obstruction is independent of all auxiliary values.
    assert (0*0-(1+0))%3!=0
    return dict(q_interval=[5,500],cases=496,
                boundary_soundness='q2 andq4 already powers2; q3 main norm impossible modulo3',
                initial_upper_ratio_counterexample=dict(q=5,r=4,minimum_a=30,four_r_over_a='8/15'),
                lower_ratio_first=True)


def main_examples():
    rows=[]
    for q in (2,4,8,16,32):
        z=canonical_main(q)
        assert (q-1).bit_count()==q.bit_length()-1
        rows.append(dict(q=q,r=q-1,X_bits=2*(q-1)+2,
                         main_coordinate_bits={name:z[name].bit_length() for name in ('a','c','d','k')},
                         strict_ratio_and_all_main_equalities=True))
    return rows


def verify():
    return dict(status='PASS_COMPLETE_POWER_TWO_GEOMETRY_43',source=source_check(),
                bootstrap=bootstrap(),canonical_main_cases=main_examples(),small_complete_witness=small_complete(),
                scope='Exact positive power-of-two geometry only; no stream typing, controller, input or universal compiler included',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps({key:value for key,value in result.items() if key!='source'},indent=2))
