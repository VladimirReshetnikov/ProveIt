"""Direct Boolean ternary rails55 and exact scalar FIFO60, not universal."""
import argparse
from collections import Counter
from itertools import product
import hashlib
import json
from math import comb
from pathlib import Path

import sympy as sp
import native_controller_three_selector_53 as prior

CORE = []
for row in prior.CORE:
    if row[0] == 'sn2':
        CORE.extend([('bt_three_s', '*', 3, 's'), ('sn2', '+', 'bt_three_s', 1)])
    else:
        CORE.append(row)
PACK = [('bt_p0', '*', 'q', 'F3'), ('bt_p1', '+', 'F2', 'bt_p0'),
        ('bt_p2', '*', 'q', 'bt_p1'), ('bt_p3', '+', 'F1', 'bt_p2'),
        ('bt_p4', '*', 'q', 'bt_p3'), ('bt_packed', '+', 'F0', 'bt_p4')]
BOUNDS = [('bt_X_bound', '+', 'r', 'bound_beta'),
          ('bt_append', '+', 'F0', 'F1'), ('bt_read', '+', 'F2', 'F3'),
          ('bt_joint', '+', 'bt_append', 'bt_read'), ('bt_joint_bound', '+', 'bt_joint', 'alpha')]
FIFO = [('bt_initial', '*', 2, 'x'), ('bt_tail', '*', 'W', 'bt_append'),
        ('bt_transport', '+', 'bt_initial', 'bt_tail'),
        ('bt_width', '+', 'bt_initial', 'width_beta'), ('bt_divisor', '*', 'W', 'L')]


def independent_sources(z, fifo):
    q = z['q']
    F = [z[f'F{i}'] for i in range(4)]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y = (z[n] for n in prior.CORE_NAMES)
    X,Y = w*q, 3*s+1
    delta = a*a+6*a+8
    u = 2*r+1+j*c
    result = [r-sum(F[k]*q**k for k in range(4)),
              ((X*Y)**2+X)*(Y*k)**2-tau*(tau+1),
              c-Y*k-eta, k-eta-zeta, k-r-1-h*X*Y,
              a-Y*(X+1), d-X-a*c-ga*(6*a+8), d*d-1-delta*c*c,
              (i*c*c)**2-delta*(f*f-1),
              delta*(f*f-1)*(u*u-y*y)-(1-y*y), u-c-o*f,
              r+z['bound_beta']-X, sum(F)+z['alpha']-q]
    if fifo:
        result += [F[2]+F[3]-2*z['x']-z['W']*(F[0]+F[1]),
                   2*z['x']+z['width_beta']-z['W'], z['W']*z['L']-q]
    return result


def source_check(fifo=True):
    parameters = ['q','F0','F1','F2','F3']+(['x','W'] if fifo else [])
    auxiliaries = prior.CORE_NAMES+['bound_beta','alpha']+(['width_beta','L'] if fifo else [])
    z = {name: sp.Symbol(name) for name in parameters+auxiliaries}
    schedule = PACK+CORE+BOUNDS+(FIFO if fifo else [])
    env = prior.execute(schedule, dict(z,n2=z['q']))
    equalities = [('r','bt_packed')]+prior.kernel.EQUALITIES[1:]
    equalities += [('bt_X_bound','wn2'),('bt_joint_bound','q')]
    if fifo:
        equalities += [('bt_read','bt_transport'),('bt_width','W'),('bt_divisor','q')]
    polynomials = independent_sources(z,fifo)
    u = 2*z['r']+1+z['j']*z['c']
    correction = polynomials[8]*(u*u-z['y_aux']**2)
    records = []
    for ix,((left,right),p) in enumerate(zip(equalities,polynomials)):
        adjust = correction if ix == 9 else 0
        assert sp.expand(env[left]-env[right]-p-adjust) == 0, ix
        records.append(dict(equality=[left,right], source=str(sp.expand(p)), correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in schedule)
    assert len(schedule) == 55+5*fifo and counts['*'] == 28+3*fifo
    assert counts['+']+counts['-'] == 27+2*fifo
    assert len(equalities) == len(polynomials) == 13+3*fifo
    assert len(auxiliaries) == 19+2*fifo
    assert set().union(*(p.free_symbols for p in polynomials)) == set(z.values())
    return dict(operations=len(schedule), multiplications=counts['*'],
                additions_subtractions=counts['+']+counts['-'], equations=len(equalities),
                positive_parameters=parameters, positive_auxiliaries=auxiliaries,
                positive_existentials_excluding_x=(len(parameters)+len(auxiliaries)-1 if fifo else None),
                aliases={'n2':'q'}, instructions=[list(row) for row in schedule], sources=records,
                fixed_Y_residue='Y=3*s+1',
                scope='Exact positive Boolean ternary rails and even total population'+(' with initialized scalar FIFO' if fifo else ''))


def native_boolean(value,t):
    return 0 < value < 3**t and all(value//3**j % 3 <= 1 for j in range(t))


def pack(fields,q):
    return sum(F*q**j for j,F in enumerate(fields))


def prepower():
    cases = 0
    for q in range(5,31):
        for f0 in range(1,q-3):
            for f1 in range(1,q-f0-2):
                for f2 in range(1,q-f0-f1-1):
                    for f3 in range(1,q-f0-f1-f2):
                        fields=(f0,f1,f2,f3)
                        r=pack(fields,q)
                        assert q**3+q*q+q+1 <= r < q**4 and r>=156
                        X=q*(r//q+1);Y=4
                        a=Y*(X+1);E=X*Y;A=a+3;P=2*X*Y*Y+1
                        assert X>r and E>r+1 and a>2*r+1 and P>A
                        assert 6*X*Y*Y>a and r+2>=158
                        cases += 1
    return dict(arbitrary_positive_joint_bounded_fields=cases, q_range=[5,30],
                minimum_Y=4, minimum_r=156, paid_bound='X>r')


def typing_checks():
    rows=[]
    for t in (1,2,3,4):
        q=3**t
        candidates=accepted=0
        # Exhaustive positive sum bound, including every non-Boolean field.
        for f0 in range(1,q-3):
            for f1 in range(1,q-f0-2):
                for f2 in range(1,q-f0-f1-1):
                    for f3 in range(1,q-f0-f1-f2):
                        fields=(f0,f1,f2,f3);r=pack(fields,q)
                        arithmetic = prior.valuation(r)==0 and r%2==0
                        semantic = all(native_boolean(F,t) for F in fields) and sum(fields)%2==0
                        assert arithmetic == semantic
                        candidates+=1;accepted+=arithmetic
        rows.append(dict(t=t,q=q,positive_joint_bounded_fields=candidates,admitted=accepted))
    residue_cases=0
    for r in range(1,1000):
        value=r;population=0;boolean=True
        while value:
            digit=value%3;boolean &= digit<=1;population+=digit;value//=3
        assert (comb(2*r,r)%3!=0)==boolean
        if boolean:
            assert comb(2*r,r)%3 == pow(2,population,3)
            assert (comb(2*r,r)%3==1)==(r%2==0)
        residue_cases+=1
    return dict(field_domains=rows, direct_binomial_residue_cases=residue_cases)


def run(initial,appended,m,t):
    W=3**m;N=initial;D=0
    for j in range(t):
        d=N%3;a=appended//3**j%3
        D += d*3**j
        N=N//3+(W//3)*a
        assert 0<=N<W
    return D,N


def fifo_checks():
    checked=accepted=0;rows=[]
    for t in range(2,5):
        q=3**t
        bools=[sum(bit*3**j for j,bit in enumerate(bits)) for bits in product((0,1),repeat=t)]
        bools=bools[1:]
        subtotal=found=0
        for fields in product(bools,repeat=4):
            A=sum(fields[:2]);D=sum(fields[2:])
            if A+D>=q: continue
            r=pack(fields,q)
            for m in range(1,t+1):
                W=3**m
                for x in range(1,min((W+1)//2,5)):
                    arithmetic = D==2*x+W*A and r%2==0
                    semantic = run(2*x,A,m,t)==(D,0)
                    assert arithmetic == semantic
                    subtotal+=1;found+=arithmetic
        rows.append(dict(t=t,candidates=subtotal,admitted=found));checked+=subtotal;accepted+=found
    return dict(candidates=checked,admitted=accepted,domains=rows)


def split(value):
    first=second=0;place=1
    while value:
        digit=value%3
        first += (digit>=1)*place;second += (digit==2)*place
        value//=3;place*=3
    return first,second


def positive_maps():
    maps=[]
    for x in range(1,201):
        W=3;m=1
        while W<=2*x+1:W*=3;m+=1
        q=3*W;t=m+1;A=2;D=2*x+2*W
        fields=[1,1,*split(D)]
        r=pack(fields,q)
        assert all(native_boolean(F,t) for F in fields)
        assert D==2*x+W*A and sum(fields)<q and r%2==0 and prior.valuation(r)==0
        assert run(2*x,A,m,t)==(D,0)
        maps.append(dict(x=x,W=W,q=q,fields=fields,alpha=q-A-D,width_beta=W-2*x,L=3,r=str(r)))
    return dict(ordinary_positive_inputs=200, examples=[maps[0],maps[1],maps[9],maps[-1]],
                kernel_extension='Full positive modified-core map is proved; enormous Pell coordinates not materialized')


def prototypes():
    rows=[]
    for r,q in ((4,3),(10,9),(12,9)):
        result=prior.kernel.check_canonical_ratio(r)
        X=3**(2*r+1);Y=(X+1)**(2*r)//X**r
        assert X%q==0 and Y%3==1 and (Y-1)//3>0 and X>r
        rows.append(dict(result,q=q,modified_s_positive_integral=True))
    return dict(actual_main_first_pell_checks=rows,
                scope='Standalone modified-kernel prototypes, not admitted four-field source tuples')


def controller_schedules():
    base=source_check(True)
    general=[('bt_c0','*','weight0','F0'),('bt_c1','*','weight1','F1'),
             ('bt_c2','*','weight2','F2'),('bt_c3','*','weight3','F3'),
             ('bt_c01','+','bt_c0','bt_c1'),('bt_c23','+','bt_c2','bt_c3'),
             ('bt_csum','+','bt_c01','bt_c23'),('bt_cq','*','q_weight','q'),
             ('bt_cleft','+','bt_csum','bt_cq')]
    old_code=[('bt_sa','+','bt_append','F0'),('bt_sapp','*',8,'bt_sa'),
              ('bt_sr0','*',176,'F2'),('bt_sr1','*',80,'F3'),
              ('bt_sread','+','bt_sr0','bt_sr1'),('bt_sdiff','-','bt_sapp','bt_sread'),
              ('bt_soffset','*',27,'q'),('bt_sleft','+','bt_sdiff','bt_soffset')]
    zero_code=[('bt_zapp0','*',5,'F0'),('bt_zapp1','*',2,'F1'),
               ('bt_zread0','*',28,'F2'),('bt_zread1','*',56,'F3'),
               ('bt_zleft','+','bt_zapp1','bt_zread1'),
               ('bt_zright','+','bt_zapp0','bt_zread0')]
    names=base['positive_parameters']+base['positive_auxiliaries']
    z={name:sp.Symbol(name) for name in names+['weight0','weight1','weight2','weight3','q_weight','endpoint']}
    result={}
    for label,extra,left,right,total in [('general69',general,'bt_cleft','endpoint',69),
                                       ('old_code68',old_code,'bt_sleft',27,68),
                                       ('zero_code66',zero_code,'bt_zleft','bt_zright',66)]:
        env=prior.execute(base['instructions']+extra,dict(z,n2=z['q']))
        right_value=env[right] if isinstance(right,str) else right
        expected=(sum(z[f'weight{i}']*z[f'F{i}'] for i in range(4))+z['q_weight']*z['q']-z['endpoint']
                  if label=='general69' else
                  16*z['F0']+8*z['F1']-176*z['F2']-80*z['F3']+27*z['q']-27
                  if label=='old_code68' else
                  -5*z['F0']+2*z['F1']-28*z['F2']+56*z['F3'])
        assert sp.expand(env[left]-right_value-expected)==0
        count=Counter(row[1] for row in base['instructions']+extra)
        assert len(base['instructions']+extra)==total
        result[label]=dict(operations=total,multiplications=count['*'],
                           additions_subtractions=count['+']+count['-'],equations=17,
                           positive_existentials_excluding_x=27,extra_instructions=[list(row) for row in extra],
                           equality=[left,right],source=str(expected),
                           scope='Entire affine carry graph on positive Boolean rails; code filter and universal compiler unpaid')
    result['general69']['fixed_numerals']='weight_i=2*c_i, q_weight=h-2*cf, endpoint=h-2*cs'
    return result


def verify():
    return dict(status='PASS_DIRECT_BOOLEAN_TERNARY_FIFO60', source55=source_check(False),source60=source_check(True),
                prepower=prepower(),typing=typing_checks(),fifo=fifo_checks(),positive_maps=positive_maps(),
                prototypes=prototypes(),controller_schedules=controller_schedules(),
                dependency_sha256=hashlib.sha256(Path(prior.kernel.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
                scope='Exact component only; four supplied Boolean rails must all be nonzero; controller and universal compiler unpaid',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps(dict(status=result['status'],prepower=result['prepower'],typing=result['typing'],
                         fifo=result['fifo'],positive_inputs=result['positive_maps']['ordinary_positive_inputs'],
                         scope=result['scope']),indent=2))
