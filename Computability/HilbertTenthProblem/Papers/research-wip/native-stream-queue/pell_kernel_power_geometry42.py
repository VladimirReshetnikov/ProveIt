"""Strong42 power predicates using k=h*q, and their paired FIFO compositions."""
import argparse
from collections import Counter
import json
from pathlib import Path
import sympy as sp
import pell_kernel_power_two43 as binary
import pell_kernel_power_three43 as ternary
import native_binary_pair_fifo52 as binary_fifo
import native_ternary_pair_fifo50 as ternary_fifo


def shorten(rows):
    assert sum(row[0] == 'hpm1' for row in rows) == 1
    assert sum(row[0] == 'R11' for row in rows) == 1
    return [('R11', '*', 'h', 'q') if name == 'hpm1' else (name, op, left, right)
            for name, op, left, right in rows if name != 'R11']


def source_check(radix):
    prior = binary if radix == 2 else ternary
    z = {name: sp.Symbol(name) for name in prior.NAMES}
    rows = shorten(prior.SCHEDULE)
    sources = prior.sources(z)
    sources[4] = z['k']-z['h']*z['q']
    env = binary_fifo.execute(rows, z)
    U = (z['j']*z['c']-(2*z['r']+1) if radix == 2
         else z['j']*z['c']+(2*z['r']+1))
    correction = sources[8]*(U*U-z['y_aux']**2)
    records = []
    for ix, ((left, right), source) in enumerate(zip(prior.EQUALITIES, sources)):
        adjust = correction if ix == 9 else 0
        assert sp.expand(env[left]-env[right]-source-adjust) == 0, ix
        records.append(dict(equality=[left, right], source=str(sp.expand(source)),
                            correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in rows)
    assert len(rows) == 42 and counts['*'] == 25 and counts['+']+counts['-'] == 17
    assert len(sources) == len(prior.EQUALITIES) == 11
    assert set().union(*(source.free_symbols for source in sources)) == set(z.values())
    return dict(operations=42, multiplications=25, additions_subtractions=17,
                equations=11, radix=radix, positive_parameters=['q'],
                positive_auxiliaries=prior.NAMES[1:],
                instructions=[list(row) for row in rows], sources=records,
                exact_projection=f'q={radix}^t, integer t>=1',
                retained_strong_auxiliary_square=True)


def canonical_main(radix, q):
    r=q-1;J=2*r+1;X=radix**J;Y=(X+1)**(2*r)//X**r
    a=Y*(X+1);A=a+radix;delta=A*A-1;P=2*X*Y*Y+1
    d,c=binary.pell(A,J);first,k=binary.pell(P,q)
    assert X%q == Y%q == k%q == 0
    modulus=2*radix*a+radix*radix-1
    assert (d-X-a*c)%modulus == 0
    values=dict(q=q,r=r,w=X//q,s=Y//q,a=a,c=c,d=d,k=k,
                eta=c-Y*k,zeta=(Y+1)*k-c,tau=(first-1)//2,
                h=k//q,ga=(d-X-a*c)//modulus)
    assert min(values.values()) > 0
    prior=binary if radix==2 else ternary
    env=binary_fifo.execute(shorten(prior.SCHEDULE)[:28],values)
    for left,right in prior.EQUALITIES[:8]:
        assert env[left]==env[right],(radix,q,left,right)
    return values


def small_complete():
    z=canonical_main(2,2);A=z['a']+2;delta=A*A-1;c=z['c'];J=3;m=2*c*J
    f,v=binary.pell(A,m);quotient,remainder=divmod(v,c*c);assert remainder==0
    i=delta*quotient;R=i*c*c
    chi,y=binary.pell(R,J);u,remainder=divmod(chi,R);assert remainder==0
    o,remainder=divmod(u+c,f);assert remainder==0
    j,remainder=divmod(u+J,c);assert remainder==0
    z.update(f=f,i=i,y_aux=y,o=o,j=j)
    assert set(z)==set(binary.NAMES) and min(z.values())>0
    env=binary_fifo.execute(shorten(binary.SCHEDULE),z)
    for left,right in binary.EQUALITIES:assert env[left]==env[right],(left,right)
    return dict(q=2,r=1,h=z['h'],auxiliary_index=m,all_positive=True,
                all_eleven_equalities=True,
                coordinate_bit_lengths={name:value.bit_length() for name,value in z.items()})


def first_index_audit():
    cases=0
    for q in range(2,51):
        # P=1 modq follows before power recovery from X=wq and Y=sq.
        for multiplier in (1,2,7):
            P=1+multiplier*q
            for n in range(0,3*q+1):
                _,k=binary.pell(P,n)
                assert k%q==n%q
                cases+=1
        assert [n for n in range(1,2*q-1) if n%q==0] == [q]
    return dict(congruence_cases=cases,q_interval=[2,50],
                exact_argument='q divides n; q<=n<=p-1=2q-2; hence n=q')


def composed_source(radix, joint=False):
    old=(binary_fifo.source_check() if radix==2 else ternary_fifo.source_check(joint))
    z={name:sp.Symbol(name) for name in old['positive_parameters']+old['positive_auxiliaries']}
    rows=shorten(old['instructions']);env=binary_fifo.execute(rows,z)
    records=[]
    for ix,record in enumerate(old['sources']):
        source=(z['k']-z['h']*z['q'] if ix==4 else sp.sympify(record['source'],locals=z))
        correction=sp.sympify(record['correction'],locals=z)
        left,right=record['equality']
        assert sp.expand(env[left]-env[right]-source-correction)==0,ix
        records.append(dict(equality=[left,right],source=str(source),correction=str(correction)))
    counts=Counter(row[1] for row in rows)
    assert len(rows)==old['operations']-1
    assert counts['*']==old['multiplications']
    assert counts['+']+counts['-']==old['additions_subtractions']-1
    result=dict(old,operations=len(rows),additions_subtractions=old['additions_subtractions']-1,
                instructions=[list(row) for row in rows],sources=records)
    controller=(binary_fifo.controller_schedules(result) if radix==2 else ternary_fifo.controller(result))
    combined=rows+controller['extra_instructions']
    cc=Counter(row[1] for row in combined)
    controller.update(operations=len(combined),multiplications=cc['*'],
                      additions_subtractions=cc['+']+cc['-'])
    result['controller']=controller
    return result


def verify():
    examples=[]
    for radix,qs in ((2,(2,4,8,16,32)),(3,(3,9,27))):
        for q in qs:
            z=canonical_main(radix,q)
            examples.append(dict(radix=radix,q=q,h_bits=z['h'].bit_length(),
                                 all_eight_main_equalities=True,strictly_positive=True))
    return dict(status='PASS_STRONG_POWER_GEOMETRY42_AND_PAIRED_FIFOS',
                power_sources={str(b):source_check(b) for b in (2,3)},
                first_index=first_index_audit(),canonical_main_cases=examples,
                small_complete=small_complete(),
                paired_sources=dict(binary51=composed_source(2),
                                    ternary49=composed_source(3),
                                    ternary49_joint=composed_source(3,True)),
                scope='Exact strong binary/ternary powers and inherited paired FIFO projections; no universal controller or acceptance compiler',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps(dict(status=result['status'],first_index=result['first_index'],
                         counts={name:dict(operations=data['operations'],controller_operations=data['controller']['operations'])
                                 for name,data in result['paired_sources'].items()},
                         small_complete=result['small_complete'],scope=result['scope']),indent=2))
