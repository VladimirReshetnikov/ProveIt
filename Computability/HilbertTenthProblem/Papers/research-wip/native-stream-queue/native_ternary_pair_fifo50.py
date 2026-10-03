"""Exact paired ternary FIFO50 and a raw-to-delimited finite loader."""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import sympy as sp
import pell_kernel_power_three43 as geometry

PARAMETERS=['x','W','q','read0','read1','append0','append1']
FIFO=[('input_bound','+','x','beta'),('total_time','*','W','L'),
      ('appended0','*','W','append0'),('transport0','+','x','appended0'),
      ('appended1','*','W','append1')]
BOUNDS=[('read_bound0','+','read0','alpha0'),('read_bound1','+','read1','alpha1')]
JOINT=[('read_sum','+','read0','read1'),('joint_bound','+','read_sum','alpha')]


def source_check(joint=False):
    auxiliaries=geometry.prior.CORE_NAMES+['L','beta']+(['alpha'] if joint else ['alpha0','alpha1'])
    z={name:sp.Symbol(name) for name in PARAMETERS+auxiliaries}
    schedule=geometry.SCHEDULE+FIFO+(JOINT if joint else BOUNDS)
    env=geometry.prior.execute(schedule,z)
    equations=geometry.EQUALITIES+[
        ('W','input_bound'),('q','total_time'),('read0','transport0'),('read1','appended1')]
    sources=geometry.sources(z)+[z['W']-z['x']-z['beta'],z['q']-z['W']*z['L'],
        z['read0']-z['x']-z['W']*z['append0'],z['read1']-z['W']*z['append1']]
    if joint:
        equations += [('joint_bound','q')]
        sources += [z['read0']+z['read1']+z['alpha']-z['q']]
    else:
        equations += [('read_bound0','q'),('read_bound1','q')]
        sources += [z['read0']+z['alpha0']-z['q'],z['read1']+z['alpha1']-z['q']]
    U=2*z['r']+1+z['j']*z['c'];correction=sources[8]*(U*U-z['y_aux']**2)
    records=[]
    for ix,((left,right),source) in enumerate(zip(equations,sources)):
        adjust=correction if ix==9 else 0
        assert sp.expand(env[left]-env[right]-source-adjust)==0,(joint,ix)
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),correction=str(sp.expand(adjust))))
    counts=Counter(row[1] for row in schedule)
    assert len(schedule)==50 and counts['*']==28 and counts['+']+counts['-']==22
    assert len(equations)==17-joint and len(auxiliaries)==21-joint
    assert set().union(*(p.free_symbols for p in sources))==set(z.values())
    return dict(operations=50,multiplications=28,additions_subtractions=22,equations=17-joint,
                positive_parameters=PARAMETERS,positive_auxiliaries=auxiliaries,
                positive_witnesses_excluding_x=27-joint,joint_read_bound=joint,
                instructions=[list(row) for row in schedule],sources=records)


def digits(n,t):return [n//3**j%3 for j in range(t)]
def word(digits):return sum(d*3**j for j,d in enumerate(digits))


def direct_fifo(x,W,reads,appends):
    N=[x,0]
    for read,append in zip(reads,appends):
        if any(N[i]%3!=read[i] for i in (0,1)):return False
        N=[N[i]//3+(W//3)*append[i] for i in (0,1)]
        assert all(0<=n<W for n in N)
    return N==[0,0]


def bounded_streams():
    checked=admitted=joint_admitted=0
    for t in (2,3):
        q=3**t
        for m in range(1,t+1):
            W=3**m
            for x in range(1,min(W,5)):
                for D0,D1,A0,A1 in product(range(1,q),repeat=4):
                    arithmetic=D0==x+W*A0 and D1==W*A1
                    reads=list(zip(digits(D0,t),digits(D1,t)))
                    appends=list(zip(digits(A0,t),digits(A1,t)))
                    assert arithmetic==direct_fifo(x,W,reads,appends)
                    if arithmetic:
                        assert t>=m+1 and 0<A0<q and 0<A1<q
                        admitted+=1;joint_admitted+=D0+D1<q
                    checked+=1
    return dict(arbitrary_positive_stream_tuples=checked,admitted=admitted,
                admitted_joint_read_bound=joint_admitted,maximum_t=3)


def bare_inputs():
    for x in range(1,201):
        W=3;m=1
        while W<=x:W*=3;m+=1
        q=3*W;t=m+1;D0=x+W;D1=W
        assert D0+D1<q
        assert direct_fifo(x,W,list(zip(digits(D0,t),digits(D1,t))),[(1,1)]+[(0,0)]*m)
    return dict(positive_inputs=200,positive_append_streams=[1,1],joint_bound_already_strict=True)


def delayed_loader(raw):
    """Return the handoff word or reject when the highest raw trit is nonzero."""
    queue=[(d,0) for d in raw];state=None;rows=[]
    first=queue.pop(0);queue.append((0,1));state=first[0]
    rows.append((first,(0,1)))
    while True:
        read=queue.pop(0)
        if read==(0,1):
            if state!=0:return None,rows
            queue.append((0,1));rows.append((read,(0,1)))
            return queue,rows
        assert read[1]==0
        append=(state,0);state=read[0];queue.append(append);rows.append((read,append))


def loader_checks():
    tested=accepted=0
    for m in range(1,7):
        W=3**m
        for x in range(1,W):
            raw=digits(x,m);out,rows=delayed_loader(raw)
            assert (out is not None)==(x<W//3)
            if out is not None:
                assert out==[(d,0) for d in raw[:-1]]+[(0,1)]
                assert len(rows)==m+1
                assert sum(a[0] for _,a in rows)>0 and sum(a[1] for _,a in rows)>0
                accepted+=1
            tested+=1
    return dict(positive_raw_inputs_and_widths=tested,accepted_prefixes=accepted,maximum_width=3**6,
                exact_projection='Accepts iff x<W/3, then outputs the original handoff initial queue',
                arithmetic_cost='No added arithmetic; this finite control is still an unpaid compiler obligation')


def controller(source):
    words=['read0','read1','append0','append1']
    extra=[(f'pair_control_p{i}','*',f'weight{i}',word) for i,word in enumerate(words)]+[
        ('pair_control_s01','+','pair_control_p0','pair_control_p1'),
        ('pair_control_s012','+','pair_control_s01','pair_control_p2'),
        ('pair_control_s0123','+','pair_control_s012','pair_control_p3'),
        ('pair_control_q','*','q_coefficient','q'),
        ('pair_control_left','+','pair_control_s0123','pair_control_q')]
    z={name:sp.Symbol(name) for name in source['positive_parameters']+source['positive_auxiliaries']+
       [f'weight{i}' for i in range(4)]+['q_coefficient','comparison_constant']}
    env=geometry.prior.execute(source['instructions']+extra,z)
    raw=sum(z[f'weight{i}']*z[word] for i,word in enumerate(words))
    expected=raw+z['q_coefficient']*z['q']-z['comparison_constant']
    assert sp.expand(env['pair_control_left']-z['comparison_constant']-expected)==0
    c=sp.symbols('c0:4');h,cs,cf=sp.symbols('h cs cf')
    replacement={z[f'weight{i}']:2*c[i] for i in range(4)}
    replacement.update({z['q_coefficient']:h-2*cf,z['comparison_constant']:h-2*cs})
    global_carry=2*sum(c[i]*z[word] for i,word in enumerate(words))+h*(z['q']-1)+2*cs-2*z['q']*cf
    assert sp.expand(expected.subs(replacement)-global_carry)==0
    assert len(extra)==9 and Counter(row[1] for row in extra)=={'*':5,'+':4}
    return dict(operations=59,multiplications=33,additions_subtractions=26,
                equations=source['equations']+1,extra_instructions=[list(row) for row in extra],
                equality=['pair_control_left','comparison_constant'],
                fixed_constants='weight_i=2ci; q_coefficient=h-2cf; comparison_constant=h-2cs',
                scope='Entire unfiltered affine carry graph; does not certify the delayed loader or original finite controller')


def verify():
    sources={str(joint):source_check(joint) for joint in (False,True)}
    return dict(status='PASS_COMPLETE_NATIVE_TERNARY_PAIR_FIFO_50',sources=sources,
                bounded_streams=bounded_streams(),bare_inputs=bare_inputs(),loader=loader_checks(),
                controllers={joint:controller(source) for joint,source in sources.items()},
                scope='Exact paired raw FIFO and finite loader semantics; arithmetic controller and universal acceptance remain unpaid',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps({key:value for key,value in result.items() if key not in ('sources','controllers')},indent=2))
