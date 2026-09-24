"""Fixed tag startup on repeated raw ternary input, with honest symbol tracks."""
from itertools import product
from pathlib import Path
import json
import math
import sympy as sp


def value(word):
    return sum(d*3**i for i,d in enumerate(word))


def schedule(beta, paid_coprime=False):
    assert beta>=2
    K=3**beta
    dag=[]
    for i in range(2,beta+1):
        dag.append((f'L{i}','*','L' if i==2 else f'L{i-1}','L'))
    dag.append(('geometric1','+',1,'L'))
    for i in range(2,beta):
        dag.append((f'geometric{i}','+',f'geometric{i-1}',f'L{i}'))
    dag += [('copies','*','x',f'geometric{beta-1}'),
            ('N0','*',K,'copies'), ('marker_scale','*',2*K,f'L{beta}'),
            ('N1','+','marker_scale',1), ('Winit','*',K*K,f'L{beta}'),
            ('input_bound','+','x','alpha')]
    if paid_coprime:
        for i in range(2,beta+1):
            dag.append((f'Y{i}','*','Y' if i==2 else f'Y{i-1}','Y'))
        dag.append(('length_phase','*',3,f'Y{beta}'))
    return dag


def evaluate(dag, values):
    env=dict(values)
    for name,op,left,right in dag:
        assert name not in env
        a=env[left] if isinstance(left,str) else left
        b=env[right] if isinstance(right,str) else right
        env[name]=a*b if op=='*' else a+b
    return env


def verify_source():
    x,L,alpha,Y=sp.symbols('x L alpha Y')
    records=[]
    for beta in range(2,8):
        for paid in (False,True):
            dag=schedule(beta,paid)
            env=evaluate(dag,dict(x=x,L=L,alpha=alpha,Y=Y))
            K=3**beta
            assert sp.expand(env['N0']-K*x*sum(L**i for i in range(beta)))==0
            assert sp.expand(env['N1']-1-2*K*L**beta)==0
            assert sp.expand(env['Winit']-K*K*L**beta)==0
            assert env['input_bound']==x+alpha
            if paid:assert sp.expand(env['length_phase']-3*Y**beta)==0
            mul=sum(op=='*' for _,op,_,_ in dag)
            add=len(dag)-mul
            assert (mul,add)==(beta+3+(beta if paid else 0),beta+1)
            records.append(dict(beta=beta,paid_length_phase=paid,
                                operations=len(dag),multiplications=mul,additions=add))
    return dict(deletion_two=records[:2],general_schedules=records,
                deletion_two_dag=schedule(2),duplicate_only_operations=2,
                initial_nonzero_coordinate_count=2,
                scope='Power-three geometry remains external; the paid phase equation is optional. Zero coordinate adapters and the complete target simulator are excluded.')


def encode_tracks(word,codes,k):
    return tuple(sum(codes[s][i]*3**j for j,s in enumerate(word)) for i in range(k))


def verify_loader():
    sigma,tau='sigma','tau'
    work=('a','b','c','d','e','f')
    k=3
    codes={d:(d,0,0) for d in range(3)}
    codes.update({sigma:(0,1,0),tau:(0,2,0)})
    available=[v for v in product(range(3),repeat=k) if v not in codes.values()]
    codes.update(zip(work,available))
    assert len(set(codes.values()))==len(codes)
    profiles=[(('a','b'),{0:('c','d'),1:('d','e'),2:('e','f')},('a','f')),
              (('a',),{0:(),1:('b',),2:('c','d','e')},()),
              ((),{0:('a','a'),1:('b','b','b'),2:('c',)},('d','e','f'))]
    dims=[(2,1),(2,3),(2,5),(2,7),(3,1),(3,2),(3,4),(3,5),(4,1),(4,3),(4,5)]
    cases=steps=zero_inputs=high_zero_inputs=phase_cases=0
    for beta,ell in dims:
        assert math.gcd(beta,ell)==1
        K,L=3**beta,3**ell
        order=[j*beta%ell for j in range(ell)]
        assert sorted(order)==list(range(ell))
        for w in product(range(3),repeat=ell):
            x=value(w)
            initial=(sigma,)+(0,)*(beta-1)+w*beta+(tau,)+(0,)*(beta-1)
            initial_tracks=encode_tracks(initial,codes,k)
            env=evaluate(schedule(beta),dict(x=x,L=L,alpha=L-x))
            assert env['input_bound']==L and L-x>0
            assert initial_tracks==(env['N0'],env['N1'],0)
            assert 3**len(initial)==env['Winit']
            assert all(0<=n<env['Winit'] for n in initial_tracks)
            if ell%beta==1:
                Y=3**((ell-1)//beta)
                penv=evaluate(schedule(beta,True),dict(x=x,L=L,alpha=L-x,Y=Y))
                assert penv['length_phase']==L
                phase_cases+=1
            for P,h,T in profiles:
                rules={sigma:P,tau:T,**h}
                current=initial;read=[]
                for step in range(ell+2):
                    assert len(current)>=beta
                    head=current[0]
                    assert head in rules  # A target/work rule is never read.
                    if step==0:assert head==sigma
                    elif step==ell+1:assert head==tau
                    else:read.append(head)
                    app=rules[head]
                    before=encode_tracks(current,codes,k)
                    deleted=encode_tracks(current[:beta],codes,k)
                    append=encode_tracks(app,codes,k)
                    W=3**len(current)
                    nxt=current[beta:]+app
                    after=encode_tracks(nxt,codes,k)
                    assert all(K*after[i]==before[i]-deleted[i]+append[i]*W for i in range(k))
                    assert K*3**len(nxt)==3**len(app)*W
                    current=nxt;steps+=1
                expected=P+tuple(s for i in order for s in h[w[i]])+T
                assert tuple(read)==tuple(w[i] for i in order) and current==expected
                restored=[None]*ell
                for i,d in zip(order,read):restored[i]=d
                assert tuple(restored)==w
                cases+=1;zero_inputs+=int(x==0);high_zero_inputs+=int(w[-1]==0)
    # Without coprimality, duplication really can forget an input symbol.
    assert [(0,0)[2*j%2] for j in range(2)]==[(0,1)[2*j%2] for j in range(2)]
    return dict(dimensions=dims,fixed_profiles=len(profiles),loading_cases=cases,
                exact_scalar_transition_checks=steps*k,loading_steps=steps,
                zero_input_cases=zero_inputs,high_zero_padded_cases=high_zero_inputs,
                paid_phase_cases=phase_cases,noncoprime_loss_examples=1,
                coordinate_count_in_test=k,
                scope='Complete small ternary-word enumeration, not a universal-target simulation. Every prefix/body/endpoint step and its scalar coordinate identity is checked.')


def verify():
    return dict(status='PASS_DUPLICATED_TAG_INPUT_LOADER',source=verify_source(),
                finite=verify_loader(),proof='../1980/EXPLORATION_DUPLICATED_TAG_INPUT_LOADER.md',
                scope='Exact fixed combinatorial startup and radix-preserving input formulas. A universal target with the resulting startup format, full mask/geometry realization and positive adapters remain unproved here.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['source']['deletion_two']);print(result['finite'])
