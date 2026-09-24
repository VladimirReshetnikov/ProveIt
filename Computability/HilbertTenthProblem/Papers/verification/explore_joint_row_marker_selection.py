"""Joint one-marker and selector component: ten operations, seven masks."""
from itertools import product
from pathlib import Path
import json
import sympy as sp


def boolean(n):
    if n < 0:
        return False
    while n:
        n, digit = divmod(n, 3)
        if digit == 2:
            return False
    return True


def words(width):
    out = [0]
    power = 1
    for _ in range(width):
        out += [v+power for v in out]
        power *= 3
    return out


def schedule(C):
    return [('radix','*',C,'A'), ('guard','*','A','H'),
            ('Qsum','+','Q0','Q1'), ('Qguard','+','Qsum','guard'),
            ('headsum','+','S0','S1'),
            ('twiceQ0','*',2,'Q0'), ('marker0','+','twiceQ0','S0'),
            ('twiceQ1','*',2,'Q1'), ('marker1','+','twiceQ1','S1'),
            ('lengthsum','+','M0','M1')]


def run(dag, env):
    env = dict(env)
    for name, op, left, right in dag:
        x = env[left] if isinstance(left, str) else left
        y = env[right] if isinstance(right, str) else right
        env[name] = x*y if op == '*' else x+y
    return env


def verify_source():
    names = 'A H Q0 Q1 S0 S1 M0 M1 R L C'.split()
    s = dict(zip(names, sp.symbols(' '.join(names))))
    env = run(schedule(s['C']), s)
    comparisons = [('radix','R'),('headsum','H'),('marker0','M0'),
                   ('marker1','M1'),('lengthsum','L')]
    source = [s['C']*s['A']-s['R'], s['S0']+s['S1']-s['H'],
              2*s['Q0']+s['S0']-s['M0'],
              2*s['Q1']+s['S1']-s['M1'], s['M0']+s['M1']-s['L']]
    assert all(sp.expand(env[a]-env[b]-p) == 0 for (a,b),p in zip(comparisons, source))
    assert sp.expand(env['Qguard']-s['Q0']-s['Q1']-s['A']*s['H']) == 0
    assert len(schedule(3)) == 10
    assert sum(row[1] == '*' for row in schedule(3)) == 4
    return dict(operations=10,multiplications=4,additions=6,
                comparisons=5,masked_words=7,
                masks=['Q0','Q1','S0','S1','M0','M1','Qguard'],
                unmasked_derived_words=['L','Qsum'],
                dag=schedule(3),source_residuals=[sp.sstr(p) for p in source])


def exact_form(Q0,Q1,S0,S1,M0,M1,R,t,b):
    for _ in range(t):
        Q0,q0=divmod(Q0,R);Q1,q1=divmod(Q1,R)
        S0,s0=divmod(S0,R);S1,s1=divmod(S1,R)
        M0,m0=divmod(M0,R);M1,m1=divmod(M1,R)
        assert (s0,s1) in ((0,1),(1,0))
        ell=m0+m1
        powers=[3**p for p in range(b+1)]
        assert ell in powers
        assert m0 == s0*ell and m1 == s1*ell
        assert q0 == s0*(ell-1)//2 and q1 == s1*(ell-1)//2
    assert Q0==Q1==S0==S1==M0==M1==0


def verify_finite():
    candidates=accepted=converse=dag_cases=0
    zero_intervals=zero_marker_channels=all_head_lengths=0
    dimensions=[(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)]
    for m,t in dimensions:
        R=3**m;bound=R**t;H=(bound-1)//(R-1)
        ws=words(m*t);heads=[sum(s*R**j for j,s in enumerate(ss)) for ss in product((0,1),repeat=t)]
        allowed=set(ws)
        for b in range(m):
            A=3**b;C=3**(m-b);guard=A*H
            for Q0 in ws:
                for Q1 in ws:
                    Qguard=Q0+Q1+guard
                    for S0 in heads:
                        candidates+=1
                        S1=H-S0;M0=2*Q0+S0;M1=2*Q1+S1
                        # Neither Qsum nor L is filtered here.
                        if Qguard not in allowed or M0 not in allowed or M1 not in allowed:
                            continue
                        exact_form(Q0,Q1,S0,S1,M0,M1,R,t,b)
                        assert boolean(Q0+Q1) and boolean(M0+M1)
                        accepted+=1
            choices=list(product((0,1),range(b+1)))
            for local in product(choices,repeat=t):
                Q0=Q1=S0=S1=M0=M1=0
                for j,(selected,p) in enumerate(local):
                    w=R**j;mark=3**p;interval=(mark-1)//2
                    if selected==0:Q0+=interval*w;S0+=w;M0+=mark*w
                    else:Q1+=interval*w;S1+=w;M1+=mark*w
                env=run(schedule(C),dict(A=A,H=H,Q0=Q0,Q1=Q1,S0=S0,S1=S1,M0=M0,M1=M1))
                assert env['radix']==R and env['headsum']==H
                assert env['marker0']==M0 and env['marker1']==M1
                assert env['lengthsum']==M0+M1
                assert all(0<=v<bound and boolean(v) for v in (Q0,Q1,S0,S1,M0,M1,env['Qguard']))
                assert M0+M1 < bound and Q0+Q1 < bound
                zero_intervals+=int(Q0==0 or Q1==0)
                zero_marker_channels+=int(M0==0 or M1==0)
                all_head_lengths+=int(Q0==Q1==0)
                converse+=1;dag_cases+=1
    assert accepted==converse
    return dict(dimensions=dimensions,complete_candidates=candidates,
                accepted=accepted,converse=converse,dag_cases=dag_cases,
                converse_with_zero_interval=zero_intervals,
                converse_with_zero_marker_channel=zero_marker_channels,
                converse_with_all_head_markers=all_head_lengths)


def verify_omissions():
    # Omit only the shared guard mask: one interval crosses a row.
    R,H,A=9,10,3
    Q0,Q1,S0,S1=4,0,1,9
    M0,M1=2*Q0+S0,2*Q1+S1
    assert all(boolean(v) and v<R**2 for v in (Q0,Q1,S0,S1,M0,M1))
    assert not boolean(Q0+Q1+A*H) and M0==M1==9
    # Omit only Q0's mask: the shared guard can conceal a digit two.
    Q0,Q1,S0,S1=6,0,1,9
    M0,M1=2*Q0+S0,2*Q1+S1
    assert not boolean(Q0)
    assert all(boolean(v) and v<R**2 for v in (Q1,S0,S1,M0,M1,Q0+Q1+A*H))
    # Omit only M1's mask: even a separately one-hot L does not repair it.
    R,H,A=9,1,3
    Q0,Q1,S0,S1=0,1,1,0
    M0,M1=2*Q0+S0,2*Q1+S1
    assert all(boolean(v) and v<R for v in (Q0,Q1,S0,S1,M0,Q0+Q1+A*H))
    assert not boolean(M1) and M0+M1==3 and M0!=S0*(M0+M1)
    return dict(exact_omission_examples=3,
                scope='Separate failures when the shared guard, Q0, or M1 mask is omitted; no global minimality claim.')


def verify():
    return dict(status='PASS_JOINT_ROW_MARKER_SELECTION',source=verify_source(),
                finite=verify_finite(),omissions=verify_omissions(),
                proof='../1980/EXPLORATION_JOINT_ROW_MARKER_SELECTION.md',
                scope='Conditional nonnegative component: exact10 operations and7 mask words, including any fixed padding depth. Radix geometry, packed bounds, Boolean-mask implementation, positive adapters, tag input and halting remain external.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
