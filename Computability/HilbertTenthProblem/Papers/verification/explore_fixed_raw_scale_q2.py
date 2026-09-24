#!/usr/bin/env python3
"""Reject the 81-source scale deletion q^3 -> q^2; no smaller certificate."""
from collections import Counter
from itertools import product
from math import comb
from pathlib import Path
import hashlib
import json
import sys
import sympy as sp

import explore_fixed_raw_universal_81 as previous

OUT = Path(__file__).with_suffix('.json')
ROOT = Path(__file__).resolve().parents[2]
NAMES = list(previous.NAMES)
EQUALITIES = list(previous.EQUALITIES)
SCHEDULE = [(name, op, 'Lbig' if left == 'n2' else left,
             'Lbig' if right == 'n2' else right)
            for name, op, left, right in previous.SCHEDULE if name != 'n2']
OUTER = SCHEDULE[:23]


def source_residuals():
    z = previous.SYM
    return [sp.expand(s.subs({z['w']:z['w']/z['q'], z['s']:z['s']/z['q']}, simultaneous=True))
            for s in previous.source_residuals()]


def verify_source():
    z = previous.SYM
    env = previous.fixed_environment(z)
    previous.bridge.baseline.run_schedule(SCHEDULE, env)
    sources = source_residuals()
    U = z['j']*z['c']-(2*z['r']+1)
    correction = sources[14]*(U*U-z['y_aux']**2)
    records = []
    for index, ((left, right), source) in enumerate(zip(EQUALITIES, sources)):
        actual = sp.expand(env[left]-env[right])
        adjust = correction if index == 15 else sp.Integer(0)
        sign = 1 if sp.expand(actual-source-adjust) == 0 else -1
        assert sp.expand(actual-sign*source-adjust) == 0, index
        assert sp.denom(source) == 1
        records.append(dict(index=index, equality=[left,right], source_sign=sign,
                            source=sp.sstr(source), correction=sp.sstr(sp.expand(adjust))))
    primitives, counts = previous.bridge.verify_primitives(SCHEDULE, env)
    assert counts == {'*':43, '+':37} and len(primitives) == 80
    assert len(NAMES) == 33 and len(sources) == 21
    assert len(OUTER) == 23
    assert Counter(row[1] for row in OUTER)['*'] == 11
    changed = [i for i,(a,b) in enumerate(zip(sources, previous.source_residuals())) if sp.expand(a-b)]
    assert changed == [7,8,10,11,12]
    assert not any(item == 'n2' for row in SCHEDULE for item in row)
    return dict(operations=80, multiplications=43, additions_subtractions=37,
                positive_unknowns=NAMES, positive_unknown_count=33, equations=21,
                deleted_instruction=['n2','*','Lbig','q'], changed_source_indices=changed,
                primitive_instructions=primitives, sources=records,
                ledger={'outer':23,'retained_kernel':43,'input_bridge':14})


def empty_machine():
    states, alphabet = ('q0','q1','H'), (0,1,2)
    table = {(q,a): ('H',a,0) if q == 'H' else
             ('q1',2 if q == 'q0' and a == 1 else a,0)
             for q in states for a in alphabet}
    return previous.unary.old.Machine(states, alphabet, 'q0', 'H', 0, table)


def four_window_relation():
    machine = empty_machine()
    pred = previous.helical.predicate(machine)
    start, end = previous.fixed_markers(machine)
    blank = (previous.tile(0,0,(0,None)),)*9
    ones = (previous.tile(0,0,(1,None)),)*9
    windows = (end,start,blank,ones)
    assert len(set(windows)) == 4 and all(pred(w) for w in windows)
    assert all(machine.delta(q,a)[0] != machine.halt
               for q in ('q0','q1') for a in machine.alphabet)
    allowed = frozenset(t for t in product(range(4), repeat=3)
                       if previous.unary.blocks.three_valid(*(windows[j] for j in t),pred))
    assert allowed == frozenset(((2,2,2),(3,3,3)))
    return windows, allowed


def verify_scalar():
    _, actual = four_window_relation()
    examples = [('four explicit machine windows',4,actual),
                ('all triples',4,None), ('no triples',4,frozenset()),
                ('asymmetric five-state rule',5,frozenset(t for t in product(range(5),repeat=3)
                                                         if (t[0]+2*t[1]+3*t[2])%5 != 0))]
    records = []
    for name,k,allowed in examples:
        cc = previous.bridge.previous.compile_rule(k,allowed)
        assert cc.padding == 0 and cc.A >= 16 and cc.m >= 3
        mass = sum(cc.c)
        assert cc.mu < 4*mass and 5*mass <= (cc.m+2)*mass <= cc.R-2
        cases = losses = 0
        for triple in product(range(k), repeat=3):
            cells = [cc.R**state for state in triple]
            field = sum(coef*cell for coef,cell in zip(cc.Ds,cells))
            phi = sum(cc.c[s*k+state] for s,state in enumerate(triple))
            expected = int(allowed is not None and triple not in allowed)
            assert 0 < field < field+cc.MF < cc.B
            assert field.bit_count()+cc.MF.bit_count()-(field+cc.MF).bit_count() == expected
            assert phi.bit_count()+cc.mu.bit_count()-(phi+cc.mu).bit_count() == expected
            # Inspect every clause independently, including its radix carry bound.
            rowbits = tuple(int(i == triple[s]) for s in range(3) for i in range(k))
            clause_loss = 0
            for weights,mask in cc.clauses:
                value = sum(w*b for w,b in zip(weights,rowbits))
                assert value+mask < cc.A
                loss = value.bit_count()+mask.bit_count()-(value+mask).bit_count()
                assert loss in (0,1)
                clause_loss += loss
            assert clause_loss == expected
            cases += 1; losses += expected
        records.append(dict(name=name,k=k,triples=cases,bad_triples=losses,A=cc.A,
                            m=cc.m,padding=cc.padding,R_bits=cc.R.bit_length()-1,B_bits=cc.d))
    return records


def outer_tuple(cc, allowed, states, h, x):
    N, B = len(states), cc.B
    assert states[0] == 1 and states[x] == 0 and states.count(0) == states.count(1) == 1
    assert 1 <= h <= N and 0 < x < N-1
    cells = [cc.R**a for a in states]
    pack = lambda values: sum(v*B**i for i,v in enumerate(values))
    C = pack(cells)
    right = pack([cells[(i-1)%N] for i in range(N)])
    nxt = pack([cells[(i-h)%N] for i in range(N)])
    Fdigits = [cc.Ds[0]*cells[i]+cc.Ds[1]*cells[(i-1)%N]+cc.Ds[2]*cells[(i-h)%N]
               for i in range(N)]
    F = pack(Fdigits)
    assert F == cc.Ds[0]*C+cc.Ds[1]*right+cc.Ds[2]*nxt
    assert all(0 < digit+cc.MF < B for digit in Fdigits)
    q,P,W,u = B**N,B**h,B**x,cc.d*x
    J, Lambda = (q-1)//(B-1),q*q
    Z = C-cc.R-W
    kR, rem = divmod(B*C-right,q-1); assert rem == 0
    kY, rem = divmod(P*C-nxt,q-1); assert rem == 0
    zquot = cc.Ds[1]*kR+cc.Ds[2]*kY
    packed, mask = Z+q*F,(cc.MC+q*cc.MF)*J
    r = (Lambda-packed)*(Lambda-1)+mask
    V = sum(allowed is not None and (states[i],states[(i-1)%N],states[(i-h)%N]) not in allowed
            for i in range(N))
    assert 0 < Z < C < q and 0 < W < q and 0 < F < q-1
    assert Z&(cc.MC*J) == 0 and 0 < packed < packed+mask < Lambda
    assert mask.bit_count() == cc.d*N
    assert packed.bit_count()+mask.bit_count()-(packed+mask).bit_count() == V
    assert r.bit_count() == 3*cc.d*N-V >= 2*cc.d*N
    assert r%2 and q*q <= r < q**4
    assert 0 <= V <= N and (F&(cc.MF*J) == 0) == (V == 0)
    values = dict(q=q,P=P,C=C,v=q//P,Jrep=J,align=(P-1)//(B-1),F=F,
                  alpha=q-C-u,zquot=zquot,Z=Z,r=r,W=W,x=x)
    assert min(values.values()) > 0 and kR >= 1 and kY >= 1
    env = previous.fixed_environment(dict(previous.bridge.previous.constants(cc),cell_bits=cc.d,**values))
    previous.bridge.baseline.run_schedule(OUTER,env)
    assert all(env[a] == env[b] for i,(a,b) in enumerate(EQUALITIES[:7]) if i != 3)
    assert env['bounded']+u == q
    return values, dict(N=N,h=h,x=x,states=list(states),forbidden_actual_triples=V,
                        q_bits=cc.d*N,packed_index_bits=r.bit_length(),valuation=r.bit_count(),
                        old_required_valuation=3*cc.d*N,new_required_valuation=2*cc.d*N,
                        r_sha256=hashlib.sha256(r.to_bytes((r.bit_length()+7)//8,'big')).hexdigest())


def pell(A,index):
    D = A*A-1
    result, base = (1,0),(A,1)
    while index:
        if index&1:
            x,y=result;u,v=base;result=(x*u+D*y*v,x*v+y*u)
        index >>= 1
        if index:
            x,y=base;base=(x*x+D*y*y,2*x*y)
    return result


def verify_words_and_bridge():
    windows, allowed = four_window_relation()
    cc = previous.bridge.previous.compile_rule(4,allowed)
    cases = failures = bridge_cases = 0
    records = []
    for N in range(4,8):
        for x,h,mode in product(range(1,N-1),(1,2,N),range(2)):
            states = [1]+[2+(mode*i)%2 for i in range(1,N)]
            states[x] = 0
            values, info = outer_tuple(cc,allowed,states,h,x)
            assert info['forbidden_actual_triples'] > 0
            cases += 1; failures += info['forbidden_actual_triples']
            if N == 4 and x == h == 1 and mode == 0:
                records.append(info)
                # Same actual outer tuple, moderate independent Pell base.
                # This verifies the adapter, not a materialized full kernel.
                u = cc.d*x;A=8;a=A-2;D=A*A-1;modulus=4*a+3
                mu,kappa = pell(A,u);c=pell(A,u+5)[1]
                delta, rem = divmod(kappa-u,a+1); assert rem == 0
                rho, rem = divmod(mu-a*kappa-values['W'],modulus); assert rem == 0
                phi = c-kappa
                assert min(delta,rho,phi)>0
                env = previous.fixed_environment(dict(previous.bridge.previous.constants(cc),cell_bits=cc.d,**values))
                previous.bridge.baseline.run_schedule(OUTER,env)
                env.update(a=a,A=D,a4m5=modulus,c=c,kappa=kappa,mu=mu,delta=delta,phi=phi,rho=rho)
                previous.bridge.baseline.run_schedule(previous.ADAPTER,env)
                assert env['raw_bound']==env['q']
                assert all(env[l]==env[r] for l,r in EQUALITIES[17:])
                bridge_cases += 1
    assert records[0]['forbidden_actual_triples'] == 3
    return dict(cases=cases,invalid_local_rows=failures,materialized_example=records[0],
                example_state_windows=windows,exact_four_window_relation=sorted(allowed),
                bridge_cases=bridge_cases,all_seven_outer_equations_checked=True,
                bridge_uses_moderate_independent_main_Pell_parameter=True,
                finite_subalphabet_only_materialized=True,
                full_machine_alphabet_handled_by_general_proof=True)


def verify_canonical_main():
    records=[]
    for r in (5,9,17,65):
        exponent = r.bit_count()
        D0=1<<exponent;J=2*r+1;X=1<<J
        Y=sum(comb(2*r,r+j)*X**j for j in range(r+1))
        assert Y%D0 == X%D0 == 0
        a=Y*(X+1);A=a+2;D=A*A-1;Q=X*Y*Y;P=2*Q+1
        d,c=pell(A,J);chi,k=pell(P,r+1)
        eta=c-k*Y;zeta=k-eta
        tau, rem=divmod(chi-1,2);assert rem==0
        h, rem=divmod(k-r-1,X*Y);assert rem==0
        gamma,rem=divmod(d-X-a*c,4*a+3);assert rem==0
        assert min(eta,zeta,tau,h,gamma)>0
        assert X*Y*Y*(X*Y*Y+1)*k*k == tau*(tau+1)
        assert d*d-D*c*c == 1
        assert Y*X**r < (X+1)**(2*r) < (4*Y+1)*X**r//4
        assert 4*c < (4*Y+3)*k
        records.append(dict(r=r,D0=D0,c_bits=c.bit_length(),k_bits=k.bit_length(),
                            all_main_witnesses_positive=True))
    return records


def verify_odd_auxiliary():
    records=[]
    for A,J in ((2,3),(2,7),(3,3)):
        d,c=pell(A,J);D=A*A-1
        f,psim=pell(A,2*c*J);R=D*psim
        i,rem=divmod(R,c*c);assert rem==0
        chi,y=pell(R,J);U,rem=divmod(chi,R);assert rem==0
        j,rem=divmod(U+J,c);assert rem==0
        o,rem=divmod(U+c,f);assert rem==0
        assert min(i,y,j,o)>0 and U>c>J
        assert R*R==D*(f*f-1)
        assert R*R*(U*U-y*y)==1-y*y
        assert U==j*c-J==o*f-c
        records.append(dict(A=A,J=J,auxiliary_bits=U.bit_length()))
    return records


def verify():
    paths=['Papers/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md',
           'Papers/verification/explore_fixed_raw_universal_81.py',
           'Papers/verification/explore_fixed_raw_universal_84.py',
           'Papers/verification/explore_three_cell_marked.py',
           'Papers/1980/BASE_TWO_PELL_89_PROOF.md',
           'Papers/1980/EXPLORATION_ODD_INDEX_PELL_SIGNS.md']
    return dict(status='PASS_REJECTED_FIXED_RAW_SCALE_Q2_80',source=verify_source(),
                scalar=verify_scalar(),words=verify_words_and_bridge(),
                canonical_main=verify_canonical_main(),odd_auxiliary=verify_odd_auxiliary(),
                dependencies_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths},
                proof='../1980/EXPLORATION_FIXED_RAW_SCALE_Q2.md',
                full_positive_counterexample_proved=True,
                full_machine_alphabet_materialized=False,full_packed_kernel_tuple_materialized=False,
                smaller_universal_certificate=False,proof_assistant_verified=False)


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert json.loads(json.dumps(result))==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'], result['source']['operations'], 'operations;',
          result['words']['cases'],'actual outer tuples;',
          sum(r['triples'] for r in result['scalar']),'scalar triples')
