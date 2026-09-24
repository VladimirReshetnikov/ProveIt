#!/usr/bin/env python3
"""Complete81 candidate: stay-step markers at distance x and W=B^x."""
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib
import json
import sys
import sympy as sp

import explore_fixed_base_exponent_bridge as bridge
import explore_helical_unary_tableau as helical

OUT = Path(__file__).with_suffix('.json')
ROOT = Path(__file__).resolve().parents[2]
unary = helical.unary
tile = helical.tile
NAMES = list(bridge.NAMES)
CONSTANTS = list(bridge.CONSTANTS)
SYM = bridge.SYM
OUTER = list(bridge.OUTER)
CORE = list(bridge.CORE)
ADAPTER = [('scaled_t', '*', 'cell_bits', 'x')] + list(bridge.ADAPTER[2:])
SCHEDULE = OUTER + CORE + ADAPTER
EQUALITIES = list(bridge.EQUALITIES)
fixed_environment = bridge.fixed_environment


def source_residuals():
    return [sp.expand(source.subs(SYM['x'], SYM['x']-2))
            for source in bridge.source_residuals()]


def verify_source():
    env = fixed_environment(SYM)
    bridge.baseline.run_schedule(SCHEDULE, env)
    sources = source_residuals()
    U = SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction = sources[14]*(U*U-SYM['y_aux']**2)
    records = []
    for index, ((left, right), source) in enumerate(zip(EQUALITIES, sources)):
        actual = sp.expand(env[left]-env[right])
        adjust = correction if index == 15 else sp.Integer(0)
        sign = 1 if sp.expand(actual-source-adjust) == 0 else -1
        assert sp.expand(actual-sign*source-adjust) == 0, index
        records.append(dict(index=index, equality=[left, right], source_sign=sign,
                            source=sp.sstr(source), correction=sp.sstr(sp.expand(adjust))))
    primitives, counts = bridge.verify_primitives(SCHEDULE, env)
    assert len(primitives) == 81 and counts == {'+':37, '*':44}
    assert len(ADAPTER) == 14 and Counter(row[1] for row in ADAPTER) == {'+':7, '*':7}
    assert len(sources) == len(EQUALITIES) == 21 and len(NAMES) == len(set(NAMES)) == 33
    assert CORE == bridge.CORE and OUTER == bridge.OUTER
    assert {index for index, pair in enumerate(zip(sources, bridge.source_residuals()))
            if sp.expand(pair[0]-pair[1]) != 0} == {3,17}
    assert sp.expand(env['scaled_t']-SYM['cell_bits']*SYM['x']) == 0
    assert sp.expand(env['raw_bound']-SYM['C']-SYM['alpha']-SYM['cell_bits']*SYM['x']) == 0
    assert {SYM[name] for name in NAMES} <= set().union(*(s.free_symbols for s in sources))
    aliases = {name:value for name,value in fixed_environment(SYM).items() if name not in SYM}
    assert all(sp.sympify(value).free_symbols <= {SYM[name] for name in CONSTANTS}
               for value in aliases.values())
    return dict(operations=81, multiplications=44, additions_subtractions=37,
                positive_existential_unknown_count=33, positive_unknowns=NAMES, equations=21,
                raw_parameters=['x>0'], fixed_constants=CONSTANTS,
                fixed_aliases={name:sp.sstr(value) for name,value in aliases.items()},
                primitive_instructions=primitives, sources=records,
                ledger={'outer':24,'retained_kernel':43,'fixed_base_bridge':14},
                changed_source_residual_indices=[3,17],
                complete_fixed_index_raw_input_universal_certificate=True)


def residue_machine(modulus, residue):
    """Prepend one stationary origin-marking step to the old unary scan."""
    old = unary.residue_machine(modulus, residue)
    states = old.states + ('prep',)
    table = dict(old.transitions)
    for symbol in old.alphabet:
        table['prep', symbol] = ('loop', symbol, 0)
    table['q0', 1] = ('prep', 2, 0)
    table['prep', 2] = ('s0', 2, -1)
    return unary.old.Machine(states, old.alphabet, old.start, old.halt, old.blank, table)


def fixed_markers(machine):
    q1, written, move = machine.delta(machine.start, 1)
    assert written == 2 and move == 0 and q1 not in (machine.start, machine.halt)
    H = tile(0, 1)
    cell = lambda symbol, head=None, phase=None: tile(0, 0, (symbol, head), phase)
    S = (H, H, H, cell(1, phase='I'), cell(1, phase='I'), cell(1, machine.start, 'Q'),
         cell(1), cell(1), cell(2, q1))
    E = (H, H, H, cell(0, phase='L'), cell(1, phase='I'), cell(1, phase='I'),
         cell(0), cell(1), cell(1))
    return S, E


def cyclic_word(grid, h):
    word = helical.cyclic_word(grid, h)
    # The old origin is Q. Last I has old index1 and becomes the new origin.
    return word[1:] + word[:1]


def verify_tableaux():
    counts = dict(padded=0, noncanonical=0, nondivisible=0, triples=0, seam_windows=0,
                  unique_marker_pairs=0, smallest_input_presentations=0,
                  short_unmarked_presentations=0, nonhalting_truncations=0,
                  payload_mutations=0, duplicated_marker_words=0)
    records = []
    for modulus, residue in ((1,0), (2,0), (3,1), (5,2)):
        machine = residue_machine(modulus, residue)
        pred = helical.predicate(machine)
        S, E = fixed_markers(machine)
        assert S != E and pred(S) and pred(E)
        for run in range(1,11):
            x = run-1
            history = unary.history_for(machine, run, limit=24)
            halted = history[-1][2] == machine.halt
            assert halted == ((run+1)%modulus == residue)
            wmin, hmin = unary.thresholds(history, run)
            if not halted:
                grid = helical.strip_array(machine, run, history, wmin, hmin)
                assert not helical.valid_word(cyclic_word(grid,wmin), wmin, machine)
                counts['nonhalting_truncations'] += 1
                continue
            records.append(dict(modulus=modulus, residue=residue, raw_input=x,
                                unary_length=run+1, steps=len(history)-1))
            for dw, dh in product(range(3), repeat=2):
                width, height = wmin+dw, hmin+dh
                grid = helical.strip_array(machine, run, history, width, height)
                for factor in (1,2,3):
                    if helical.gcd(factor,height) != 1:
                        continue
                    h = factor*width
                    word = cyclic_word(grid,h)
                    lifted = helical.lift_word(word,h)
                    N = len(word)
                    assert helical.valid_word(word,h,machine)
                    assert all(unary.blocks.three_valid(lifted[i], lifted[(i-1)%N],
                                                       lifted[(i-h)%N], pred) for i in range(N))
                    counts['triples'] += N
                    counts['seam_windows'] += sum(bool(block[4][0]) for block in lifted)
                    counts['padded' if factor == 1 else 'noncanonical'] += 1
                    counts['nondivisible'] += bool(N%h)
                    if run == 1:
                        assert S not in lifted and E not in lifted
                        counts['short_unmarked_presentations'] += 1
                        continue
                    assert lifted[0] == S and lifted[x] == E and 0 < x < N
                    assert lifted.count(S) == lifted.count(E) == 1
                    counts['unique_marker_pairs'] += 1
                    counts['smallest_input_presentations'] += int(x == 1)
                    assert N >= 4  # Completeness padding, not a soundness assumption.
                    bad = list(word)
                    bad[-1] = tile(0,0,(0,machine.start),'Q')
                    assert not helical.valid_word(bad,h,machine)
                    counts['payload_mutations'] += 1
                    doubled = word*2
                    dlift = helical.lift_word(doubled,h)
                    assert helical.valid_word(doubled,h,machine)
                    assert dlift.count(S) == dlift.count(E) == 2
                    assert dlift[x+N] == E and any(dlift[j] == S for j in range(1,x+N+1))
                    counts['duplicated_marker_words'] += 1
    assert counts['smallest_input_presentations'] and counts['short_unmarked_presentations']
    assert counts['nondivisible']
    return dict(counts, halting_examples=records, raw_input_marker_distance='x',
                first_transition_move=0, start_window_center='last I', end_window_center='first I')


def verify_marker_link():
    own = other = short_strips = 0
    for lengths in product(range(1,6), repeat=3):
        for left_margin, right_margin in product((1,2), repeat=2):
            row, starts, ends = [], [], []
            for strip, run in enumerate(lengths):
                row += ['V']+['L']*left_margin
                end = len(row)
                row += ['I']*run
                start = len(row)-1
                row += ['Q']+['R']*right_margin
                if run >= 2:
                    starts.append((strip,start)); ends.append((strip,end))
                else:
                    short_strips += 1
            N = len(row)
            for strip,start in starts:
                for target,end in ends:
                    distance = (start-end)%N
                    path = [(start-j)%N for j in range(1,distance+1)]
                    encountered = [s for _,s in starts if s in path]
                    if target == strip:
                        assert distance == lengths[strip]-1 and not encountered
                        own += 1
                    else:
                        assert encountered and any(s in path[:-1] for _,s in starts)
                        other += 1
    return dict(correct_endpoints=own, wrong_strip_endpoints_crossing_start=other,
                unmarked_one_I_strips=short_strips)


def verify_compositions():
    cc = bridge.previous.compile_rule(3,None)
    B,R,bits = cc.B,cc.R,cc.d
    cases = nondivisible = aliases = wrong = 0
    max_kappa_bits = 0
    for x,h,mode in product(range(1,4),(1,2),(0,1,2)):
        N = x+h+2
        states = [1]+[2]*(N-1)
        states[x] = 0
        rows = [tuple(int(j==state) for j in range(3)) +
                tuple(0 if mode==0 else 1 if mode==1 else (i+j)%2
                      for j in range(cc.m+2-3)) for i,state in enumerate(states)]
        cells = [cc.cell(row) for row in rows]
        pack = lambda values: sum(value*B**i for i,value in enumerate(values))
        C = pack(cells)
        right = pack([cells[(i-1)%N] for i in range(N)])
        nxt = pack([cells[(i-h)%N] for i in range(N)])
        F = cc.Ds[0]*C+cc.Ds[1]*right+cc.Ds[2]*nxt
        assert F == pack([cc.Ds[0]*cells[i]+cc.Ds[1]*cells[(i-1)%N]+cc.Ds[2]*cells[(i-h)%N]
                          for i in range(N)])
        q,P,W,u = B**N,B**h,B**x,bits*x
        Z = C-R-W
        D,J = q-1,(q-1)//(B-1)
        assert 0 < Z < C < q and 0 < W < C < q and 0 < F < q-1 and 4 <= u < q
        assert Z&(cc.MC*J) == F&(cc.MF*J) == 0
        assert C <= (B-2)*J and q-C >= J+1 and J >= B**x > u
        alpha = q-C-u
        nondivisible += int(bool(Z%B))
        kR,rem = divmod(B*C-right,D); assert rem == 0
        kY,rem = divmod(P*C-nxt,D); assert rem == 0
        align = (P-1)//(B-1)
        assert kR >= 1 and kY >= align >= 1
        zquot = cc.Ds[1]*kR+cc.Ds[2]*kY
        r = (q*q-Z-q*F)*(q*q-1)+(cc.MC+q*cc.MF)*J
        assert r%2 and q*q <= r < q**4 and r.bit_count() == 3*bits*N
        values = dict(q=q,P=P,W=W,C=C,Z=Z,v=q//P,Jrep=J,align=align,F=F,
                      alpha=alpha,zquot=zquot,r=r)
        env = fixed_environment(dict(bridge.previous.constants(cc),cell_bits=bits,**values))
        bridge.baseline.run_schedule(OUTER,env)
        assert all(env[a] == env[b] for a,b in bridge.previous.OUTER_EQUALITIES if (a,b)!=('bounded','q'))
        A0 = 10*q+11
        a,H,Delta,J0 = A0-2,4*A0-5,A0*A0-1,u+5
        mu,kappa = bridge.variable.pell(A0,u)
        next_mu,c = mu,kappa
        for _ in range(5):
            next_mu,c = A0*next_mu+Delta*c,next_mu+A0*c
        delta,rem = divmod(kappa-u,a+1); assert rem == 0
        rho,rem = divmod(mu-a*kappa-W,H); assert rem == 0
        phi = c-kappa
        assert min(alpha,zquot,delta,rho,phi) > 0 and 0 < u < J0 < a+1
        env.update(x=x,a=a,A=Delta,a4m5=H,c=c,kappa=kappa,mu=mu,delta=delta,phi=phi,rho=rho)
        bridge.baseline.run_schedule(ADAPTER,env)
        assert env['raw_bound'] == q and env['index_rhs'] == kappa and env['pell_gap'] == c
        assert env['mu2'] == env['norm_rhs'] and env['exponent_rhs'] == mu
        assert (2**(u+bits)-W)%H != 0
        wrong += 1
        assert delta > bits and kappa == bits*(x+a+1)+(delta-bits)*(a+1)
        aliases += 1
        max_kappa_bits = max(max_kappa_bits,kappa.bit_length())
        cases += 1
    assert nondivisible > 0
    return dict(cases=cases, nondivisible_Z_cases=nondivisible, rejected_wrong_inputs=wrong,
                positive_aliases_without_raw_bound=aliases, cell_bits=bits,
                max_bridge_kappa_bits=max_kappa_bits, full_packed_kernel_tuples_materialized=False,
                scope='All outer/adapter equations with common coordinates; moderate independent Pell parameters')


def verify():
    paths = ['Papers/1980/FIXED_RAW_UNIVERSAL_82_PROOF.md',
             'Papers/1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md',
             'Papers/verification/explore_helical_unary_tableau.py',
             'Papers/1980/EXPLORATION_FIXED_BASE_EXPONENT_BRIDGE.md',
             'Papers/verification/explore_fixed_base_exponent_bridge.py']
    return dict(status='PASS_FIXED_RAW_UNIVERSAL81', source=verify_source(),
                tableaux=verify_tableaux(), marker_link=verify_marker_link(),
                base_two_congruences=bridge.verify_congruences(), compositions=verify_compositions(),
                inherited_component_sha256={path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in paths},
                proof='../1980/FIXED_RAW_UNIVERSAL_81_PROOF.md',
                complete_fixed_index_raw_input_universal_certificate=True,
                proof_assistant_verified=False, full_packed_kernel_tuples_materialized=False)


if __name__ == '__main__':
    result = verify()
    if sys.argv[1:] == ['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result == json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],'operations;',
          result['tableaux']['triples'],'helical triples;',result['compositions']['cases'],'arithmetic interfaces')
