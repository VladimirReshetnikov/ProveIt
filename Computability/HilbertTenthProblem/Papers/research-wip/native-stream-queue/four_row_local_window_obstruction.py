#!/usr/bin/env python3
"""FIFO66/FIFO58 traces that defeat every fixed row-only local window.

For each finite fixture width, each window of a rejecting-input cleanup
trace occurs at the identical position of a truly accepting encoded trace.
The adjacent note proves the construction uniformly for every window width.
"""
import argparse
import json
from pathlib import Path

from four_row_queue_block_simulator import Compiler, physical_reachable

ROWS = ((0, 0), (0, 1), (1, 2), (2, 0))
BINARY_ROWS = ((0, 0), (0, 1), (1, 0))


def parity_machine(force_even_accept=False, binary=False):
    table = {}
    for state in (0, 1):
        table[state, 0] = ((state, 0),)
        table[state, 1] = ((1-state, 1),)
        end_state = 2 if state == 1 or force_even_accept else 3
        table[state, 2] = ((end_state, 2),)
    for symbol in range(3):
        table[3, symbol] = ((3, symbol),)
    return Compiler(3, 4, {2}, table, binary=binary)


def trace(machine, word):
    queue, state = machine.encoded(word), machine.initial()
    m = len(queue)
    result = []
    # One cycle followed by cleanup; binary omits the PREPARE sweep.
    duration = (2 if machine.binary else 3)*m+machine.k+2
    for _ in range(duration):
        options = machine.step(state, queue[0])
        assert len(options) == 1
        append, state = options[0]
        result.append((queue[0], append))
        queue = queue[1:]+(append,)
    assert state[0] == 'done' and not any(queue)
    return tuple(result)


def fifo_parameters(machine, word, edges):
    digits = machine.encoded(word)
    m, t = len(digits), len(edges)
    if machine.binary:
        W, q = 2**m, 2**t
        initial = sum(a*2**j for j, a in enumerate(digits))
        selectors = [sum(2**j for j, edge in enumerate(edges) if edge == row)
                     for row in BINARY_ROWS]
        F0,F1,F2 = selectors
        D,A = F2,F1
        x, width_beta, quotient = initial//2, W-initial, q//W
        assert initial % 2 == 0 and F0 % 2 == 1
        assert all(v > 0 for v in [x,width_beta,quotient,*selectors])
        assert q == sum(selectors)+1 and q == W*quotient
        assert D == 2*x+W*A and D+A < q
        assert edges[0] == (0,0) and m % 2 == t % 2 == 0
        assert F1 % 2 == 0  # Numerical parity is not its population parity.
        return dict(m=m,t=t,x=x,W=W,q=q,F1=F1)
    W, q = 3**m, 3**t
    initial = sum(a*3**j for j, a in enumerate(digits))
    selectors = [sum(3**j for j, edge in enumerate(edges) if edge == row)
                 for row in ROWS]
    F0,F1,F2,F3 = selectors
    G, H = F1+F2, sum(selectors)
    D, A = F2+2*F3, F1+2*F2
    x = initial//2
    width_beta, quotient = W-initial, q//W
    assert initial % 2 == 0
    assert all(v > 0 for v in [x,width_beta,quotient,*selectors,G])
    assert q == 2*H+1 and q == W*quotient
    assert D == 2*x+W*A and D+A < q
    assert H % 2 == G % 2 == 0
    packed = F0+q*F1+q*q*F2+q**3*F3+q**4*G
    assert packed % 2 == 0 and 0 < packed < q**5
    assert edges[0] == (0,0) and m % 2 == t % 2 == 0
    return dict(m=m,t=t,x=x,W=W,q=q,F1=F1)


def check_substrate(binary=False):
    real = parity_machine(binary=binary)
    false_acceptor = parity_machine(True, binary=binary)
    assert real.k == false_acceptor.k == 4
    linear_windows = cyclic_windows = boundary_pairs = coded_good = 0
    bad_inputs = 0
    examples = []
    for width in range(1,33):
        N = 2*width+1
        word = (0,)*N+(2,)
        bad = trace(false_acceptor, word)
        params = fifo_parameters(real, word, bad)
        assert not physical_reachable(real, word)[0]
        assert params['F1'] % 2 == 0
        good_traces, supports = [], []
        owner = {}
        for cell in range(N):
            changed = tuple(1 if j == cell else 0 for j in range(N))+(2,)
            good = trace(real, changed)
            good_params = fifo_parameters(real, changed, good)
            assert good_params['q'] == params['q'] and good_params['W'] == params['W']
            if binary:
                assert good_params['F1'] % 2 == 0
                assert good_params['x'] == params['x']+2**(2*real.k*cell)
            else:
                assert good_params['F1'] % 2 == 1 and good_params['F1'] > 1
                v = (good_params['F1']-1)//2
                assert v > 0 and v+v+1 == good_params['F1']
                assert good_params['x'] == params['x']+3**(2*real.k*cell+1)
            differences = {j for j,(a,b) in enumerate(zip(bad,good)) if a != b}
            k,m = real.k,params['m']
            expected = {2*k*cell+1,2*k*cell+k+1,m+k+2*k*cell+1}
            if not binary:
                expected.add(2*m+k+2*k*cell+1)
            assert differences == expected
            assert all(j not in owner for j in differences)
            owner.update({j:cell for j in differences})
            supports.append(differences)
            good_traces.append(good)
            coded_good += 1
        t = len(bad)
        for start in range(t):
            positions = [(start+j) % t for j in range(width)]
            excluded = {owner[j] for j in positions if j in owner}
            assert len(excluded) <= width
            cell = next(i for i in range(N) if i not in excluded)
            assert [bad[j] for j in positions] == [good_traces[cell][j] for j in positions]
            cyclic_windows += 1
            if start+width <= t:
                linear_windows += 1
        boundary = set(range(width)) | set(range(t-width,t))
        excluded = {owner[j] for j in boundary if j in owner}
        assert len(excluded) <= 2*width
        cell = next(i for i in range(N) if i not in excluded)
        assert bad[:width] == good_traces[cell][:width]
        assert bad[-width:] == good_traces[cell][-width:]
        boundary_pairs += 1
        bad_inputs += 1
        if width in (1,4,32):
            examples.append(dict(window_width=width,editable_data_cells=N,
                                 physical_width=params['m'],duration=t,
                                 accepting_comparison_traces=N,
                                 exact_positive_component_extension=True))
    return dict(
        arithmetic_component=('native_binary_three_row_fifo58.md' if binary else
                              'native_four_row_fifo66.md'),
        rejecting_coded_inputs=bad_inputs,
        accepting_same_geometry_traces=coded_good,
        linear_windows=linear_windows,cyclic_windows=cyclic_windows,
        simultaneous_boundary_pairs=boundary_pairs,
        exact_support_size_per_changed_cell=3 if binary else 4,
        examples=examples,
    )


def check():
    return dict(
        status='PASS_FOUR_ROW_AND_BINARY_LOCAL_WINDOW_OBSTRUCTION',
        proof='four_row_local_window_obstruction.md',
        simulator='four_row_queue_block_simulator.md',
        ternary=check_substrate(),
        binary=check_substrate(binary=True),
        separate_nonlocal_parity_guard=dict(operations=2,additions=2,
                                           new_positive_witnesses=1,
                                           equation='F1=v+v+1',
                                           scope='Separates this particular ternary parity fixture only'),
        scope='Row-only bounded windows, even position-dependent and with the same '
              'q,W. Does not cover auxiliary state tracks, global matrix products, '
              'nonlocal constraints or dependence on the varying input parameter.',
        established_complete_bound=75,
    )


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = check()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result,indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == result
    print(json.dumps(result,indent=2))
