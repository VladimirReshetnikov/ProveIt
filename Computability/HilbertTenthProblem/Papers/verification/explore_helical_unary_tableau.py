#!/usr/bin/env python3
"""Fixed unary input on helical cyclic words, with offsets 1 and h."""
from math import gcd
from pathlib import Path
import json
import sys

import explore_fixed_unary_tableau as unary

OUT = Path(__file__).with_suffix('.json')
tile = unary.old.tile


def local_valid(center, at, machine):
    v, h, payload, phase = center
    if v not in (0,1) or h not in (0,1):
        return False
    left,right,down,up = at(-1,0),at(1,0),at(0,-1),at(0,1)
    if v != up[0] or (v and right[0]) or (h and up[1]):
        return False
    if not v and not right[0] and h != right[1]:
        return False
    if v:
        return h == 0 and payload is None and phase is None
    if h:
        return payload is None and phase is None
    if payload is None or payload[0] not in machine.alphabet:
        return False
    if payload[1] is not None and payload[1] not in machine.states:
        return False
    if down[1]:
        if phase not in unary.PHASES or (left[0] and phase != 'L') or (right[0] and phase != 'R'):
            return False
        if not right[0] and (phase,right[3]) not in unary.PAIRS:
            return False
        if payload != unary.phase_payload(phase,machine):
            return False
    elif phase is not None:
        return False
    symbol,state = payload
    if up[1] and state is not None and state != machine.halt:
        return False
    if state is not None:
        move = machine.delta(state,symbol)[2]
        if (move == -1 and left[0]) or (move == 1 and right[0]):
            return False
    if not up[1]:
        blank = (machine.blank,None)
        if (not left[0] and left[2] is None) or (not right[0] and right[2] is None):
            return False
        expected = unary.old.next_payload(blank if left[0] else left[2],payload,
                                         blank if right[0] else right[2],machine)
        if expected is None or up[2] != expected:
            return False
    return True


def predicate(machine):
    return lambda window: local_valid(window[4],lambda dx,dy:window[(dy+1)*3+dx+1],machine)


def strip_array(machine,t,history,width,height):
    grid = unary.build_torus(machine,t,history,width,height)
    for row in grid:
        row[0] = tile(1,0)
    return grid


def cyclic_word(grid,h):
    height,width = len(grid),len(grid[0])
    assert h%width == 0 and gcd(h//width,height) == 1
    N = width*height
    result = [None]*N
    for y,row in enumerate(grid):
        for x,cell in enumerate(row):
            i = (-(x-(width-3))-h*(y-1))%N
            assert result[i] is None
            result[i] = cell
    assert None not in result
    return result


def lift_word(word,h):
    N = len(word)
    return [tuple(word[(i-dx-h*dy)%N] for dy in (-1,0,1) for dx in (-1,0,1))
            for i in range(N)]


def valid_word(word,h,machine):
    return all(predicate(machine)(block) for block in lift_word(word,h))


def verify():
    padded = noncanonical = triples = rejected = mutations = old_rejected = seam_windows = 0
    starts = ends = nondivisible = duplicated = 0
    records = []
    for modulus,residue in ((1,0),(2,0),(3,1),(5,2)):
        machine = unary.residue_machine(modulus,residue)
        pred = predicate(machine)
        S,E = unary.fixed_markers(machine)
        assert pred(S) and pred(E)
        for t in range(1,10):
            history = unary.history_for(machine,t,limit=20)
            wmin,hmin = unary.thresholds(history,t)
            halted = history[-1][2] == machine.halt
            if not halted:
                grid = strip_array(machine,t,history,wmin,hmin)
                assert not valid_word(cyclic_word(grid,wmin),wmin,machine)
                rejected += 1
                continue
            for dw in range(3):
                for dh in range(3):
                    width,height = wmin+dw,hmin+dh
                    grid = strip_array(machine,t,history,width,height)
                    for factor in (1,2,3):
                        if gcd(factor,height) != 1:
                            continue
                        h = factor*width
                        assert h <= width*height
                        word = cyclic_word(grid,h)
                        lifted = lift_word(word,h)
                        N = len(word)
                        assert valid_word(word,h,machine)
                        assert all(unary.blocks.three_valid(lifted[i],lifted[(i-1)%N],lifted[(i-h)%N],pred)
                                   for i in range(N))
                        assert lifted[0] == S and lifted.count(S) == 1
                        starts += 1
                        if t >= 3:
                            assert lifted[t] == E and lifted.count(E) == 1 and t < N
                            assert all(lifted[j] != S for j in range(1,t+1))
                            ends += 1
                        # The previous rule propagated H through V and rejects
                        # this altered relation at a strip corner.
                        assert not all(unary.predicate(machine)(block) for block in lifted)
                        old_rejected += 1
                        seam_windows += sum(bool(block[4][0]) for block in lifted)
                        # Initialization corruption at the uniquely known head.
                        bad = list(word)
                        bad[0] = tile(0,0,(0,machine.start),'Q')
                        assert not valid_word(bad,h,machine)
                        mutations += 1
                        # Repeating a word preserves local truth but duplicates
                        # both distinguished markers, so uniqueness is material.
                        doubled = word*2
                        dlift = lift_word(doubled,h)
                        assert valid_word(doubled,h,machine) and dlift.count(S) == 2
                        if t >= 3:
                            assert dlift[t+N] == E and any(dlift[j] == S for j in range(1,t+N+1))
                        duplicated += 1
                        triples += N
                        if factor == 1:
                            padded += 1
                        else:
                            noncanonical += 1
                            nondivisible += bool(N%h)
            records.append(dict(modulus=modulus,residue=residue,input_length=t+1,steps=len(history)-1,
                                minimum_width=wmin,minimum_height=hmin))
    assert nondivisible > 0
    return dict(status='PASS_HELICAL_UNARY_TABLEAU',halting_examples=records,
                independently_padded_presentations=padded,noncanonical_stride_presentations=noncanonical,
                noncanonical_N_not_divisible_by_h=nondivisible,local_triples_checked=triples,
                vertical_seam_windows_checked=seam_windows,unique_starts=starts,unique_endpoints_t_at_least_three=ends,
                old_global_boundary_rule_rejections=old_rejected,rejected_nonhalting_truncations=rejected,
                rejected_initial_payload_mutations=mutations,valid_repetitions_with_duplicate_markers=duplicated,
                proof='../1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md',arithmetic_operation_count=None,
                scope='Fixed unary semantic theorem with offsets1,h; exact helical seams and arbitrary-period soundness; no complete arithmetic claim')


if __name__ == '__main__':
    result = verify()
    if sys.argv[1:] == ['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result == json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['independently_padded_presentations'],'padded;',
          result['noncanonical_stride_presentations'],'noncanonical;',result['local_triples_checked'],'triples')
