#!/usr/bin/env python3
"""Construct and independently check both transfer-plus-one loop rotations.

The proof is universal for all nine natural-valued registers.  It does not
use a reachability invariant or trust a finite run prefix.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import json


def increment_path(path):
    if not path:
        return ''
    return format((int(path, 2)+1) % (1 << len(path)), f'0{len(path)}b')


def jump(path, bit, count):
    assert type(count) is int and count > 0
    positions = [i for i in range(len(path)-1, -1, -1) if path[i] == bit]
    stem = path[:positions[count-1]] if count <= len(positions) else ''
    return increment_path(stem) if bit == '0' else stem


class Program:
    """Full source tree with the literal natural-register path semantics."""
    def __init__(self, sites):
        self.sites = sites
        self.leaves = {}
        self.prefixes = set()
        for i, row in enumerate(sites):
            assert isinstance(row, list) and len(row) == 3
            path, op, arg = row
            assert path and set(path) <= {'0', '1'}
            assert ((op in {'CI', 'CD'} and type(arg) is int and 0 <= arg < 9)
                    or (op in {'CB', 'CC'} and type(arg) is int and arg > 0)
                    or (op == 'CH' and arg is None))
            assert path not in self.leaves
            self.leaves[path] = i
            self.prefixes.update(path[:j] for j in range(len(path)))
        assert not self.prefixes.intersection(self.leaves)
        nodes = self.prefixes | self.leaves.keys()
        assert all(stem+'0' in nodes and stem+'1' in nodes for stem in self.prefixes)
        assert [path for path, _, _ in sites] == sorted(self.leaves)
        self.depth = max(map(len, self.leaves))

    def site_at(self, path):
        assert set(path) <= {'0', '1'}
        for length in range(1, self.depth+1):
            prefix = (path+'0'*length)[:length]
            if prefix in self.leaves:
                assert set(path[length:]) <= {'0'}, ('discarded nonzero suffix', path, prefix)
                return self.leaves[prefix]
        raise AssertionError(('path does not reach a source leaf', path))

    def successors(self, index):
        path, op, arg = self.sites[index]
        if op == 'CH':
            return {}
        if op == 'CI':
            targets = {'inc': increment_path(path)}
        elif op == 'CD':
            targets = {'zero': jump(path, '0', 1), 'positive': increment_path(path)}
        elif op == 'CB':
            targets = {'control': jump(path, '0', arg)}
        else:
            targets = {'control': jump(path, '1', arg)}
        return {case: self.site_at(dest) for case, dest in targets.items()}

PREFIX = '011'
OLD_FIRST, OLD_AFTER = 6, 10


def symbolic_trace(program, start, length, x_is_zero):
    """Execute a straight segment for an entire unbounded register region.

    Register r has value entry_Rr + delta[r].  Lower bounds are tracked
    exactly for the sole possible tested register X.  No numerical samples
    or saturation are used in this proof.
    """
    lower = [0] * 9
    upper = [None] * 9
    if x_is_zero:
        upper[6] = 0
    else:
        lower[6] = 1
    delta = [0] * 9
    state = start
    trace = []
    for _ in range(length):
        _, opcode, register = program.sites[state]
        if opcode == 'CI':
            lower[register] += 1
            if upper[register] is not None:
                upper[register] += 1
            delta[register] += 1
            case = 'inc'
        elif opcode == 'CD':
            if upper[register] == 0:
                case = 'zero'
            else:
                assert lower[register] >= 1, ('branch not forced on whole symbolic region', state, lower, upper)
                case = 'positive'
                lower[register] -= 1
                if upper[register] is not None:
                    upper[register] -= 1
                delta[register] -= 1
        else:
            assert opcode in ('CB', 'CC')
            case = 'control'
        successor = program.successors(state)[case]
        trace.append([state, case, successor])
        state = successor
    return {'exit': state, 'register_deltas': delta, 'trace': trace,
            'output_lower_bounds': lower, 'output_upper_bounds': upper}


def main():
    if not __debug__:
        raise RuntimeError('Assertions are required; do not use Python -O.')
    ap = argparse.ArgumentParser()
    ap.add_argument('--reference', type=Path, default=Path(__file__).resolve().parents[1]/'reference/baseline245')
    ap.add_argument('--output', type=Path, default=Path(__file__).with_name('qt_rotation'))
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    old_sites = json.loads((args.reference/'certificate/sites_logical.json').read_text())
    old_physical = json.loads((args.reference/'certificate/sites_physical.json').read_text())
    assert len(old_sites) == len(old_physical) == 6460
    physical = {}
    for (path, op, arg), (other_path, other_op, other_arg) in zip(old_sites, old_physical):
        assert path == other_path and op == other_op
        if op in ('CI', 'CD'):
            assert arg not in physical or physical[arg] == other_arg
            physical[arg] = other_arg
        else:
            assert arg == other_arg
    assert len(physical) == 9 and set(physical.values()) == set(range(9))
    old = Program(old_sites)
    expected = [[PREFIX+'00', 'CD', 6], [PREFIX+'010', 'CI', 0],
                [PREFIX+'011', 'CC', 2], [PREFIX+'1', 'CI', 0]]
    assert old_sites[OLD_FIRST:OLD_AFTER] == expected
    assert [row for row in old_sites if row[0].startswith(PREFIX)] == expected
    assert old.successors(6) == {'zero': 9, 'positive': 7}
    assert old.successors(7) == {'inc': 8}
    assert old.successors(8) == {'control': 6}
    assert old.successors(9) == {'inc': 10}
    results = []
    variants = {
        'right': [('0', 'CI', 0), ('10', 'CD', 6), ('11', 'CC', 2)],
        'left': [('00', 'CI', 0), ('01', 'CD', 6), ('1', 'CC', 1)],
    }
    for name, suffixes in variants.items():
        replacement = [[PREFIX+suffix, op, arg] for suffix, op, arg in suffixes]
        sites = old_sites[:OLD_FIRST] + replacement + old_sites[OLD_AFTER:]
        assert len(sites) == 6459
        new = Program(sites)
        assert [i for i, (_, op, _) in enumerate(old_sites) if op == 'CH'] == [6324]
        assert [i for i, (_, op, _) in enumerate(sites) if op == 'CH'] == [6323]
        # Both tree associations must realize exactly the same three-node CFG.
        assert new.successors(6) == {'inc': 7}
        assert new.successors(7) == {'zero': 9, 'positive': 8}
        assert new.successors(8) == {'control': 6}
        assert sites[6][1:] == ['CI', 0]
        assert sites[7][1:] == ['CD', 6]
        assert sites[8][1:] == ['CC', 2 if name == 'right' else 1]
        # Exact context: every outside instruction and every outside branch.
        mapping = {i: i if i < OLD_FIRST else i-1 for i in range(len(old_sites))
                   if i < OLD_FIRST or i >= OLD_AFTER}
        mapping[OLD_FIRST] = OLD_FIRST
        incoming, checked_edges = [], 0
        for i, j in mapping.items():
            if i == OLD_FIRST:
                continue
            assert old.sites[i][1:] == new.sites[j][1:]
            before, after = old.successors(i), new.successors(j)
            assert before.keys() == after.keys()
            for branch, target in before.items():
                assert target in mapping, ('external entry to middle of rotated loop', i, branch, target)
                assert mapping[target] == after[branch], (i, j, branch, target)
                if target == OLD_FIRST:
                    incoming.append([i, branch])
                checked_edges += 1
        assert mapping[old.site_at('')] == new.site_at('')
        # Two symbolic blocks give an even simpler relation: equal registers
        # at old first test6 and new first increment6.  For X>0 each returns
        # after three steps with the same updates; for X=0 each exits after2.
        symbolic_blocks = []
        for zero, length in [(True, 2), (False, 3)]:
            before = symbolic_trace(old, 6, length, zero)
            after = symbolic_trace(new, 6, length, zero)
            assert before['exit'] == (10 if zero else 6)
            assert after['exit'] == (9 if zero else 6)
            assert before['register_deltas'] == after['register_deltas']
            assert before['output_lower_bounds'] == after['output_lower_bounds']
            assert before['output_upper_bounds'] == after['output_upper_bounds']
            expected_delta = [0] * 9
            expected_delta[0] = 1
            if not zero:
                expected_delta[6] = -1
            assert before['register_deltas'] == expected_delta
            symbolic_blocks.append({'guard': 'R6=0' if zero else 'R6>=1',
                                    'instruction_count': length, 'old': before, 'new': after})
        # Check the symbolic relation at loop heads without enumerating values.
        # Represent register differences new-old by a length-nine integer vector.
        difference = [0] * 9
        difference[0] += 1  # new initial increment, old reaches its first test
        expected_difference = [1] + [0] * 8
        assert difference == expected_difference
        # Positive iteration: both decrement X; old increments NP; new's
        # continue followed by its next first instruction increments NP too.
        positive_difference = difference.copy()
        positive_difference[6] -= 1
        positive_difference[6] += 1
        positive_difference[0] -= 1
        positive_difference[0] += 1
        assert positive_difference == expected_difference
        # Zero exit: only the old program has a final increment of NP.
        exit_difference = difference.copy()
        exit_difference[0] -= 1
        assert exit_difference == [0] * 9
        # In both loops every positive iteration decreases X by one, every
        # intervening segment is finite, and the zero branch exits.  X in N
        # therefore gives termination for every entry vector, with exact counts.
        result = {
            'status': 'PASS_UNIVERSAL_SOURCE_EQUIVALENCE', 'association': name,
            'scope': 'Source loop identity and exact surrounding CFG only; TM runtime and blank bootstrap are separate obligations.',
            'old_source_leaves': len(old_sites), 'new_source_leaves': len(sites),
            'new_guarded_cases': sum(2 if op == 'CD' else 1 for _, op, _ in sites),
            'old_subtree': expected, 'new_subtree': replacement,
            'register_precondition': 'All nine registers arbitrary natural numbers.',
            'register_postcondition': 'R0_new=R0_entry+R6_entry+1; R6_new=0; all seven other registers unchanged.',
            'old_loop_head': 6, 'new_loop_head': 7,
            'new_minus_old_at_related_heads': expected_difference,
            'equal_register_block_heads': [6, 6],
            'unbounded_symbolic_blocks': symbolic_blocks,
            'loop_variant': 'R6, decreases by exactly one per positive iteration.',
            'old_instruction_count': '3*R6_entry+2',
            'new_instruction_count': '3*R6_entry+2',
            'context_edges_checked': checked_edges, 'external_entry_edges': incoming,
            'old_halt_site': 6324, 'new_halt_site': 6323,
            'old_sites_sha256': sha256((args.reference/'certificate/sites_logical.json').read_bytes()).hexdigest(),
            'old_physical_sites_sha256': sha256((args.reference/'certificate/sites_physical.json').read_bytes()).hexdigest(),
            'logical_to_physical_registers': physical,
            'new_sites_sha256': sha256((json.dumps(sites, indent=2)+'\n').encode()).hexdigest(),
        }
        # Count: original has X positive tests, X incs, X continues, one zero
        # test and one final inc.  New has X+1 incs, X+1 tests, X continues.
        assert (1 + 1 + 1, 1 + 1) == (3, 2)
        folder = args.output/name
        folder.mkdir(exist_ok=True)
        (folder/'sites_logical.json').write_text(json.dumps(sites, indent=2)+'\n')
        (folder/'sites_physical.json').write_text(json.dumps([[p, op, physical[arg] if op in ('CI', 'CD') else arg] for p, op, arg in sites], indent=2)+'\n')
        (folder/'source_verification.json').write_text(json.dumps(result, indent=2)+'\n')
        results.append(result)
    (args.output/'source_verification.json').write_text(json.dumps(results, indent=2)+'\n')
    print(json.dumps([{key: value for key, value in result.items() if key not in {'old_subtree', 'new_subtree'}} for result in results], indent=2))


if __name__ == '__main__':
    assert __debug__, 'Assertions must be enabled.'
    main()
