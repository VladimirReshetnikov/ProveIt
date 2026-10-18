#!/usr/bin/env python3
"""Generate a shorter, exactly equivalent NIP source and check its context.

This is a source artifact only. It deliberately makes no TM state-count claim.
The context checker imports only our independent source path interpreter.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import json
from check_source_244 import Program, check_interval_certificate

Q = '1110100101'
OLD_ENTRY = 6312
OLD_CHECK_END = 6325


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--reference', type=Path, default=Path(__file__).resolve().parent/'reference')
    parser.add_argument('--invariant', type=Path, default=Path(__file__).resolve().parent/'dirty_invariant.json')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('nip_specialization'))
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    old_sites = json.loads((args.reference/'certificate/sites_logical.json').read_text())
    old = Program(old_sites)
    values, interval_replay = check_interval_certificate(old, json.loads(args.invariant.read_text()))
    assert values[OLD_ENTRY][6] == (0, 0)
    assert old_sites[OLD_ENTRY] == [Q+'0', 'CI', 6]
    assert all(path.startswith(Q+'10') for path, op, arg in old_sites[OLD_ENTRY+1:OLD_CHECK_END])
    assert old_sites[OLD_CHECK_END-1][1:] == ['CH', None]
    specialized_check = [[Q+'0'+suffix, op, register] for suffix, op, register in
                         [('0', 'CD', 5), ('100', 'CD', 5), ('10100', 'CD', 5),
                          ('10101', 'CC', 1), ('1011', 'CB', 1), ('11', 'CH', None)]]
    old_cleanup = [row for row in old_sites if row[0].startswith(Q+'11')]
    assert len(old_cleanup) == 14
    new_cleanup = [[Q+'1'+path[len(Q)+2:], op, arg] for path, op, arg in old_cleanup]
    old_end = OLD_CHECK_END + len(old_cleanup)
    assert old_sites[OLD_CHECK_END:old_end] == old_cleanup
    new_sites = old_sites[:OLD_ENTRY] + specialized_check + new_cleanup + old_sites[old_end:]
    assert len(new_sites) == 6453
    new = Program(new_sites)
    # All instructions outside the replaced check retain exactly their CFG effects.
    map_index = {i: i if i < OLD_ENTRY else i-7 for i in range(len(old_sites))
                 if i < OLD_ENTRY or i >= OLD_CHECK_END}
    map_index[OLD_ENTRY] = OLD_ENTRY  # The one permitted entry into the check.
    ordinary_edges = 0
    entry_edges = []
    for i, j in map_index.items():
        if i == OLD_ENTRY:
            continue
        assert old.sites[i][1:] == new.sites[j][1:]
        old_successors, new_successors = old.successors(i), new.successors(j)
        assert old_successors.keys() == new_successors.keys()
        for branch, target in old_successors.items():
            assert target in map_index, ('external edge enters interior', i, branch, target)
            assert map_index[target] == new_successors[branch], (i, branch, target)
            ordinary_edges += 1
            if target == OLD_ENTRY:
                entry_edges.append([i, branch])
    # Match the common suffix after the first decrement of H succeeds.
    # Old indices6320..6324 and newindices6313..6317 have identical effects.
    suffix_mapping = {6320+i: 6313+i for i in range(5)} | {6325: 6318}
    common_edges = 0
    for i in range(6320, 6325):
        j = suffix_mapping[i]
        assert old.sites[i][1:] == new.sites[j][1:]
        for branch, target in old.successors(i).items():
            assert target in suffix_mapping, (i, branch, target)
            assert suffix_mapping[target] == new.successors(j)[branch]
            common_edges += 1
    # The prefix before CDH changes only X: 0 ->1 ->0.
    assert old.sites[6312][1:] == ['CI', 6]
    assert old.successors(6312) == {'inc': 6313}
    assert old.sites[6313][1:] == ['CD', 6]
    assert old.successors(6313)['positive'] == 6314
    assert old.sites[6314][1:] == ['CD', 5]
    assert new.sites[6312][1:] == ['CD', 5]
    # Positive branch reaches the common suffix without register changes.
    assert old.successors(6314)['positive'] == 6315
    assert old.sites[6315][1:] == ['CC', 2]
    assert old.successors(6315) == {'control': 6313}
    assert old.successors(6313)['zero'] == 6320
    assert new.successors(6312)['positive'] == 6313
    # The zero branch is a finite path through known constants H=0, X=0.
    # All other registers are symbolic and untouched on this path.
    old_zero_trace = []
    state = 6314
    registers = [0] * 9
    for _ in range(20):
        if state == 6325:
            break
        path, op, arg = old.sites[state]
        old_zero_trace.append([state, op, arg, registers[5], registers[6]])
        successors = old.successors(state)
        if op == 'CD':
            assert arg in (5, 6)
            branch = 'positive' if registers[arg] else 'zero'
            if branch == 'positive':
                registers[arg] -= 1
        elif op == 'CI':
            assert arg in (5, 6)
            registers[arg] += 1
            branch = 'inc'
        else:
            assert op in ('CB', 'CC')
            branch = 'control'
        state = successors[branch]
    assert state == 6325 and registers == [0]*9
    assert new.successors(6312)['zero'] == 6318
    result = {'status': 'PASS_SOURCE_EQUIVALENCE_ONLY',
              'warning': 'No TM implementation or state count is certified by this source transformation. Direct literal state rewrites also disturb shared phase routers.',
              'old_leaf_count': 6460, 'new_leaf_count': 6453,
              'subtree_prefix': Q, 'old_check_leaves': 13, 'new_check_leaves': 6,
              'new_guarded_cases': sum(2 if op == 'CD' else 1 for _, op, _ in new_sites),
              'entry_precondition': 'R6=0; R5 arbitrary natural; all other registers arbitrary.',
              'check_specification': 'Halt iff entry R5=1. Otherwise return with R5=R6=0 and preserve all other registers.',
              'global_initial_condition': 'R1=R2=R5=0; other six registers arbitrary naturals.',
              'interval_closure_edges_replayed': interval_replay['closure_edges'],
              'old_sites_sha256': sha256((args.reference/'certificate/sites_logical.json').read_bytes()).hexdigest(),
              'old_invariant_sha256': sha256(args.invariant.read_bytes()).hexdigest(),
              'context_commuting_edges': ordinary_edges,
              'external_entry_edges': entry_edges,
              'common_suffix_edges': common_edges,
              'positive_branch_common_suffix_map': suffix_mapping,
              'zero_branch_trace': old_zero_trace,
              'specialized_check_leaves': specialized_check,
              'new_sites_sha256': sha256((json.dumps(new_sites, indent=2)+'\n').encode()).hexdigest()}
    (args.output/'sites_logical.json').write_text(json.dumps(new_sites, indent=2)+'\n')
    # The deployed tape uses a fixed permutation of logical register names.
    # Use the pinned physical site list to infer and verify, never guess it.
    old_physical = json.loads((args.reference/'certificate/sites_physical.json').read_text())
    inferred = {}
    for (_, op, logical), (_, physical_op, physical) in zip(old_sites, old_physical):
        assert op == physical_op
        if op in ('CI', 'CD'):
            assert logical not in inferred or inferred[logical] == physical
            inferred[logical] = physical
    assert len(inferred) == 9
    new_physical = [[path, op, inferred[arg] if op in ('CI', 'CD') else arg] for path, op, arg in new_sites]
    (args.output/'sites_physical.json').write_text(json.dumps(new_physical, indent=2)+'\n')
    (args.output/'source_verification.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: value for key, value in result.items() if key not in {'zero_branch_trace', 'specialized_check_leaves'}}, indent=2))


if __name__ == '__main__':
    assert __debug__, 'Assertions must be enabled.'
    main()
