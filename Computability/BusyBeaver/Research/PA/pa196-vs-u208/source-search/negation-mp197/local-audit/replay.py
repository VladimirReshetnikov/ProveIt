#!/usr/bin/env python3
"""Audit the exact eight negation rewrites and their scratch precondition."""
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent.parent
REPO = HERE.parents[7]
ARCHIVE = REPO / 'docs/incoming/pa_consistency_research_2026-11-13.zip'
ARCHIVE_SHA = '466c804d54495d3347252a98788af021aecc459b041fcc1733b3adf1ff1e943b'
STARTS = [584, 686, 1759, 1861, 3119, 3193, 3428, 3611]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def branches(row):
    return row[2:] if row[0] in ('inc', 'dec') else row[1:]


def normalize(rows, start):
    result = []
    for row in rows:
        prefix = row[:2] if row[0] in ('inc', 'dec') else row[:1]
        result.append(prefix + tuple(x - start for x in branches(row)))
    return result


def execute(graph, pc, end, registers, checkpoint=None):
    registers = list(registers)
    check_value = None
    for steps in range(200000):
        if pc == checkpoint and check_value is None:
            check_value = tuple(registers)
        if pc == end:
            return tuple(registers), steps, check_value
        row = graph[pc]
        if row[0] == 'inc':
            registers[row[1]] += 1
            pc = row[2]
        elif row[0] == 'dec':
            if registers[row[1]]:
                registers[row[1]] -= 1
                pc = row[3]
            else:
                pc = row[2]
        elif row[0] == 'jump':
            pc = row[1]
        else:
            raise ValueError(('unexpected instruction', pc, row))
    raise ValueError('finite test exceeded bound')


def main():
    need(hashlib.sha256(ARCHIVE.read_bytes()).hexdigest() == ARCHIVE_SHA,
         'incoming archive hash mismatch')
    rot = load('rotations', SOURCE / 'scan_rotations.py')
    independent = load('zero_transfer', SOURCE / 'verify_zero_transfer.py')
    combined = load('combined_negation_mp', HERE.parent / 'replay.py')
    for file, expected in independent.PINS.items():
        need(hashlib.sha256((independent.UPSTREAM / file).read_bytes()).hexdigest() == expected,
             'source seed mismatch: ' + file)
    with ZipFile(ARCHIVE) as z:
        tree = combined.decode_tree(rot, json.loads(z.read(
            'pa_consistency_research/experiments/negation197/source.tree.json')))
    old, new = rot.graph(rot.root), rot.graph(tree)
    need(old == independent.interval_graph(rot, rot.root)[0] and
         new == independent.interval_graph(rot, tree)[0], 'independent graph resolvers disagree')
    need((len(old), len(new)) == (3812, 3596), 'source size changed')
    intervals = [(s, s + 47) for s in STARTS]
    starts_new = [s - 27*i for i, s in enumerate(STARTS)]
    intervals_new = [(s, s+20) for s in starts_new]
    need(all(intervals[i][1] <= intervals[i+1][0] for i in range(7)), 'overlapping blocks')
    def relocate(pc):
        need(not any(lo < pc < hi for lo, hi in intervals), 'outside edge enters block interior')
        return pc - 27 * sum(hi <= pc for lo, hi in intervals)
    old_template = normalize(old[STARTS[0]:STARTS[0]+47], STARTS[0])
    new_template = normalize(new[starts_new[0]:starts_new[0]+20], starts_new[0])
    # Once the removed pair/unpair detour is over, the final 16 instructions
    # are literally the same CFG at old offset 31 and new offset 4.
    need(normalize(old[STARTS[0]+31:STARTS[0]+47], STARTS[0]+31) ==
         normalize(new[starts_new[0]+4:starts_new[0]+20], starts_new[0]+4),
         'shared suffix changed')
    for i, (start, start_new) in enumerate(zip(STARTS, starts_new)):
        need(normalize(old[start:start+47], start) == old_template, 'old block differs')
        need(normalize(new[start_new:start_new+20], start_new) == new_template, 'new block differs')
        for graph, lo, length in ((old, start, 47), (new, start_new, 20)):
            hi = lo + length
            for q, row in enumerate(graph):
                for dest in branches(row):
                    if lo <= q < hi:
                        need(lo <= dest <= hi, 'block exits away from its continuation')
                    else:
                        need(not lo < dest < hi, 'external entry to block interior')
    checked = 0
    for pc, row in enumerate(old):
        if any(lo <= pc < hi for lo, hi in intervals):
            continue
        prefix = row[:2] if row[0] in ('inc', 'dec') else row[:1]
        need(new[relocate(pc)] == prefix + tuple(relocate(x) for x in branches(row)),
             'outside control-flow relocation differs')
        checked += 1
    need(checked == 3436, 'outside site count differs')
    tests = 0
    for start, start_new in zip(STARTS, starts_new):
        for t, w, scratch in itertools.product(range(4), repeat=3):
            registers = [7, t, w, 9, 3, 2, scratch, 0, 6]
            expected = list(registers)
            expected[1], expected[6], expected[7] = 1, t + scratch, 0
            out_old, _, middle_old = execute(old, start, start+47, registers, start+31)
            out_new, _, middle_new = execute(new, start_new, start_new+20, registers, start_new+4)
            need(middle_old == tuple(expected) == middle_new, 'intermediate values differ')
            need(out_old == out_new, 'final register files differ')
            final = list(registers)
            u = t + scratch
            final[1] = 4 * (((u + 1) * (u + 2)) // 2 + 1)
            final[6] = final[7] = 0
            need(out_old == tuple(final), 'negation output changed')
            tests += 1
    registers = [0]*9
    registers[7] = 1
    out_old, old_steps, _ = execute(old, STARTS[0], STARTS[0]+47, registers)
    out_new, new_steps, _ = execute(new, starts_new[0], starts_new[0]+20, registers)
    need(out_old == (0,16,0,0,0,0,0,0,0) and out_new == (0,12,0,0,0,0,0,0,0),
         'nonzero scratch counterexample changed')
    result = {'archive_sha256': ARCHIVE_SHA,
              'program_sha256': hashlib.sha256(rot.p.read_bytes()).hexdigest(),
              'old_entries': STARTS, 'new_entries': starts_new,
              'old_block_sites': 47, 'new_block_sites': 20,
              'all_blocks_same_per_version': True,
              'block_external_entry_exit_checks': True,
              'outside_cfg_rows_relocated_and_compared': checked,
              'independent_graph_resolvers_agree': True,
              'zero_scratch_finite_controls': tests,
              'nonzero_scratch_counterexample': {'initial': registers,
                 'old_result': out_old, 'old_steps': old_steps,
                 'new_result': out_new, 'new_steps': new_steps},
              'scope': 'Finite structural and control checks; see README for the arbitrary-value proof.'}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
