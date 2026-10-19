#!/usr/bin/env python3
"""Pinned K227 -> closed rotation -> all-tape context fold -> K226.

Uses only the adjacent stdlib module reconstruct227.py. The final arbitrary-
register binary-runtime theorem is a separate certificate. The local fold
is proved here for arbitrary binary tapes from the common initial state.
"""
from pathlib import Path
import argparse
import json
import reconstruct227 as core

TABLE227 = '3fec7dfdc3b763c16b332abed69c474e4d9b12f2a5778a62799774f99ce3482b'
SOURCE227 = '339511182a98cec549d4c2b5ee98192fd92fd137e8e925ff11c620a9b1865e3f'
TABLE226 = '30082fe31158b8ae049a1bf15f56acffaae71f9031642e6fa7ab75555e466be4'
SOURCE226 = '200cfe32d7b16587bd56667650e5eb192c9e392a3f4764b3ec4ca4705a074f89'
PATH = '11101001001110011100'


def rotation(root, table):
    q = 96
    for bit in PATH:
        b = int(bit); w, d, q = table[q, b]
        core.require((w, d) == (b, 1), 'Rotation prefix is not pure decoding')
    core.require(q == 210, 'Unexpected outer decoder state')
    expected = {(210, 0): (0, 1, 177), (210, 1): (1, 1, 215),
                (177, 0): (0, 1, 165), (177, 1): (1, 1, 240)}
    core.require(all(table[row] == action for row, action in expected.items()), 'Rotation row changed')
    core.require(core.ports(table, 177) == [(210, 0, 0, 1)], 'Inner state has another incoming transition')
    before = core.subtree(root, PATH)
    (a, b), c = before
    core.require([len(core.sites(n)) for n in (a, b, c)] == [28, 81, 138], 'Wrong source chunks')
    core.require(all(core.boundary(n) == (0, 0, False) for n in (a, b, c)), 'A rotation chunk is not closed')
    after = a, (b, c)
    newroot = core.replace(root, PATH, after)
    oldsites, newsites = core.sites(root), core.sites(newroot)
    core.require([r[1:] for r in oldsites] == [r[1:] for r in newsites], 'Instruction order changed')
    oldgraph, _ = core.graph_arithmetic(oldsites)
    newgraph, checks = core.graph_arithmetic(newsites)
    core.require(oldgraph == newgraph == core.graph_intervals(oldsites) == core.graph_intervals(newsites), 'Source graph differs')
    new = dict(table)
    new[210, 0] = 0, 1, 165
    new[210, 1] = 1, 1, 177
    new[177, 0] = 0, 1, 240
    new[177, 1] = 1, 1, 215
    receipt = {'outer_state': 210, 'inner_state': 177, 'direction': 'right', 'path': PATH,
               'chunk_leaves': [28, 81, 138], 'all_chunks_closed': True,
               'ordered_instructions_equal': True, 'guarded_graphs_equal': True,
               'independent_graph_agrees': True, 'no_stray_checks': checks,
               'metrics': core.metrics(newroot)}
    return newroot, new, receipt


def fold(old):
    # (retained zero-tagged state, deleted one-tagged state, helper for read0,
    #  helper for read1). The tag is the cell immediately left of the head.
    retained, deleted, helper0, helper1 = 86, 508, 182, 177
    for q, tag in ((retained, 0), (deleted, 1)):
        incoming = core.ports(old, q)
        core.require(incoming and all(w == tag and d == 1 for p, b, w, d in incoming), 'Preceding-bit invariant failed')
        core.require(q != core.START, 'Folded state is initial')
        core.require(all(old[q, b][:2] == (b, 1) for b in (0, 1)), 'Folded state is not pure decoding')
    new = {(q, b): (w, d, retained if z == deleted else z)
           for (q, b), (w, d, z) in old.items() if q != deleted}
    new[retained, 0] = 0, -1, helper0
    new[retained, 1] = 1, -1, helper1
    core.require(len(old) == 454 and len(new) == 452, 'State census failed')
    def trace(table, q, tag, bit, count):
        tape = {-1: tag, 0: bit}; head = 0; events = []
        for i in range(count):
            core.require(head in tape, 'Block accesses an unspecified cell')
            read = tape[head]; w, d, z = table[q, read]
            events.append([q, head, read, w, d, z])
            tape[head] = w; head += d; q = z
        return (q, head, tape), events
    blocks = []
    for q, tag in ((retained, 0), (deleted, 1)):
        for bit in (0, 1):
            endpoint = old[q, bit][2]
            old_end, old_trace = trace(old, q, tag, bit, 1)
            new_end, new_trace = trace(new, retained, tag, bit, 3)
            core.require(old_end == new_end == (endpoint, 1, {-1: tag, 0: bit}), 'All-tape fold block failed')
            blocks.append({'old_state': q, 'left_tag': tag, 'read': bit,
                           'new_state': retained, 'old_steps': 1, 'new_steps': 3,
                           'endpoint': endpoint, 'old_trace': old_trace, 'new_trace': new_trace})
    for (q, bit), (w, d, z) in old.items():
        if q in (retained, deleted): continue
        core.require(new[q, bit] == (w, d, retained if z == deleted else z), 'An ordinary row does not commute')
    return new, {'status': 'PASS_ALL_TAPE_POSITIVE_BLOCK_SIMULATION',
                 'roles': {'retained_zero_tagged': retained, 'deleted_one_tagged': deleted,
                           'helper_read0': helper0, 'helper_read1': helper1},
                 'incoming_ports': {str(q): core.ports(old, q) for q in (retained, deleted)},
                 'blocks': blocks, 'arbitrary_outside_cells': True,
                 'scope': 'Whole-tape simulation from start95 on every binary tape, between rotated227 and226.'}


def construct(table_path, source_path, output):
    raw, source = table_path.read_bytes(), source_path.read_bytes()
    core.require(core.sha(raw) == TABLE227 and core.sha(source) == SOURCE227, 'Pinned K227 input mismatch')
    old = core.read_table(raw); root = core.tree(json.loads(source))
    newroot, rotated, rotation_receipt = rotation(root, old)
    final, fold_receipt = fold(rotated)
    final_bytes, source_bytes = core.encode(final), core.compact(core.sites(newroot))
    core.require(core.sha(final_bytes) == TABLE226 and core.sha(source_bytes) == SOURCE226, 'Pinned K226 output mismatch')
    oldboot, newboot = core.boot(old, 409835), core.boot(final, 409835)
    core.require(oldboot['one_cells'] == newboot['one_cells'], 'Complete blank startup differs')
    changed = {row for row in set(old) | set(final) if old.get(row) != final.get(row)}
    visited = {tuple(record['row']) for record in oldboot['visited_rows']}
    core.require(not changed.intersection(visited), 'Changed row visited in startup')
    receipt = {'status': 'PASS_EXACT_K226_EXTENSION', 'input_table_sha256': TABLE227,
               'input_source_sha256': SOURCE227, 'table_sha256': TABLE226, 'source_sha256': SOURCE226,
               'rotation': rotation_receipt, 'fold': fold_receipt,
               'working_states': 226, 'rows': 452, 'changed_or_deleted_rows': len(changed),
               'startup_steps': 409835, 'complete_startup_equal': True,
               'changed_startup_rows_visited': 0,
               'edits': [{'row': list(row), 'before': old.get(row), 'after': final.get(row)} for row in sorted(changed)],
               'proof_scope': 'Source equality, exact construction, startup and all-tape local fold. Final unbounded binary-runtime certificate is separate.'}
    output.mkdir(parents=True, exist_ok=True)
    (output / 'rotated227.tm').write_bytes(core.encode(rotated))
    (output / 'candidate226.tm').write_bytes(final_bytes)
    (output / 'sites226.json').write_bytes(source_bytes)
    core.dump(output / 'extension226_receipt.json', receipt)
    core.dump(output / 'startup226_receipt.json', newboot)
    return receipt


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table', type=Path, required=True)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    result = construct(args.table, args.source, args.output_dir)
    print(json.dumps({k: v for k, v in result.items() if k not in ('rotation', 'fold', 'edits')}, indent=2))
