#!/usr/bin/env python3
"""Check a K230-derived literal TM against a separately calibrated source.

Adapted from the root protocol audit for the 236-state investigation.

This is a protocol theorem, not by itself a calibration to Con(ZFC).
The unchanged, pinned symbolic engine supplies natural-number and finite-list
induction. Its proof-construction fuel does not bound simulated machine runs.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
import time


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + '\n')


def bootstrap(table, start, output, reference):
    """Exhaust the finite startup and compare its entire infinite tape."""
    expected = json.loads(reference.read_bytes())
    expected_tape = set(expected['all_one_positions'])
    state, head, tape, visits = start, 0, set(), Counter()
    for ticks in range(2_000_001):
        if ticks and state == 96 and head == expected['head'] and tape == expected_tape:
            break
        require(ticks < 2_000_000, 'Startup proof fuel exhausted')
        row = state, int(head in tape)
        visits[row] += 1
        w, d, state = table[row]
        if w:
            tape.add(head)
        else:
            tape.discard(head)
        head += d
    require(head == expected['head'], 'Wrong startup head')
    require(tape == expected_tape, 'Wrong complete startup tape')

    working = {q for q, b in table}
    order = [start] + sorted(working - {start})
    number = {q: n for n, q in enumerate(order)} | {254: len(working)}
    canonical = {(number[q], b): (w, d, number[z])
                 for (q, b), (w, d, z) in table.items()}
    offset = ticks + 1
    dense = bytearray(2 * ticks + 3)
    h, q = offset, 0
    for _ in range(ticks):
        w, d, q = canonical[q, dense[h]]
        dense[h] = w
        h += d
    require((q, h - offset) == (number[96], head), 'Dense startup control mismatch')
    require({i - offset for i, b in enumerate(dense) if b} == tape,
            'Dense startup whole-tape mismatch')
    header = min(p for p in tape if p >= head)
    values, p = [], header + 1
    while p <= max(tape):
        require(p not in tape and p + 1 in tape, 'Malformed unary file')
        begin = p + 1
        p = begin
        while p in tape:
            p += 1
        values.append(p - begin - 1)
    phy = (6, 2, 0, 4, 3, 7, 8, 5, 1)
    logical = [values[j] for j in phy]
    require(logical == [3, 0, 0, 0, 3, 0, 0, 0, 0], 'Wrong logical seed')
    require(len(values[9:]) == 167 and set(values[9:]) == {1}, 'Wrong spare file')
    receipt = {'status': 'EXACT_BLANK_STARTUP_PASS', 'steps': ticks,
               'head': head, 'marker': head - 1, 'header': header,
               'gap_parameter': header - head - 64, 'pc': '',
               'logical_registers': logical, 'physical_registers': values[:9],
               'spare_values': values[9:], 'all_one_positions': sorted(tape),
               'all_other_cells_zero': True, 'dense_canonical_replay': True,
               'visited_rows': [[q, b, n] for (q, b), n in sorted(visits.items())],
               'canonical_renumbering': number,
               'reference_sha256': sha(reference.read_bytes())}
    write(output / 'bootstrap.json', receipt)
    canonical_raw = ('#! start 0\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {z}\n'
        for (q, b), (w, d, z) in sorted(canonical.items()))).encode('ascii')
    (output / 'canonical.tm').write_bytes(canonical_raw)
    return receipt, set(visits), sha(canonical_raw)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, required=True,
                        help='Extracted, hash-pinned ZFC236 package')
    parser.add_argument('--table', type=Path, required=True)
    parser.add_argument('--sites', type=Path, required=True)
    parser.add_argument('--reference', type=Path, required=True,
                        help='Separately calibrated source for complete CFG comparison')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--full', action='store_true')
    parser.add_argument('--boot-reference', type=Path, required=True)
    args = parser.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Run with assertions enabled')
    sys.path.insert(0, str(args.base / 'upstream/zfc237/verification'))
    import symbolic_runtime as s
    import check_source_graph as g
    sys.path.insert(0, str(args.base / 'verification'))
    from verify_state_fold import parse_table

    raw, sr, rr = args.table.read_bytes(), args.sites.read_bytes(), args.reference.read_bytes()
    table, start = parse_table(raw)
    sites, reference = json.loads(sr), json.loads(rr)
    require(start == 95, 'Wrong native start convention')
    # The engine's command-line validate_inputs pins the historical rotation240
    # source. Here the explicit reference comparison below supplies the source
    # obligation; the generic symbolic induction functions remain unchanged.
    working = {q for q, b in table}
    require(95 in working and 96 in working and 254 not in working,
            'Wrong control conventions')
    require(set(table) == {(q, b) for q in working for b in (0, 1)},
            'Incomplete binary transition table')
    require({z for w, d, z in table.values()} - working == {254},
            'Invalid external target')
    require(all(w in (0, 1) and d in (-1, 1) for w, d, z in table.values()),
            'Invalid write symbol or head direction')
    require(isinstance(sites, list) and len(sites) in (5121, 5125), 'Wrong K source census')
    for pc, op, arg in sites:
        require(isinstance(pc, str) and 0 < len(pc) <= 64 and set(pc) <= {'0', '1'},
                'Malformed or oversized source path')
        require(op in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Invalid source opcode')
        require((op == 'CH' and arg is None)
                or (op in ('CI', 'CD') and type(arg) is int and 0 <= arg < 9)
                or (op in ('CB', 'CC') and type(arg) is int and arg >= 1),
                'Invalid source operand')
    ro, rg, ri, _ = g.graph(reference)
    co, cg, ci, depth = g.graph(sites)
    require([x[1:] for x in ro] == [x[1:] for x in co] and rg == cg and ri == ci,
            'Complete source control graph differs from calibrated reference')
    working = {q for q, b in table}
    pending, reachable = [start], set()
    while pending:
        q = pending.pop()
        if q in reachable:
            continue
        reachable.add(q)
        if q != 254:
            pending.extend(table[q, b][2] for b in (0, 1))
    require(reachable == working | {254}, 'Unreachable rows remain in counted table')
    args.output.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    boot, boot_rows, canonical_hash = bootstrap(
        table, start, args.output,
        args.boot_reference)
    metadata = {'working_states': len(working), 'transition_rows': len(table),
                'table_sha256': sha(raw), 'canonical_sha256': canonical_hash,
                'sites_sha256': sha(sr), 'reference_sha256': sha(rr),
                'checker_sha256': sha(Path(__file__).read_bytes()),
                'engine_sha256': sha(Path(s.__file__).read_bytes()),
                'helper_sha256': sha(Path(s.r.__file__).read_bytes()),
                'source_leaf_occurrences': len(sites), 'maximum_path_depth': depth,
                'all_states_graph_reachable': True, 'exact_bootstrap_steps': boot['steps']}
    print('Exact source CFG, blank startup, and dense canonical replay passed.', flush=True)
    if not args.full:
        write(args.output / 'verification.json', {'status': 'QUICK_SOURCE_AND_STARTUP_PASS', **metadata})
        return

    lemmas, blocks = s.prove_blocks(table)
    print('Four exact-table finite-list induction schemas passed.', flush=True)
    cases, rows = [], set()
    for index, site in enumerate(sites):
        for positive in ((False, True) if site[1] == 'CD' else (False,)):
            try:
                answer = s.case(table, lemmas, site, positive)
            except (AssertionError, KeyError, ValueError) as error:
                write(args.output / 'verification.json', {
                    'status': 'NOT_PROVED', **metadata, 'site_index': index, 'site': site,
                    'positive': positive, 'prior_cases': len(cases), 'reason': str(error)})
                raise
            rows.update(answer.pop('rows'))
            answer.pop('trace')
            cases.append({'site_index': index, 'positive': positive, **answer})
            if len(cases) % 1000 == 0:
                print('proved', len(cases), 'guards;', round(time.monotonic() - started, 2), 'seconds', flush=True)
    expected_cases = sum(2 if site[1] == 'CD' else 1 for site in sites)
    require(len(cases) == expected_cases, 'Incomplete guard census')
    require(min(row['duration'][0] for row in cases) > 0, 'Missing positive progress')
    receipt = {'status': 'UNIVERSAL_SOURCE_PROTOCOL_AND_BLANK_STARTUP_PASS', **metadata,
               'cases': len(cases), 'symbolic_steps': sum(x['symbolic_steps'] for x in cases),
               'minimum_actual_steps': min(x['duration'][0] for x in cases),
               'blocks': blocks, 'directly_used_rows': sorted(rows),
               'rows_outside_runtime_and_boot': sorted(set(table) - rows - boot_rows),
               'seconds': time.monotonic() - started,
               'scope': 'All guarded source leaves; all natural primary register values, arbitrary natural gap, arbitrary first spare and finite spare tail; exact complete tape and zero exterior, with positive duration. Source-calculus calibration is a separate proof. Ordinary mathematical checker, not a proof-assistant endpoint.'}
    write(args.output / 'verification.json', receipt)
    write(args.output / 'cases.json', cases)
    print(json.dumps({k: v for k, v in receipt.items() if k not in ('blocks', 'directly_used_rows')}, indent=2), flush=True)


if __name__ == '__main__':
    main()
