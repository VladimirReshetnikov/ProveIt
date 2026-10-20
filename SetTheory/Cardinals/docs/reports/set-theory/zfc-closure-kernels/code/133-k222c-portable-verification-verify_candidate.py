#!/usr/bin/env python3
"""Audit a new K-family table independently of its construction program.

Inputs are data. The retained symbolic engine proves unary scans and four
arbitrary-list schemas from the exact supplied table, then every source case.
This is an executable mathematical check, not a proof-assistant endpoint.
"""
from pathlib import Path
import argparse
import hashlib
import importlib
import json
import sys
import time

ENGINE_SHA = 'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145'
HELPER_SHA = '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, obj):
    Path(path).write_text(json.dumps(obj, indent=2) + '\n')


def parse(path):
    rows, starts = {}, []
    for line in Path(path).read_text().splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:])); continue
        if not line or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        q, b, w, z = map(int, (q, b, w, z))
        need(b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'Invalid binary row')
        need((q, b) not in rows, 'Duplicate row')
        rows[q, b] = w, (1 if d == 'R' else -1), z
    states = {q for q, b in rows}
    need(starts == [0], 'Expected K-labelled start state 0')
    need(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'Partial table')
    need({z for w, d, z in rows.values()} - states == {254}, 'Incorrect terminal')
    order, seen = [0], {0}
    for q in order:
        for b in (0, 1):
            z = rows[q, b][2]
            if z != 254 and z not in seen:
                seen.add(z); order.append(z)
    need(seen == states, 'Unreachable declared states')
    mapping = {q: i for i, q in enumerate(order)}
    mapping[254] = len(order)
    canon = {(mapping[q], b): (w, d, mapping[z]) for (q, b), (w, d, z) in rows.items()}
    return rows, states, canon, mapping


def encode(rows):
    return ('#! start 0\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {z}\n'
        for (q, b), (w, d, z) in sorted(rows.items()))).encode()


def inspect_source(path):
    sites = json.loads(Path(path).read_text())
    leaves, prefixes = {}, set()
    for pc, op, arg in sites:
        need(isinstance(pc, str) and pc and set(pc) <= {'0', '1'}, 'Invalid address')
        need(pc not in leaves, 'Duplicate address')
        need(op in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Unknown primitive')
        if op in ('CI', 'CD'):
            need(type(arg) is int and 0 <= arg < 9, 'Invalid register')
        elif op in ('CB', 'CC'):
            need(type(arg) is int and arg >= 1, 'Invalid jump depth')
        else:
            need(arg is None, 'Halt argument')
        leaves[pc] = op, arg
        prefixes.update(pc[:i] for i in range(len(pc)))
    need(not set(leaves) & prefixes and len(prefixes) == len(leaves) - 1, 'Not a prefix tree')
    need(all(p + b in leaves or p + b in prefixes for p in prefixes for b in '01'), 'Incomplete tree')
    need([pc for pc, op, arg in sites] == sorted(leaves), 'Noncanonical source order')
    subtrees = set()
    def visit(pc):
        node = leaves[pc] if pc in leaves else (visit(pc+'0'), visit(pc+'1'))
        subtrees.add(node)
        return node
    visit('')
    return sites, dict(instructions=len(sites), distinct_subtrees=len(subtrees),
                      maximum_depth=max(map(len, leaves)),
                      maximum_zero_run=max(len(s) for pc in leaves for s in pc.split('1')),
                      guarded_cases=sum(2 if op == 'CD' else 1 for pc, op, arg in sites))


def startup(rows, physical_map):
    q, h, ones, used = 0, 0, set(), set()
    for step in range(409835):
        need(q != 254, 'Premature halt during blank startup')
        b = int(h in ones)
        used.add((q, b))
        w, d, q = rows[q, b]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += d
    logical = [3, 0, 0, 0, 3, 0, 0, 0, 0]
    physical = [None] * 9
    for i, j in enumerate(physical_map):
        physical[j] = logical[i]
    want = {-6, 176}
    position = 177
    for value in physical + [1] * 167:
        position += 1
        want.update(range(position, position + value + 1))
        position += value + 1
    need((q, h, ones) == (84, -5, want), 'Wrong complete blank-startup tape or control')
    return dict(status='EXACT_COMPLETE_BLANK_STARTUP_PASS', steps=409835,
                k_state=q, head=h, one_cells=sorted(ones), all_unlisted_cells=0,
                logical_registers=logical, physical_registers=physical,
                extra_gap=117, spare_values=[1]*167, used_rows=sorted(used))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table', type=Path, required=True)
    ap.add_argument('--sites', type=Path, required=True)
    ap.add_argument('--legacy-map', type=Path, required=True)
    ap.add_argument('--engine-dir', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--structure-only', action='store_true')
    args = ap.parse_args()
    need(__debug__ and not sys.flags.optimize, 'Assertions must be enabled')
    args.output.mkdir(parents=True, exist_ok=True)
    receipt = dict(status='IN_PROGRESS', checker_sha256=sha(__file__),
                   table_sha256=sha(args.table), source_sha256=sha(args.sites))
    started = time.monotonic()
    cases = []
    try:
        need(sha(args.engine_dir/'symbolic_runtime.py') == ENGINE_SHA, 'Wrong engine')
        need(sha(args.engine_dir/'independent_runtime.py') == HELPER_SHA, 'Wrong helper')
        sys.path.insert(0, str(args.engine_dir.resolve()))
        E = importlib.import_module('symbolic_runtime')
        need(sha(E.__file__) == ENGINE_SHA and sha(E.r.__file__) == HELPER_SHA, 'Wrong imported engine')
        rows, states, canonical, canonical_map = parse(args.table)
        sites, metrics = inspect_source(args.sites)
        need(metrics['maximum_depth'] < 64 and metrics['maximum_zero_run'] <= 6, 'Address bound')
        raw_map = json.loads(args.legacy_map.read_text())
        raw_map = raw_map.get('k230_to_old', raw_map.get('k_to_legacy', raw_map))
        legacy = {int(q): int(z) for q, z in raw_map.items()}
        legacy[254] = 254
        for q in states:
            if q not in legacy:
                legacy[q] = q + 1000
        legacy = {q: legacy[q] for q in states | {254}}
        need(len(set(legacy.values())) == len(legacy), 'Noninjective legacy map')
        need((legacy[0], legacy[84], legacy[254]) == (95, 96, 254), 'Engine label mismatch')
        table = {(legacy[q], b): (w, d, legacy[z]) for (q, b), (w, d, z) in rows.items()}
        canonical_path = args.output/f'candidate{len(states)}.tm'
        canonical_path.write_bytes(encode(canonical))
        save(args.output/'canonical_map.json', dict(k_to_canonical=canonical_map))
        receipt.update(working_states=len(states), rows=len(rows), source_metrics=metrics,
                       canonical_sha256=sha(canonical_path), k_to_legacy=legacy,
                       symbolic_engine_sha256=ENGINE_SHA, helper_sha256=HELPER_SHA,
                       startup=startup(rows, E.r.PHY))
        print(f'{len(states)} states, {len(rows)} rows; source census and exact startup PASS', flush=True)
        if args.structure_only:
            receipt['status'] = 'STRUCTURE_AND_STARTUP_PASS'
        else:
            lemmas, blocks = E.prove_blocks(table)
            used = set()
            for i, site in enumerate(sites):
                for positive in ((False, True) if site[1] == 'CD' else (False,)):
                    answer = E.case(table, lemmas, site, positive)
                    used.update(answer.pop('rows')); answer.pop('trace')
                    need(len(answer['duration']) == 13 and answer['duration'][0] > 0
                         and all(type(n) is int and n >= 0 for n in answer['duration']), 'Nonpositive duration')
                    cases.append(dict(site_index=i, positive=positive, **answer))
                    if len(cases) % 1000 == 0:
                        print(f'Proved {len(cases)}/{metrics["guarded_cases"]} guarded cases', flush=True)
            need(len(cases) == metrics['guarded_cases'] and used == set(table), 'Incomplete coverage')
            case_path = args.output/'runtime_cases.json'
            save(case_path, cases)
            receipt.update(status='UNIVERSAL_MATHEMATICAL_PASS', cases=len(cases),
                           symbolic_steps=sum(c['symbolic_steps'] for c in cases),
                           minimum_actual_steps=min(c['duration'][0] for c in cases),
                           maximum_symbolic_steps=max(c['symbolic_steps'] for c in cases),
                           list_induction_blocks=blocks, all_rows_used=True,
                           used_legacy_rows=sorted(used), cases_file=case_path.name,
                           cases_sha256=sha(case_path),
                           scope='Nine independent natural registers; both decrement guards; arbitrary natural gap, first spare, and arbitrary finite remaining spare list; exact tape with blank exterior.',
                           proof_status='Executable ordinary mathematical induction; no new kernel-checked endpoint.',
                           fuel_scope='4000 bounds symbolic proof construction only, not registers, tape size, or execution time.')
        need(sha(args.table) == receipt['table_sha256'] and sha(args.sites) == receipt['source_sha256'], 'Input changed during verification')
    except Exception as error:
        receipt.update(status='FAILED', error=repr(error), case_count=len(cases),
                       site_index=locals().get('i'), site=locals().get('site'), positive=locals().get('positive'))
        raise
    finally:
        receipt['seconds'] = time.monotonic() - started
        save(args.output/'verification.json', receipt)
    print(receipt['status'], flush=True)


if __name__ == '__main__':
    main()
