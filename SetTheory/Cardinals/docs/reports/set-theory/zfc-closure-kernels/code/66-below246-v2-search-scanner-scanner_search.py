#!/usr/bin/env python3
"""Portable bounded state-reuse searches, plus an exact scanner obstruction.

This file runs with Python's standard library. Results are finite discovery
evidence. Fuel and dispatch-visit cutoffs do not prove inequivalence.

Tape conventions, physical permutation, expected path updates, and the finite
test recipe are adapted from the attributed context246 package's
code/check_literal_instructions.py. New enumeration and obstruction analysis
were prepared on 18 October 2026. See NOTICE.txt and README.md.
"""
from __future__ import annotations
from collections import Counter
from hashlib import sha256
from pathlib import Path
import argparse, gzip, json, random, re

ROOT = Path(__file__).resolve().parent
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)
TABLE_HASH = '303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee'
SITES_HASH = '1e989801225be6a66477fe6c4f7dcc7c08751fc1c03cc65c321a08e8528625b0'

def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        key = int(q), int(bit)
        assert key not in table
        table[key] = int(write), 1 if direction == 'R' else -1, int(target)
    states = {q for q, bit in table}
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    return table

def paint(pc, span, registers, spares, head=0):
    assert len(pc) <= span and all(v >= 0 for v in registers + spares)
    ones = {head - 1, head + span}
    ones.update(head + i for i, b in enumerate(pc) if b == '1')
    cursor = head + span + 1
    for v in registers + spares:
        ones.update(range(cursor + 1, cursor + v + 2))
        cursor += v + 2
    return ones

def successor(bits):
    word = list(bits)
    i = len(word) - 1
    while i >= 0 and word[i] == '1':
        word[i] = '0'
        i -= 1
    if i < 0:
        return None
    word[i] = '1'
    return ''.join(word)

def cut(bits, symbol, count):
    i = len(bits)
    while count and i:
        i -= 1
        if bits[i] == symbol:
            count -= 1
    return bits[:i]

def target_frame(pc, kind, r, registers, spares, span=40):
    registers = list(registers)
    spares = list(spares)
    extra = 0
    if kind == 'CH':
        return None
    if kind == 'CI':
        registers[PHYSICAL[r]] += 1
        spares.append(1)
        next_pc = successor(pc)
    elif kind == 'CD':
        if registers[PHYSICAL[r]]:
            registers[PHYSICAL[r]] -= 1
            extra = 1
            next_pc = successor(pc)
        else:
            next_pc = successor(cut(pc, '0', 1))
    elif kind == 'CB':
        next_pc = successor(cut(pc, '0', r))
    elif kind == 'CC':
        next_pc = cut(pc, '1', r)
    else:
        raise ValueError(kind)
    head = -int(next_pc is None)
    span += extra + int(next_pc is None)
    return head, paint(next_pc or '', span, registers, spares, head)

def cases_for(sites):
    cases = []
    for pc, kind, r in sites:
        for positive in ((False, True) if kind == 'CD' else (False,)):
            registers = [(3 * i + 1) % 7 for i in range(9)]
            if kind == 'CD':
                registers[PHYSICAL[r]] = int(positive)
            cases.append((pc, kind, r, positive,
                paint(pc, 40, registers, [0]),
                target_frame(pc, kind, r, registers, [0])))
    return cases

def first_failure(table, cases, fuel=2400, visit_limit=8):
    for index, (pc, kind, r, positive, initial, wanted) in enumerate(cases):
        state, head, ones, visits = 96, 0, initial.copy(), 0
        outcome = None
        for steps in range(1, fuel + 1):
            key = state, int(head in ones)
            if key not in table:
                outcome = 'missing-row'
                break
            write, direction, state = table[key]
            if write:
                ones.add(head)
            else:
                ones.discard(head)
            head += direction
            if state == 254:
                if kind != 'CH':
                    outcome = 'unexpected-halt'
                break
            if state == 96:
                if wanted is not None and head == wanted[0] and ones == wanted[1]:
                    break
                visits += 1
                if visits >= visit_limit:
                    outcome = 'dispatch-visit-cutoff'
                    break
        else:
            outcome = 'fuel-cutoff'
        if outcome is not None:
            return dict(case_index=index, pc=pc, operation=kind, register=r,
                positive=positive, outcome=outcome, steps=steps,
                final_state=state, final_head=head, dispatch_visits=visits)
    return None

def histogram(paths, strip=False):
    return dict(sorted(Counter(max(map(len, re.findall('0+',
        pc.rstrip('0') if strip else pc)), default=0)
        for pc, op, r in paths).items()))

def encode(table):
    return '#! start 95\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {t}\n'
        for (q, b), (w, d, t) in sorted(table.items()))

def analyze_obstruction(table, sites):
    pc = '111010010010000000'
    assert [pc, 'CD', 1] in sites
    registers = [0] * 9
    initial = paint(pc, 40, registers, [0])
    wanted = target_frame(pc, 'CD', 1, registers, [0])
    short = {key: row for key, row in table.items() if key[0] != 74}
    short[58, 0] = 0, -1, 84
    rows = {}
    for name, machine in [('baseline246', table), ('rejected245', short)]:
        state, head, ones = 96, 0, initial.copy()
        visits, trace = [], []
        for elapsed in range(1000):
            read = int(head in ones)
            write, direction, following = machine[state, read]
            if state in (58, 74) or (state == 84 and read == 1):
                trace.append(dict(before_step=elapsed, state=state, head=head,
                    read=read, write=write, direction=direction, next_state=following,
                    next_head=head + direction))
            if write:
                ones.add(head)
            else:
                ones.discard(head)
            head += direction
            state = following
            if state == 96:
                visits.append(dict(after_steps=elapsed + 1, head=head))
                if name == 'rejected245' and head != 0:
                    assert elapsed + 1 == 185 and head == 11
                    assert all(i not in ones for i in range(11, 19))
                    assert -1 in ones and 10 in ones
                    break
                if name == 'baseline246' and head == wanted[0] and ones == wanted[1]:
                    assert elapsed + 1 == 386
                    break
        else:
            raise AssertionError('The advertised finite trace did not reproduce.')
        rows[name] = dict(dispatch_visits=visits, critical_trace=trace,
            final_state=state, final_head=head, final_ones=sorted(ones),
            after_steps=elapsed + 1)
    return short, dict(pc=pc, operation='CD', logical_register=1,
        physical_register=PHYSICAL[1], initial_head=0, dispatcher=96,
        marker=-1, header=40, primary_registers=registers, spares=[0],
        initial_ones=sorted(initial), zero_run_after_selection=[11, 18],
        false_marker=10, expected_dispatch_head=0, traces=rows,
        interpretation='Exact failure of the marker-recovery invariant on a legal '
          'macro input. Reachability of this input from blank is not asserted. '
          'No conclusion about the modified machine\'s blank halting is drawn.')

def run_family(name, recipes, output, cases):
    ledger = output / (name + '.jsonl.gz')
    digest = sha256()
    failures, survivors, count = Counter(), [], 0
    # mtime=0 makes the compressed ledger reproducible.
    with ledger.open('wb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as stream:
            for recipe, table in recipes:
                failure = first_failure(table, cases)
                count += 1
                entry = dict(recipe=recipe, first_failure=failure)
                payload = (json.dumps(entry, sort_keys=True, separators=(',', ':'))
                    + '\n').encode('ascii')
                stream.write(payload)
                digest.update(payload)
                if failure is None:
                    survivors.append(recipe)
                else:
                    failures[failure['outcome']] += 1
    result = dict(family=name, recipes=count, finite_cases=len(cases),
        fuel_per_case=2400, dispatch_visit_cutoff=8, survivor_count=len(survivors),
        survivors=survivors, failure_outcomes=dict(failures),
        uncompressed_ledger_sha256=digest.hexdigest(),
        compressed_ledger_sha256=sha256(ledger.read_bytes()).hexdigest(),
        result_scope='bounded discovery screen; not a lower-bound proof')
    print(name, count, 'recipes;', len(survivors), 'survivors', flush=True)
    return result

def one_action_recipes(table):
    for doomed, predecessor in [(74, 58), (58, 41), (41, 29), (29, 19),
            (19, 13), (13, 9), (9, 6), (6, 4)]:
        base = {k: v for k, v in table.items() if k[0] != doomed}
        for target in sorted({q for q, bit in base}):
            for write in (0, 1):
                for direction in (-1, 1):
                    candidate = base.copy()
                    candidate[predecessor, 0] = write, direction, target
                    yield dict(removed=doomed,
                        changed_row=[predecessor, 0, write, direction, target]), candidate

def two_action_recipes(table):
    base = {k: v for k, v in table.items() if k[0] != 74}
    base[58, 0] = 0, -1, 84
    for source in (2, 4, 6, 9, 13, 19, 29, 41, 58, 84):
        for bit in (0, 1):
            for target in sorted({q for q, bit in base}):
                for write in (0, 1):
                    for direction in (-1, 1):
                        row = write, direction, target
                        if row == base[source, bit]:
                            continue
                        candidate = base.copy()
                        candidate[source, bit] = row
                        yield dict(removed=74, fixed_row=[58, 0, 0, -1, 84],
                            second_row=[source, bit, write, direction, target]), candidate

def free_row_recipes(table):
    base = table.copy()
    forced_callers = [(26, 1), (50, 1), (55, 1), (60, 0),
        (66, 1), (147, 1), (168, 1), (170, 1)]
    assert table[20, 1] == table[143, 1]
    for key in forced_callers:
        write, direction, target = base[key]
        assert target == 20
        base[key] = write, direction, 143
    base[20, 1] = 1, 1, 254
    for target in sorted({q for q, bit in table}):
        for write in (0, 1):
            for direction in (-1, 1):
                candidate = base.copy()
                candidate[141, 1] = write, direction, target
                yield dict(changed_callers=forced_callers,
                    disabled_row=[20, 1, 1, 1, 254],
                    repair_row=[141, 1, write, direction, target]), candidate

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'results')
    parser.add_argument('--obstruction-only', action='store_true')
    args = parser.parse_args()
    if not __debug__:
        parser.error('Assertions must be enabled; omit -O and -OO.')
    args.output.mkdir(parents=True, exist_ok=True)
    table_path = ROOT / 'inputs/zfc_context246_old.tm'
    assert sha256(table_path.read_bytes()).hexdigest() == TABLE_HASH
    table = read_table(table_path)
    sites_path = ROOT / 'inputs/instruction-sites.json'
    assert sha256(sites_path.read_bytes()).hexdigest() == SITES_HASH
    sites = json.loads(sites_path.read_text())
    assert len(sites) == 6460
    hard = [s for s in sites if '0000000' in s[0]]
    assert len(hard) == 18 and all(s[0].endswith('0000000') for s in hard)
    short, obstruction = analyze_obstruction(table, sites)
    (args.output / 'rejected_scanner245.tm').write_text(encode(short))
    (args.output / 'obstruction.json').write_text(json.dumps(obstruction, indent=2) + '\n')
    census = dict(leaves=len(sites), whole_path_zero_run_histogram=histogram(sites),
        nonterminal_zero_run_histogram=histogram(sites, strip=True),
        seven_zero_tail_sites=hard)
    (args.output / 'path-census.json').write_text(json.dumps(census, indent=2) + '\n')
    if args.obstruction_only:
        print('Exact 185-step wrong-marker trace and path census reproduced.')
        return
    all_cases = cases_for(sites)
    assert len(all_cases) == 8391
    assert first_failure(table, all_cases) is None
    bounded_sites = hard + random.Random(787).sample(sites, 45)
    bounded_cases = cases_for(bounded_sites)
    control_sites = sorted([s for s in sites if s[1] == 'CC'],
        key=lambda s: s[0] != '1111100101')
    row_cases = cases_for(control_sites + sites)
    results = [
        run_family('one_incoming_action', one_action_recipes(table),
            args.output, bounded_cases),
        run_family('detector_second_action', two_action_recipes(table),
            args.output, bounded_cases),
        run_family('free_row20', free_row_recipes(table), args.output, row_cases),
    ]
    assert [r['recipes'] for r in results] == [7840, 19580, 984]
    summary = dict(status='REPRODUCED', baseline_table_sha256=TABLE_HASH,
        sites_sha256=sha256(sites_path.read_bytes()).hexdigest(),
        baseline_literal_cases=8391, baseline_status='PASS', families=results,
        total_recipes=sum(r['recipes'] for r in results),
        surviving_recipes=sum(r['survivor_count'] for r in results),
        warning='No lower bound, modified-machine blank-tape theorem, '
          'or 245-state consistency machine is established.')
    (args.output / 'search-summary.json').write_text(json.dumps(summary, indent=2) + '\n')

if __name__ == '__main__':
    main()
