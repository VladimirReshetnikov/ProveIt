#!/usr/bin/env python3
"""Own stdlib full SOS collector and complete24-profile retention comparison."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
PINS = {'build.py': '893e68ac06b1f8cf093bf7e422301d3ea0045b8188a2d41d25bf17e71ddfec67',
        'check.py': '3a8d13c3005a5201b225ea93d1e9dcb2c52a5ecb0c18964dfd22776e7596faba',
        'SOURCE_PINS.json': '6adc25e7f34d2c0ea1a5512ed39547ebd09386fc823331448b8e4a968dda5d01',
        'BUILD.json': '3dfc34cc97f32bbd52cc301352ea304446cc207c1d75cbac224855b14f2b42a6'}


def need(ok, why):
    if not ok:
        raise ValueError(why)


def load(path):
    return json.loads(path.read_bytes())


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def decode(terms, n):
    answer = {}
    for coefficient, monomial in terms:
        key = tuple(monomial)
        need(type(coefficient) is int and coefficient != 0 and key == tuple(sorted(key)) and key not in answer,
             'canonical unique sparse integer coefficient')
        need(all(type(v) is int and 0 <= v < n for v in key), 'every monomial coordinate in the full equation')
        answer[key] = coefficient
    return answer


def measure(folder):
    equation = load(folder / 'equation.json')
    quartic = load(folder / 'polynomial.json')
    n = len(equation['variables'])
    collected = Counter()
    live = set()
    row_height = 0
    for row in equation['residuals']:
        terms = list(decode(row['terms'], n).items())
        for i, (left, a) in enumerate(terms):
            need(len(left) <= 2, 'quadratic residual')
            live.update(left)
            row_height = max(row_height, abs(a))
            for j in range(i, len(terms)):
                right, b = terms[j]
                collected[tuple(sorted(left + right))] += a * b * (1 if i == j else 2)
    exact = {m: c for m, c in collected.items() if c}
    need(exact == decode(quartic['terms'], n), 'every coefficient of the complete sum of squared residuals')
    need(live == set(range(n)) and max(map(len, exact)) == 4, 'all integer coordinates live and exact quartic degree')
    measured = dict(variables=n, quadratic_rows=len(equation['residuals']), exact_degree=4,
                    expanded_monomials=len(exact), max_abs_expanded_coefficient=max(map(abs, exact.values())),
                    max_abs_row_coefficient=row_height, variable_kinds=dict(Counter(v['kind'] for v in equation['variables'])))
    need(equation['metrics'] == measured, 'all actual measured census fields')
    return measured


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    packet = args.packet.resolve()
    for name, h in PINS.items():
        need(digest(packet / name) == h, 'whole reviewed current core ' + name)
    root = packet.parents[1]
    pins = load(packet / 'SOURCE_PINS.json')
    old = root / pins['parent_profile']
    need(digest(old / 'MANIFEST.json') == '933bf6ad5871142a4474881ac322e4364462c9cef6513984b976c1de7e2c85a9', 'exact frozen63 profile family')
    for name, h in load(old / 'MANIFEST.json')['files'].items():
        need(digest(old / name) == h, 'complete frozen parent member ' + name)
    for name, h in load(packet / 'BUILD.json')['files'].items():
        need(digest(packet / name) == h, 'whole generated current member ' + name)
    census = load(packet / 'CENSUS.json')
    previous = load(old / 'CENSUS.json')
    need(set(census) == set(previous) and len(census) == 24, 'same complete24 profile configurations')
    cuts = load(packet / 'CUTS.json')
    variable_map = dict(cuts['retained_old_variable_map'])
    row_map = dict(cuts['parent_row_map'])
    results = {}
    histogram = Counter()
    for name in sorted(census):
        before = measure(old / name)
        after = measure(packet / name)
        need(previous[name]['metrics'] == before and census[name]['metrics'] == after, 'both entire measured profiles match their censuses')
        a = load(old / name / 'projection.json')
        b = load(packet / name / 'projection.json')
        need(a['unconstrained_removed'] == b['unconstrained_removed'] == [], 'no unconstrained integer deletion')
        retained = set(b['retained_original_variables'])
        eliminated = [s['variable'] for s in b['steps']]
        need(len(eliminated) == len(set(eliminated)) and not (set(eliminated) & retained) and set(eliminated) | retained == set(range(1454)), 'entire current integer coordinate partition')
        sa = set(a['retained_original_variables'])
        mapped = {variable_map[v] for v in sa if v in variable_map}
        sr = set(a['retained_original_rows'])
        tr = set(b['retained_original_rows'])
        mapped_rows = {row_map[r] for r in sr if row_map[r] is not None}
        delta = {k: after[k] - before[k] for k in ['variables', 'quadratic_rows', 'expanded_monomials', 'max_abs_expanded_coefficient']}
        histogram[(delta['variables'], delta['quadratic_rows'], delta['expanded_monomials'])] += 1
        removed = sorted(sa - set(variable_map))
        lost = sorted(mapped - retained)
        extra = sorted(retained - mapped)
        need(removed == [1309, 1310, 1311] and after['variables'] == before['variables'] - len(removed) - len(lost) + len(extra), 'actual loss/extra partition explains every variable delta')
        if name.endswith('/support2_affine1'):
            need(lost == [1234] and extra == [] and sorted(mapped_rows - tr) == [1152] and sorted(tr - mapped_rows) == [], 'actual extra eliminated accumulator/defining row in support2_affine1')
            step = next(s for s in b['steps'] if s['variable'] == 1234)
            need(step['row_id'] == 1152 and step['restoration_degree'] == 2 and step['restoration'] == [[-1, [106, 106]], [1, [1235]]], 'actual signed quadratic accumulator inverse')
        elif name.endswith('/retained'):
            need(lost == [] and extra == [1267] and sorted(mapped_rows - tr) == [] and sorted(tr - mapped_rows) == [1185], 'actual retained new square and row')
        else:
            need(lost == extra == [] and mapped_rows == tr, 'remaining20 profiles differ only by the removed guard triple and row')
        results[name] = dict(old_metrics=before, new_metrics=after, measured_delta=delta,
                             removed_old_retained_variables=removed, mapped_old_retained_lost=lost, new_retained_extra=extra,
                             mapped_old_rows_lost=sorted(mapped_rows - tr), new_rows_extra=sorted(tr - mapped_rows),
                             raw106_retained=106 in retained, new_square1267_retained=1267 in retained,
                             signed_restorations=len(b['steps']), unconstrained_removed=[])
    need(histogram == {(-3, -1, -14): 20, (-2, 0, -11): 2, (-4, -2, -14): 2}, 'all actual measured delta classes')
    result = dict(status='PASS', optimized_python=bool(sys.flags.optimize), profiles=results,
                  measured_delta_classes=[dict(variables=v, rows=r, terms=t, profiles=count) for (v, r, t), count in sorted(histogram.items())],
                  reviewed_core=PINS, full_old_and_new_quartics=48, all_coefficients_recollected=True,
                  author_checker_builder_optimizer_or_incoming_code_imported=False, ordinary_semantics_claimed=False,
                  source_sha256=digest(Path(__file__)))
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output.exists():
        need(args.output.read_text() == text, 'refuse changed peer profile receipt overwrite')
    else:
        args.output.write_text(text)
    print(json.dumps({'status': 'PASS', 'profiles': 24, 'full_quartics': 48, 'delta_classes': len(histogram)}, sort_keys=True))


if __name__ == '__main__':
    main()
