#!/usr/bin/env python3
"""Exhaust the per-step omitted-branch choices of four fixed complete fixtures."""
import argparse
import hashlib
import itertools
import json
import types
from collections import Counter
from pathlib import Path

PINS = {
    'three_mass_projected_endpoint_penalties.py': 'f5fec893112b011564620834e0b76095c1ea53b9545d4fb76ccabb3230bdaaf6',
    'three_mass_selector_projection.py': '8129ec4da0aded05c98993b7575eb3ccfe42ee908c5d15c18a748a8b53d874b8',
    'three_mass_endpoint_penalties.py': '7010ab32c2ac44a84ea61f4393b826cdc1401c654f20364dbad7f694e3eb605c',
    'review_three_mass_projected_endpoint_penalties.py': 'a348f9ffa8e411892cd892986b304bec291adbeb500b167e267632b0327d6be9',
    'review_three_mass_selector_projection.py': 'c519ac0693e4928b64a1fead9ab30212570d50eb63331cf3706d335f20906321',
    'three_mass_arithmetic.py': 'd5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0',
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def load(root, name):
    path = Path(root) / name
    raw = path.read_bytes()
    need(hashlib.sha256(raw).hexdigest() == PINS[name], 'Pinned search dependency')
    module = types.ModuleType('_mixed_search_' + name[:-3])
    module.__file__ = str(path.resolve())
    exec(compile(raw, module.__file__, 'exec'), module.__dict__)
    return module


def run(root, repo):
    Q, R, E, I, A, P = [load(root, name) for name in PINS]
    data, archives = P.source_bytes(repo)
    counts = Counter()
    cases = []
    with P.subjects(data) as (C, CT):
        for name, horizon, clean in (
            ('incdec', 2, False), ('incdec', 2, True),
            ('incchain3', 3, False), ('incchain3', 3, True),
        ):
            cert = A.fixture(C, CT, name, horizon, clean)
            forward = cert.get('forward_certificate', cert)
            branches = len(forward['branches'])
            rows, best, best_uniform = [], None, None
            for indices in itertools.product(range(branches), repeat=horizon):
                counts['per_step_index_layouts'] += 1
                for mode, endpoints in itertools.product(
                    ('direct', 'factored', 'horner'),
                    ('none', 'initial', 'terminal', 'both'),
                ):
                    packet = Q.emit(P, R, E, cert, mode, list(indices), endpoints)
                    checked, polys = I.check(A, cert, packet)
                    row = dict(indices=list(indices), mode=mode, endpoints=endpoints,
                               ledger=checked['ledger'], degree=checked['degree'])
                    rows.append(row)
                    key = (checked['ledger']['total'], checked['ledger']['M'])
                    candidate = (key, row, packet)
                    if best is None or key < best[0]:
                        best = candidate
                    if len(set(indices)) == 1 and (best_uniform is None or key < best_uniform[0]):
                        best_uniform = candidate
                    counts['complete_coefficient_degree_ledger_checks'] += 1
                    counts['paid_live_gates'] += checked['paid']
                    counts['retained_residuals'] += checked['rows']
                    counts['weighted_step_guards'] += checked['guards']
            need(len(rows) == branches ** horizon * 12, 'Entire declared finite search')
            lifts = []
            for x in (0, 1, 4, 17):
                original = CT.make_clean_witness(cert, {'x': x}) if clean else C.make_witness(cert, {'x': x})
                mass = P.push(cert, original)
                packet = best[2]
                projected = {k: v for k, v in mass.items() if k not in packet['restoration_forms']}
                info, (poly, parent, correction, restoration) = I.check(A, cert, packet)
                restored = projected | {k: A.ev(v, projected) for k, v in restoration.items()}
                need(min(projected.values()) >= 0 and restored == mass, 'Natural exact restoration')
                need(A.ev(poly, projected) == A.ev(parent, projected) == 0, 'Full independent zero outputs')
                need(P.pull(cert, restored) == original, 'Original offset lift')
                lifts.append(dict(input=x, projected=projected))
                counts['complete_winner_natural_lifts'] += 1
            cases.append(dict(fixture=name, horizon=horizon, clean=clean,
                              branches=branches, certificate=cert,
                              uniform_best=best_uniform[1], best=best[1],
                              natural_witnesses=best[2]['natural_witnesses'],
                              complete_best=best[2], all_ledgers=rows,
                              natural_lifts=lifts))
    need([c['best']['ledger']['total'] for c in cases] == [44, 43, 86, 83], 'Recorded complete frontier')
    return dict(status='PASS', dependency_pins=PINS, archive_pins=archives,
                counts=dict(counts), cases=cases,
                scope='Four external-horizon source fixtures; every per-step implicit index and the 12 stated gate/endpoint schedules, with ties broken by fewer multiplications then enumeration order. No general circuit optimum or universal bound.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = run(args.root, args.repo)
    if args.expect:
        A = load(args.root, 'review_three_mass_selector_projection.py')
        need(A.exact(result, json.loads(args.expect.read_text())), 'Typed search receipt mismatch')
    if args.output:
        args.output.write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps(dict(counts=result['counts'], best=[c['best'] for c in result['cases']]), indent=2))
