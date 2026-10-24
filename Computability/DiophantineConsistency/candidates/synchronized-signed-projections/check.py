#!/usr/bin/env python3
"""Independent full signed-projection, integer-sign and quartic replay.

Imports the pinned algebraic certificate replayer, never the optimizer or
generator. Sign inferences below use literal rows, not coordinate metadata.
"""
from collections import Counter, defaultdict
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import zipfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
OPTIMIZER_ARCHIVE_SHA = 'ff0d3f638d91a905f676f6fe3e40e134979a14880ed34cadf0741604386e8e55'
NATURAL_ARCHIVE_SHA = 'ea82e23aa5956262c823368e947e31ad113201c22654c214b9c6f7427d63e0bf'
PARENT_HASHES = {
    'integer1224': 'f34bc294d33f4d2bab8b9e745ee27df98c5385f8a95d220cfa9bde39a710d167',
    'integer1231': '2a7248de119600cd7a7d9fb51ba90f4de05d03ed431f70654ea28f7071be1219',
    'integer1298': '5fd1448595a29d2457867be4389e23cd69bc8e7a611fbc177a8ca397f686dcea',
}
SOURCE_HASHES = {
    'terminal_elimination.py': '73ca399b859116cedd9b2b7cb107c82926421697f41ee63b9b61f8bc6c1c0027',
    'verify_projection.py': '6c097d79f0ab37e97db3df452afc43f20897fee42e4935af56206fc8f1c1fb3b',
    'audit_common_radix.py': '5852e74a1c6bb3aa8614d6f0d2d229a89f3ca70e226f59116980ab9297f4376c',
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def encoded(obj):
    return (json.dumps(obj, sort_keys=True, separators=(',', ':')) + '\n').encode()


def digest(raw):
    return sha256(raw).hexdigest()


def load(path):
    return json.loads(path.read_bytes())


def decode(terms):
    out = {}
    for c, mon in terms:
        key = tuple(mon)
        need(type(c) is int and c and key == tuple(sorted(key)) and key not in out,
             'canonical nonzero integral monomial')
        need(all(type(i) is int and i >= 0 for i in mon), 'nonnegative coordinate index')
        out[key] = c
    return out


def exact_sos(eq, expanded):
    n = len(eq['variables'])
    need(eq['domain'] == expanded['domain'] == 'unrestricted integers', 'integer domain')
    need(eq['polynomial'] == 'sum(square(row) for row in residuals)', 'SOS equation meaning')
    collected = defaultdict(int)
    used = set()
    max_row = 0
    for row in eq['residuals']:
        terms = list(decode(row['terms']).items())
        need(terms and all(len(m) <= 2 and all(i < n for i in m) for m, _ in terms), 'actual nonempty quadratic row')
        for i, (m, c) in enumerate(terms):
            used.update(m)
            max_row = max(max_row, abs(c))
            collected[tuple(sorted(m + m))] += c*c
            for k, d in terms[:i]:
                collected[tuple(sorted(m + k))] += 2*c*d
    expected = {m: c for m, c in collected.items() if c}
    actual = decode(expanded['terms'])
    need(expected == actual, 'complete polynomial is exact collected residual SOS')
    need(used == set(range(n)) and expanded['variables'] == n, 'all listed coordinates live')
    need(len({v['name'] for v in eq['variables']}) == n, 'unique coordinate names')
    metrics = dict(variables=n, quadratic_rows=len(eq['residuals']), exact_degree=max(map(len, actual)),
        expanded_monomials=len(actual), max_abs_expanded_coefficient=max(map(abs, actual.values())),
        max_abs_row_coefficient=max_row)
    need(metrics['exact_degree'] == 4, 'actual nonzero quartic coefficient')
    for key, value in metrics.items():
        need(eq['metrics'][key] == value, 'actual metric ' + key)
    quartic = next((m, c) for m, c in actual.items() if len(m) == 4)
    return metrics, [quartic[1], list(quartic[0])]


def parent_sign_proof(parent, natural, certificate):
    n = len(natural['variables'])
    prefix = natural['residuals']
    need(parent['variables'][:n] == natural['variables'] and parent['residuals'][:len(prefix)] == prefix,
         'entire natural parent prefix unchanged')
    need(certificate['parent_variables'] == n and certificate['parent_equation_sha256'] == digest(encoded(natural)),
         'sign certificate exact natural parent')
    seeds = certificate['seed_variables']
    need(seeds == sorted(set(seeds)) and all(type(v) is int and 0 <= v < n for v in seeds), 'distinct in-range seeds')
    guards = parent['residuals'][len(prefix):]
    bindings = parent['seed_guards']
    need([b['input'] for b in bindings] == seeds and len(bindings) == len(guards), 'every seed guarded once')
    for j, (binding, row) in enumerate(zip(bindings, guards)):
        v = binding['input']
        a, b, c = binding['auxiliaries']
        need([a, b, c] == list(range(n + 3*j, n + 3*j + 3)), 'fresh ordered unrestricted guard witnesses')
        need(decode(row['terms']) == {(v,): 1, (a, a): -1, (b, b): -1, (c, c): -1, (c,): -1}, 'literal universal nonnegativity guard')
    need(len(parent['variables']) == n + 3*len(seeds), 'all added coordinates are guard witnesses')
    known = set(seeds)
    multipliers = Counter()
    for step in certificate['derivation']:
        v, rid = step['variable'], step['row']
        need(type(v) is int and 0 <= v < n and v not in known, 'fresh sign conclusion')
        need(type(rid) is int and 0 <= rid < len(prefix), 'actual prefix row reference')
        terms = decode(prefix[rid]['terms'])
        need((v,) in terms, 'nonzero linear conclusion coefficient')
        c = terms[(v,)]
        sign = 1 if c > 0 else -1
        for mon, d in terms.items():
            if mon == (v,):
                continue
            need(v not in mon and -sign*d >= 0, 'output-free nonnegative RHS')
            need(all(i in known for i, exponent in Counter(mon).items() if exponent % 2), 'prior odd-power sign premises')
        known.add(v)
        multipliers[abs(c)] += 1
    need(known == set(range(n)), 'entire natural prefix nonnegative at every arbitrary integer zero')
    return dict(natural_variables=n, seed_guards=len(seeds), derived_signs=len(certificate['derivation']),
                positive_multipliers=dict(sorted(multipliers.items())), metadata_sign_assumptions=False)


def evaluate(terms, values):
    total = 0
    for c, mon in terms:
        term = c
        for i in mon:
            term *= values[i]
        total += term
    return total


def restoration_controls(parent, child, certificate):
    """Off-source integer controls, additional to the unbounded symbolic proof."""
    values_count = 0
    retained = certificate['retained_original_variables']
    row_map = dict(zip(certificate['retained_original_rows'], child['residuals']))
    for offset in (0, 1, 3):
        final = [((7*i + offset) % 5) - 2 for i in range(len(retained))]
        values = dict(zip(retained, final))
        for step in reversed(certificate['steps']):
            values[step['variable']] = evaluate(step['restoration'], values)
        need(set(values) == set(range(len(parent['variables']))), 'unique total reverse restoration')
        for rid, row in enumerate(parent['residuals']):
            expected = evaluate(row_map[rid]['terms'], final) if rid in row_map else 0
            need(evaluate(row['terms'], values) == expected, 'reverse restoration preserves each actual residual')
        values_count += 1
    return values_count


def main():
    provenance = load(HERE / 'PROVENANCE.json')
    need(provenance['optimizer_archive_sha256'] == OPTIMIZER_ARCHIVE_SHA, 'signed archive identity')
    archive_path = REPO / provenance['optimizer_archive']
    need(digest(archive_path.read_bytes()) == OPTIMIZER_ARCHIVE_SHA, 'complete original signed archive')
    with zipfile.ZipFile(archive_path) as archive:
        for name, expected in SOURCE_HASHES.items():
            raw = archive.read('con-zfc-batched-certificates/integer/' + name)
            need(digest(raw) == expected and (HERE / 'source' / name).read_bytes() == raw, 'authentic independent source ' + name)
    need(provenance['optimizer_members'] == SOURCE_HASHES, 'exact module hash pins')
    sys.path.insert(0, str(HERE / 'source'))
    spec = importlib.util.spec_from_file_location('independent_projection_replayer', HERE / 'source/verify_projection.py')
    replayer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(replayer)
    build = load(HERE / 'BUILD.json')
    for name, expected in build['sha256'].items():
        need(digest((HERE / name).read_bytes()) == expected, 'generated artifact seal ' + name)
    parents = {}
    parent_results = {}
    for name, expected in PARENT_HASHES.items():
        directory = HERE / 'parents' / name
        need(digest((directory / 'equation.json').read_bytes()) == expected, 'independently frozen integer parent')
        for file_name, pin in provenance['parent_files'][name].items():
            need(digest((directory / file_name).read_bytes()) == pin, 'whole copied parent packet')
        parent = load(directory / 'equation.json')
        natural = load(directory / 'natural_parent.json')
        pins = load(directory / 'PARENT_PINS.json')
        path = REPO / pins['archive']
        need(pins['archive_sha256'] == NATURAL_ARCHIVE_SHA and digest(path.read_bytes()) == NATURAL_ARCHIVE_SHA, 'whole original synchronized archive')
        with zipfile.ZipFile(path) as archive:
            raw = archive.read(pins['parent_member'])
            need(raw == (directory / 'natural_parent.json').read_bytes() and digest(raw) == pins['parent_sha256'], 'actual unchanged natural source member')
        sign = parent_sign_proof(parent, natural, load(directory / 'NONNEGATIVITY.json'))
        metric, _ = exact_sos(parent, load(directory / 'expanded_polynomial.json'))
        parents[name] = parent
        parent_results[name] = dict(sign_certificate=sign, metrics=metric)
    results = {}
    corruptions = []
    for name, selection in provenance['selected'].items():
        parent = parents[selection['parent']]
        child = load(HERE / name / 'equation.json')
        certificate = load(HERE / name / 'terminal_elimination_certificate.json')
        need(certificate['unconstrained_removed'] == [], 'bijection requires no free-coordinate deletion')
        need(not any(k in child for k in ('seed_guards', 'natural_parent_sha256')), 'no stale parent coordinate metadata')
        review = replayer.verify(parent, child, certificate)
        metrics, quartic = exact_sos(child, load(HERE / name / 'expanded_polynomial.json'))
        controls = restoration_controls(parent, child, certificate)
        need(metrics['variables'] == selection['metrics']['output_variables'], 'selected variable count')
        signed = sum(any(c < 0 for c, _ in s['restoration']) for s in certificate['steps'])
        results[name] = dict(metrics=metrics, projection=review, signed_restoration_steps=signed,
                            exact_quartic_witness=quartic, reverse_integer_controls=controls,
                            equation_sha256=digest((HERE / name / 'equation.json').read_bytes()),
                            expanded_sha256=digest((HERE / name / 'expanded_polynomial.json').read_bytes()))
        # A bad restoration is tested with the authentic child hash unchanged.
        bad = deepcopy(certificate)
        bad['steps'][0]['restoration'][0][0] += 1
        try:
            replayer.verify(parent, child, bad)
        except ValueError:
            pass
        else:
            raise ValueError('corrupted signed restoration accepted')
        # Rehash the corrupted child, so rejection requires actual row algebra.
        bad_child = deepcopy(child)
        del bad_child['residuals'][-1]
        bad_cert = deepcopy(certificate)
        bad_cert['output_sha256'] = digest(encoded(bad_child))
        try:
            replayer.verify(parent, bad_child, bad_cert)
        except ValueError:
            pass
        else:
            raise ValueError('missing fully substituted row accepted')
        corruptions.append(dict(variant=name, bad_restoration_rejected=True, rehashed_missing_row_rejected=True))
    probes = load(HERE / 'PROBES.json')['configurations']
    need(len(probes) == 18 and all(p['metrics']['unconstrained_removed'] == 0 for p in probes), 'entire 18-configuration ledger')
    result = dict(status='PASS', optimized_python=bool(sys.flags.optimize), parents=parent_results,
        variants=results, corruption_controls=corruptions, complete_probe_configurations=18,
        scope='Unbounded signed monic identities and every restored actual-row sign certificate, exact complete quartics. No optimizer, compiler, Lean or object-ZFC derivation is imported.')
    output = 'CHECK_OPTIMIZED.json' if sys.flags.optimize else 'CHECK.json'
    (HERE / output).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(dict(status='PASS', variants={name: x['metrics'] for name, x in results.items()},
                         rejected_corruptions=2*len(corruptions)), indent=2))


if __name__ == '__main__':
    main()
