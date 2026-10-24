#!/usr/bin/env python3
"""Independent complete-quartic and calibration audit; imports no packet program."""
import argparse
from collections import defaultdict
from copy import deepcopy
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
POLICIES = ('support8', 'support16', 'support32', 'support16_affine3',
            'support16_affine4', 'support16_quadratic_first')


def need(ok, label):
    if not ok:
        raise ValueError(label)


def load(path):
    return json.loads(path.read_text())


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def compact(obj):
    return (json.dumps(obj, sort_keys=True, separators=(',', ':')) + '\n').encode()


def collected(terms):
    out = defaultdict(int)
    for coefficient, monomial in terms:
        need(type(coefficient) is int and all(type(v) is int and v >= 0 for v in monomial), 'integer term')
        out[tuple(sorted(monomial))] += coefficient
    return {m: c for m, c in out.items() if c}


def terms(poly):
    return [[c, list(m)] for m, c in sorted(poly.items())]


def squared_rows(equation):
    """Collect diagonals once and distinct cross terms twice, independently."""
    out = defaultdict(int)
    for row in equation['residuals']:
        entries = list(collected(row['terms']).items())
        need(all(len(m) <= 2 for m, _ in entries), 'quadratic input row')
        for i, (m, c) in enumerate(entries):
            out[tuple(sorted(m + m))] += c * c
            for n, d in entries[i + 1:]:
                out[tuple(sorted(m + n))] += 2 * c * d
    return {m: c for m, c in out.items() if c}


def shifted(poly, shifts):
    """Expand each monomial by independent binary choices of variable/constant."""
    out = defaultdict(int)
    for monomial, coefficient in poly.items():
        choices = [[(v, 1), (None, shifts[v])] if v in shifts else [(v, 1)] for v in monomial]
        for selected in product(*choices):
            c = coefficient
            m = []
            for v, factor in selected:
                c *= factor
                if v is not None:
                    m.append(v)
            out[tuple(m)] += c
    return {m: c for m, c in out.items() if c}


def census(equation, poly):
    return dict(variables=len(equation['variables']), rows=len(equation['residuals']),
                degree=max(map(len, poly), default=0), monomials=len(poly),
                height=max(map(abs, poly.values()), default=0),
                row_height=max(abs(c) for r in equation['residuals'] for c, _ in r['terms']))


def endpoint(directory, allow_free=()):
    equation = load(directory / 'equation.json')
    poly = squared_rows(equation)
    need(load(directory / 'expanded_polynomial.json') == dict(schema='sparse_integer_polynomial_v1',
         domain='unrestricted integers', variables=len(equation['variables']), terms=terms(poly)),
         'complete coefficient equality')
    metrics = census(equation, poly)
    need(load(directory / 'METRICS.json') == metrics and metrics['degree'] == 4, 'exact complete census')
    used = {v for r in equation['residuals'] for _, m in r['terms'] for v in m}
    need(used <= set(range(len(equation['variables']))) and
         set(range(len(equation['variables']))) - used == set(allow_free), 'all unused coordinates explicit')
    return equation, poly, metrics


def audit(binding):
    pins = load(HERE / 'SOURCE_PINS.json')
    for name, expected in pins['parent_files'].items():
        need(digest(ROOT / name) == expected, 'whole inherited pin ' + name)
    for name, expected in pins['own_core'].items():
        need(digest(HERE / name) == expected, 'whole own pin ' + name)
    ordinary = load(ROOT / 'research/round14-pair-guard-compression/CERTIFICATE.json')['variants']
    index = load(HERE / 'full-data/INDEX.json')
    need(binding['schema'] == 'complete_round14_pair_guard_calibration_binding_v1' and
         binding['ordinary_manifest_sha256'] == pins['ordinary_manifest_sha256'] and
         binding['finite_data_index_sha256'] == digest(HERE / 'full-data/INDEX.json'), 'calibration ancestry')
    need(binding['named_logical_dependencies'] == ['KEndpoint.c222_iff_zf_refutation',
         'ConstructibleChoice.zf_refutation_iff_zfc_refutation'] and
         binding['accepted_metrics_or_canonical_promotion_claimed'] is False, 'calibration scope')
    need(set(binding['variants']) == set(ordinary) == {'derived517', 'hybrid519'}, 'both ancestries')
    need(len(index['files']) == 118 and set(index['files']) ==
         {str(p.relative_to(HERE / 'full-data')) for p in (HERE / 'full-data').rglob('*')
          if p.is_file() and p.name != 'INDEX.json'}, 'closed generated inventory')
    for name, expected in index['files'].items():
        need(digest(HERE / 'full-data' / name) == expected, 'whole generated pin ' + name)
    summaries = {}
    for tag in ordinary:
        entry = binding['variants'][tag]
        oldpath = ordinary[tag]['factored_directory'] + '/factored_source.json'
        need(entry['old_factored_source'] == dict(path=oldpath, sha256=digest(ROOT / oldpath)), 'exact old endpoint')
        sourcepaths = ['full-data/sources/' + tag + '/' + n for n in
                       ['BODY_GUARD_MAP.json', 'IDEAL_BINDINGS.json', 'equation.json']]
        need(entry['new_source_files'] == {n: digest(HERE / n) for n in sourcepaths}, 'complete literal source binding')
        for name in sourcepaths:
            need((HERE / name).read_bytes() == (HERE / name.replace('full-data/', 'data/', 1)).read_bytes(),
                 'normative source-only/full equality')
        free = [136, 138] if tag == 'derived517' else [160, 162]
        source, _, raw = endpoint(HERE / 'full-data/sources' / tag, free)
        need(set(entry['profiles']) == set(POLICIES), 'all six policies')
        profiles = {}
        for policy in POLICIES:
            prefix = 'full-data/profiles/' + tag + '/' + policy + '/'
            directory = HERE / prefix
            plain, pp, pm = endpoint(directory)
            center, cp, cm = endpoint(directory / 'centered')
            cert = load(directory / 'terminal_elimination_certificate.json')
            tc = load(directory / 'centered/translation_certificate.json')
            selected = {i: -1 for i, v in enumerate(plain['variables']) if v['name'].startswith('crt.encoded')
                        or v['name'] in ('t0', 'M0') or v['name'].endswith('minus1')}
            need(cert['unconstrained_removed'] == free and len(cert['steps']) + len(free) +
                 len(plain['variables']) == len(source['variables']), 'entire coordinate partition census')
            need(tc['input_sha256'] == sha256(compact(plain)).hexdigest() and
                 tc['output_sha256'] == sha256(compact(center)).hexdigest() and
                 tc['shifts'] == [[i, s] for i, s in selected.items()], 'translation endpoints and exact name rule')
            need(len(selected) == (13 if tag == 'derived517' else 14), 'all translated coordinates')
            need(shifted(pp, selected) == cp and shifted(cp, {i: -s for i, s in selected.items()}) == pp,
                 'whole-quartic forward and inverse translation')
            names = [prefix + n for n in ['ENGINE_VERIFICATION.json', 'METRICS.json',
                     'equation.json', 'expanded_polynomial.json', 'terminal_elimination_certificate.json',
                     'centered/METRICS.json', 'centered/equation.json', 'centered/expanded_polynomial.json',
                     'centered/translation_certificate.json']]
            profile = entry['profiles'][policy]
            need(profile['complete_files'] == {n: digest(HERE / n) for n in names}, 'all nine projection/translation members')
            need(profile['plain_census'] == pm and profile['centered_census'] == cm and
                 profile['integral_restorations'] == len(cert['steps']) and profile['unconstrained_coordinates'] == free
                 and profile['translated_coordinates'] == len(selected), 'calibration complete measured statistics')
            need(index['summaries'][tag]['profiles'][policy] == dict(plain=pm, centered=cm), 'complete index summaries')
            profiles[policy] = dict(plain=pm, centered=cm, restorations=len(cert['steps']),
                                    free=free, translated=len(selected))
        summaries[tag] = dict(raw=raw, profiles=profiles)
    return summaries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    binding = load(HERE / 'CALIBRATION_BINDING.json')
    result = audit(binding)
    mutations = []
    for label, mutate in [
        ('missing ancestry', lambda b: b['variants'].pop('hybrid519')),
        ('missing profile', lambda b: b['variants']['derived517']['profiles'].pop('support8')),
        ('source endpoint', lambda b: b['variants']['derived517']['old_factored_source'].__setitem__('sha256', '0' * 64)),
        ('incomplete source binding', lambda b: b['variants']['hybrid519']['new_source_files'].popitem()),
        ('incomplete endpoint chain', lambda b: b['variants']['derived517']['profiles']['support8']['complete_files'].popitem()),
        ('wrong global degree', lambda b: b['variants']['derived517']['profiles']['support8']['centered_census'].__setitem__('degree', 3)),
        ('wrong free coordinate', lambda b: b['variants']['hybrid519']['profiles']['support8']['unconstrained_coordinates'].pop()),
        ('wrong translation census', lambda b: b['variants']['derived517']['profiles']['support8'].__setitem__('translated_coordinates', 12)),
    ]:
        bad = deepcopy(binding)
        mutate(bad)
        try:
            audit(bad)
        except ValueError:
            mutations.append(label)
        else:
            raise ValueError('accepted malformed calibration ' + label)
    receipt = dict(status='PASS', optimized_python=bool(sys.flags.optimize),
                   script_sha256=digest(Path(__file__)), source_pins_sha256=digest(HERE / 'SOURCE_PINS.json'),
                   calibration_sha256=digest(HERE / 'CALIBRATION_BINDING.json'),
                   complete_quartics=26, plain_centered_profiles=24, monic_projection_certificates=12,
                   inherited_pins=len(load(HERE / 'SOURCE_PINS.json')['parent_files']),
                   actual_corruptions_rejected=mutations, summaries=result,
                   packet_or_optimizer_imported=False, no_new_ordinary_semantics_claimed=True)
    text = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    if args.output.exists():
        need(args.output.read_text() == text, 'refuse changed output overwrite')
    else:
        args.output.write_text(text)
    print(json.dumps(dict(status='PASS', complete_quartics=26, profiles=24, actual_corruptions=len(mutations),
                          optimized_python=bool(sys.flags.optimize)), sort_keys=True))


if __name__ == '__main__':
    main()
