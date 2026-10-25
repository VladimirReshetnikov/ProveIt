#!/usr/bin/env python3
"""Inert exact arithmetic on archived JSON data; executes no incoming program."""
import argparse
from collections import defaultdict
from copy import deepcopy
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path
import sys
import zipfile
from read_archives import archive_bytes, COMMIT

HERE = Path(__file__).resolve().parent
CASES = {
    'ConZFC_Cofinal_Witnesses_2026-10-24.zip': ['direct/principal'],
    'ConZFC_Paired_Guards_Centered_Carriers_2026-10-24.zip': ['alternative/paired', 'alternative/squared_paired'],
    'ConZFC_Residue_Compiler_2026-10-24.zip': ['equations/natural332/natural', 'equations/natural333/natural'],
    'ConZFC_Shared_Binomial_Certificates_2026-10-24.zip': ['direct/equation319/natural', 'direct/equation320/natural'],
    'ConZFC_Shared_Pell_Bound_261_2026-10-24.zip': ['portable/equations/primary/natural', 'portable/equations/sparse/natural'],
    'ConZFC_Unified_Binomial_Even_Indices_Round15_2026-10-24.zip': ['direct/integer442'] +
        ['architecture/' + n + '/natural' for n in ['unified_derived_cantor', 'unified_derived_shell',
         'unified_slack_cantor', 'unified_slack_shell', 'unified_square_derived_cantor', 'unified_square_slack_shell']],
    'ConZFC_Weak_Carriers_and_Shared_Signs_2026-10-24.zip': ['direct'],
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def poly(ts):
    result = defaultdict(int)
    for c, m in ts:
        need(type(c) is int and all(type(v) is int and v >= 0 for v in m), 'integer literal terms')
        result[tuple(sorted(m))] += c
    return {m: c for m, c in result.items() if c}


def check(equation, polynomial):
    nv = len(equation['variables'])
    result = defaultdict(int)
    for row in equation['residuals']:
        entries = list(poly(row['terms']).items())
        need(all(len(m) <= 2 and all(v < nv for v in m) for m, c in entries), 'complete quadratic row bounds')
        for i, (m, c) in enumerate(entries):
            result[tuple(sorted(m + m))] += c * c
            for n, d in entries[i + 1:]:
                result[tuple(sorted(m + n))] += 2 * c * d
    result = {m: c for m, c in result.items() if c}
    need(poly(polynomial['terms']) == result and len(polynomial['terms']) == len(result),
         'all collected coefficients exactly match the complete sum of squares')
    used = {v for m in result for v in m}
    need(used == set(range(nv)), 'all displayed endpoint variables occur')
    need(polynomial['variables'] == nv and polynomial['domain'] == equation['domain'], 'complete polynomial signature')
    return dict(domain=equation['domain'], variables=nv, quadratic_rows=len(equation['residuals']),
                degree=max(map(len, result)), monomials=len(result), height=max(map(abs, result.values())))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    inventory = json.loads((HERE / 'INVENTORY.json').read_text())
    headers = {Path(a['path']).name:a for a in inventory['archives']}
    results, rejected = [], []
    for name, folders in CASES.items():
        blob = archive_bytes('docs/incoming/' + name)
        need(sha256(blob).hexdigest() == headers[name]['sha256'], 'whole archive pin')
        with zipfile.ZipFile(BytesIO(blob)) as archive:
            root = archive.namelist()[0].split('/')[0] + '/'
            members = {m['name']:m for m in headers[name]['members']}
            for folder in folders:
                names = [root + folder + '/' + n for n in ['equation.json', 'expanded_polynomial.json']]
                data = [archive.read(n) for n in names]
                for n, b in zip(names, data):need(sha256(b).hexdigest() == members[n]['sha256'], 'whole member pin')
                equation, polynomial = map(json.loads, data)
                census = check(equation, polynomial)
                results.append(dict(archive=name, members={n:members[n]['sha256'] for n in names}, census=census))
                for kind in ['row', 'coefficient']:
                    e, p = deepcopy(equation), deepcopy(polynomial)
                    if kind == 'row':e['residuals'][0]['terms'][0][0] += 1
                    else:p['terms'][0][0] += 1
                    try:check(e, p)
                    except ValueError:rejected.append(name + ':' + folder + ':' + kind)
                    else:raise ValueError('accepted malformed literal ' + kind)
    name = 'ConZFC_Height_One_and_Degree_464_2026-10-24.zip'
    blob = archive_bytes('docs/incoming/' + name)
    need(sha256(blob).hexdigest() == headers[name]['sha256'], 'height-one archive pin')
    with zipfile.ZipFile(BytesIO(blob)) as archive:
        root = archive.namelist()[0].split('/')[0] + '/'
        member = root + 'height_one/output/polynomial.json';data = archive.read(member);p = json.loads(data);q = poly(p['terms'])
        need(len(q) == len(p['terms']) and set(q.values()) == {-1, 1}, 'literal coefficient height one')
        need({v for m in q for v in m} == set(range(len(p['variables']))), 'all height-one coordinates occur')
        height_one = dict(archive=name, member=member, member_sha256=sha256(data).hexdigest(),
                          domain=p['domain'], variables=len(p['variables']), monomials=len(q),
                          degree=max(map(len,q)), height=1, constant=q.get((), 0),
                          lifting_certificate_or_value_bridge_audited=False)
    receipt = dict(status='PASS', optimized_python=bool(sys.flags.optimize), commit=COMMIT,
                   inventory_sha256=sha256((HERE/'INVENTORY.json').read_bytes()).hexdigest(),
                   script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(), complete_quartics=results,
                   separate_height_one_literal_census=height_one, actual_corruptions_rejected=rejected,
                   incoming_code_imported_or_executed=False, incoming_archives_extracted_or_restored=False,
                   scope='Complete literal data/coefficient checks only; no source transformation, circuit count/degree, unbounded calibration, or incoming runtime approval.')
    text = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    if args.output.exists():need(args.output.read_text() == text, 'refuse changed receipt overwrite')
    else:args.output.write_text(text)
    print(json.dumps(dict(status='PASS', complete_quartics=len(results), actual_corruptions=len(rejected),
                         optimized_python=bool(sys.flags.optimize)), sort_keys=True))


if __name__ == '__main__':
    main()
