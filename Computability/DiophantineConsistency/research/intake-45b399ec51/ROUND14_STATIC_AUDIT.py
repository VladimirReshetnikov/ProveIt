#!/usr/bin/env python3
"""Own read-only ZIP/data audit; never imports or executes incoming code."""
import argparse
from collections import Counter
import copy
from hashlib import sha256
import io
import json
from pathlib import Path
import sys
import subprocess
import zipfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
ARCHIVE = 'ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24.zip'
ARCHIVE_SHA = 'a303369f9973ae400ba28e3b080960c8480af8359c23434473d86d4a3ef7a1d8'
ARCHIVE_COMMIT = '45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6'
PREFIX = ARCHIVE[:-4] + '/'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def poly(terms):
    out = Counter()
    for coefficient, monomial in terms:
        out[tuple(sorted(monomial))] += coefficient
    return {m: c for m, c in out.items() if c}

def add(*values):
    return poly((c, m) for p in values for m, c in p.items())

def scale(p, n):
    return {m: n*c for m, c in p.items() if n*c}

def mul(p, q):
    return poly((c*d, m+n) for m, c in p.items() for n, d in q.items())

def sub(p, images):
    out = {}
    for monomial, coefficient in p.items():
        value = {(): coefficient}
        for v in monomial:
            value = mul(value, images.get(v, {(v,): 1}))
        out = add(out, value)
    return out

def canon(obj):
    return (json.dumps(obj, sort_keys=True, separators=(',', ':'))+'\n').encode()

def sos(eq):
    return add(*(mul(poly(r['terms']), poly(r['terms'])) for r in eq['residuals']))

def census(eq, full):
    expected = sos(eq)
    need(expected == poly(full['terms']), 'every quartic coefficient')
    need(all(len(m) <= 2 for r in eq['residuals'] for m in poly(r['terms'])), 'quadratic rows')
    need({v for m in expected for v in m} == set(range(len(eq['variables']))), 'whole variable occurrence')
    return dict(variables=len(eq['variables']), rows=len(eq['residuals']),
                terms=len(expected), degree=max(map(len, expected)),
                height=max(map(abs, expected.values())))

def projection(src, dst, cert):
    need(sha256(canon(src)).hexdigest() == cert['input_sha256'], 'projection parent hash')
    need(sha256(canon(dst)).hexdigest() == cert['output_sha256'], 'projection child hash')
    rows = {i: poly(r['terms']) for i, r in enumerate(src['residuals'])}
    live = set(range(len(src['variables'])))
    for step in cert['steps']:
        v, rid = step['variable'], step['row_id']
        need(v in live and rid in rows, 'live monic pivot')
        restore = poly(step['restoration'])
        need(all(v not in m and set(m) <= live and len(m) <= 2 and type(c) is int
                 for m, c in restore.items()), 'integer triangular restoration')
        want = add({(v,): 1}, scale(restore, -1))
        need(rows[rid] in (want, scale(want, -1)), 'exact monic pivot row')
        del rows[rid]
        for r, p in list(rows.items()):
            p = sub(p, {v: restore})
            need(all(len(m) <= 2 for m in p), 'quadratic substitution boundary')
            if p:
                rows[r] = p
            else:
                del rows[r]
        live.remove(v)
    keep, unused = cert['retained_original_variables'], cert['unconstrained_removed']
    need(len(keep) == len(set(keep)) and len(unused) == len(set(unused)), 'coordinate uniqueness')
    need(set(keep).isdisjoint(unused) and set(keep)|set(unused) == live, 'coordinate partition')
    need({v for p in rows.values() for m in p for v in m} == set(keep), 'unused partition')
    need(sorted(rows) == cert['retained_original_rows'], 'row partition')
    need(dst['variables'] == [src['variables'][v] for v in keep], 'whole child metadata')
    rename = {v: {(i,): 1} for i, v in enumerate(keep)}
    need(len(rows) == len(dst['residuals']), 'whole child row count')
    for rid, actual in zip(sorted(rows), dst['residuals']):
        need(sub(rows[rid], rename) == poly(actual['terms']), 'whole surviving residual')
        need(src['residuals'][rid]['label'] == actual['label'], 'whole residual labels')
    return dict(restorations=len(cert['steps']), free_coordinates_removed=len(unused),
                integer_existence_equivalence=True, whole_tuple_bijection=False)

def translation(src, dst, cert):
    need(sha256(canon(src)).hexdigest() == cert['input_sha256'], 'translation parent hash')
    need(sha256(canon(dst)).hexdigest() == cert['output_sha256'], 'translation child hash')
    need(src['variables'] == dst['variables'], 'translation variables')
    shifts = dict(cert['shifts'])
    need(len(shifts) == len(cert['shifts']) and all(type(s) is int for s in shifts.values()), 'integer translations')
    forward = {v: {(v,): 1, (): s} for v, s in shifts.items()}
    inverse = {v: {(v,): 1, (): -s} for v, s in shifts.items()}
    need(len(src['residuals']) == len(dst['residuals']), 'translation rows')
    for old, new in zip(src['residuals'], dst['residuals']):
        need(old['label'] == new['label'], 'translation labels')
        need(sub(poly(old['terms']), forward) == poly(new['terms']), 'whole forward translation')
        need(sub(poly(new['terms']), inverse) == poly(old['terms']), 'whole inverse translation')
    return dict(translated_coordinates=len(shifts), two_sided_integer_bijection=True)

def interfaces(meta):
    """Collect all actual power and indexed-Pell rows before affine export."""
    variables, rows = meta['variables'], meta['rows']
    names = {v['name']: i for i, v in enumerate(variables)}
    defs = {int(v): rows[r] for v, r in meta['gates'].items()}
    ports = {a[1] for p in meta['powers'] for a in p.values() if a[0] == 'v'}
    indices = {tuple(s['exponent']): s['pair'] for s in meta['indices']}
    ports |= {a[1] for pair in indices.values() for a in pair if a[0] == 'v'}
    ports |= {names[n] for n in names if n.startswith(('shared.', 'shared_index.', 'base', 'index')) and variables[names[n]]['kind'] != 'gate'}
    def atom(a):
        return {(): a[1]} if a[0] == 'c' and a[1] else {} if a[0] == 'c' else {(a[1],): 1}
    def expand(p, extra=()):
        stop = ports | set(extra)
        memo = {}
        def vvalue(v):
            if v in stop or v not in defs:
                return {(v,): 1}
            if v not in memo:
                q = poly(defs[v]['terms'])
                need(q.pop((v,), None) == 1, 'monic gate interface')
                q = scale(q, -1)
                memo[v] = sub(q, {u: vvalue(u) for m in q for u in m})
            return memo[v]
        return sub(p, {v: vvalue(v) for m in p for v in m})
    A = atom(meta['scale'][1])
    base_moduli = {}
    for j, p in enumerate(meta['powers']):
        n, k, m = (atom(p[r]) for r in ['base', 'exponent', 'output'])
        X, Y = map(atom, indices[tuple(p['exponent'])])
        q = {(names['pow'+str(j)+'.quotient'],): 1}
        row = next(r for r in rows if r['label'] == 'pow'+str(j)+'.power_congruence')
        found = []
        for name, v in names.items():
            if name.startswith('base') and name.endswith('.T'):
                want = add(X, mul(n, Y), scale(mul(A, Y), -1), scale(m, -1), scale(mul({(v,): 1}, q), -1))
                if expand(poly(row['terms'])) == want:
                    found.append(v)
        need(len(found) == 1, 'actual whole power congruence')
        T = found[0]
        if T not in base_moduli:
            label = variables[T]['name'][:-1]+'T_definition'
            row = next(r for r in rows if r['label'] == label)
            want = add(scale(mul(A, n), 2), scale(mul(n, n), -1), {(): -1, (T,): -1})
            need(expand(poly(row['terms'])) == want, 'actual positive-base modulus')
            base_moduli[T] = p['base']
        else:
            need(base_moduli[T] == p['base'], 'base sharing binding')
    # Seed Y>=k is a literal retained-slack row, independent of power outputs.
    for seed in meta['seeds']:
        X, Y = seed['pair']; yname = variables[Y[1]]['name']; tag = yname.rsplit('.', 1)[0]
        row = next(r for r in rows if r['label'] == tag+'.index_at_most_Y')
        slack = names[tag+'.YminusK']
        need(expand(poly(row['terms'])) == add(atom(Y), scale(atom(seed['exponent']), -1), {(slack,): -1}), 'actual seed-slack cut')
    return dict(actual_power_congruences=len(meta['powers']), actual_base_moduli=len(base_moduli),
                actual_seed_slack_rows=len(meta['seeds']), derived_indices=len(meta['derivations']))

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    path = REPO/'docs/incoming'/ARCHIVE
    blob = path.read_bytes() if path.exists() else subprocess.check_output(
        ['git', 'show', ARCHIVE_COMMIT+':docs/incoming/'+ARCHIVE], cwd=REPO)
    need(sha256(blob).hexdigest() == ARCHIVE_SHA, 'exact incoming archive or pinned historical Git blob')
    with zipfile.ZipFile(io.BytesIO(blob)) as z:
        members = {n[len(PREFIX):]: z.read(n) for n in z.namelist() if not n.endswith('/')}
    get = lambda n: json.loads(members[n])
    manifest = get('MANIFEST_SHA256.json')['files']
    need(set(manifest) == set(members)-{'MANIFEST_SHA256.json'}, 'whole closed ZIP manifest')
    for n, record in manifest.items():
        need(len(members[n]) == record['bytes'] and sha256(members[n]).hexdigest() == record['sha256'], 'whole release member '+n)
    for n, h in get('direct/SOURCE_PINS.json').items():
        need(sha256(members[n]).hexdigest() == h, 'whole direct pin '+n)
    missing = []
    binding = get('architecture/SOURCE_BINDING.json')
    for record in binding['runtime_files']+binding['runtime_data']:
        if record['path'] not in members:
            missing.append(record['path'])
        else:
            data = members[record['path']]
            need(sha256(data).hexdigest() == record['sha256'] and len(data) == record['bytes'], 'whole runtime module binding')
    need(len(missing) == 3 and all(n.endswith('.zip') for n in missing), 'exact documented omitted provenance archives')
    results = []
    rejected = []
    for raw, signed, factored, final in [
        ('architecture/carrier_hybrid_shell/raw', 'direct/hybrid_noguard_signed_shell', 'direct/integer519', 'direct/integer519_centered'),
        ('architecture/derived16_shell/raw', 'direct/derived16_signed_shell', 'direct/derived16_factored_shell', 'direct/derived16_centered_shell')]:
        eq = get(factored+'/equation.json')
        dst = get(final+'/equation.json')
        result = dict(path=final, power_interfaces=interfaces(get(raw+'/raw_audit_input.json')))
        result['projection'] = projection(get(factored+'/factored_source.json'), eq, get(factored+'/projection_certificate.json'))
        result['translation'] = translation(eq, dst, get(final+'/translation_certificate.json'))
        result['uncentered_census'] = census(eq, get(factored+'/expanded_polynomial.json'))
        result['final_census'] = census(dst, get(final+'/expanded_polynomial.json'))
        for mutation in ['quartic coefficient', 'quadratic residual', 'inverse polynomial', 'translation shift', 'actual power output sign', 'actual seed-slack cut']:
            try:
                if mutation == 'quartic coefficient':
                    bad = get(final+'/expanded_polynomial.json')
                    bad['terms'][0][0] += 1
                    census(dst, bad)
                elif mutation == 'quadratic residual':
                    bad = copy.deepcopy(dst)
                    bad['residuals'][0]['terms'][0][0] += 1
                    census(bad, get(final+'/expanded_polynomial.json'))
                elif mutation == 'inverse polynomial':
                    bad = get(factored+'/projection_certificate.json')
                    bad['steps'][0]['restoration'][0][0] += 1
                    projection(get(factored+'/factored_source.json'), eq, bad)
                elif mutation == 'translation shift':
                    bad = get(final+'/translation_certificate.json')
                    bad['shifts'][0][1] += 1
                    translation(eq, dst, bad)
                else:
                    bad = get(raw+'/raw_audit_input.json')
                    label = 'pow0.power_congruence' if mutation == 'actual power output sign' else 'index0.index_at_most_Y'
                    row = next(r for r in bad['rows'] if r['label'] == label)
                    row['terms'][0][0] += 1
                    interfaces(bad)
            except (ValueError, StopIteration):
                rejected.append(dict(artifact=final, actual_data_mutation=mutation, rejected=True))
            else:
                raise ValueError('accepted actual-data corruption '+mutation)
        results.append(result)
    receipt = dict(status='PASS', optimized_python=bool(sys.flags.optimize), archive_sha256=ARCHIVE_SHA,
                   closed_release_members=len(members), direct_input_pins=len(get('direct/SOURCE_PINS.json')),
                   stale_runtime_zip_entries=missing, artifacts=results, incoming_code_imported_or_executed=False,
                   rejected_actual_data_corruptions=rejected,
                   ordinary_proof_replaced_by_finite_check=False, audit_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    data = json.dumps(receipt, indent=2, sort_keys=True)+'\n'
    if args.output.exists():
        need(args.output.read_text() == data, 'refuse changed audit receipt overwrite')
    else:
        args.output.write_text(data)
    print(json.dumps(dict(status='PASS', integer_endpoints=[r['final_census'] for r in results]), sort_keys=True))

if __name__ == '__main__':
    main()
