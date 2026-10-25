#!/usr/bin/env python3
"""Independent finite audit of the new horizon source and terminal deletion.

This file imports no producer, transform, or predecessor checker module.
It uses exact integer sparse-polynomial arithmetic. It does not claim to
check the mathematical Pell theorem, the intermediate affine lineage, or
the logical C222/ZFC calibration; those are separate obligations.
"""
from collections import defaultdict
import argparse
import hashlib
import json
from pathlib import Path
import zipfile

WORK = Path(__file__).resolve().parent.parent
ARCHIVE = WORK / 'provenance/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25.zip'
PREFIX = 'ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/direct/'
NEW = WORK / 'stages/horizon'


def require(value, why):
    if not value:
        raise ValueError(why)


def plus(*polys):
    out = defaultdict(int)
    for p in polys:
        for mon, value in p.items():
            out[mon] += value
    return {mon: value for mon, value in out.items() if value}


def times(p, q):
    out = defaultdict(int)
    for mon, value in p.items():
        for mon2, value2 in q.items():
            out[tuple(sorted(mon + mon2))] += value * value2
    return {mon: value for mon, value in out.items() if value}


def neg(p):
    return {mon: -value for mon, value in p.items()}


def scalar(c):
    return {(): c} if c else {}


def variable(i):
    return {(i,): 1}


def scale(c, p):
    return times(scalar(c), p)


def square(p):
    return times(p, p)


def polynomial(terms):
    return plus(*({tuple(sorted(mon)): value} for value, mon in terms))


def sub(p, i, replacement):
    out = {}
    for mon, value in p.items():
        term = scalar(value)
        for j in mon:
            term = times(term, replacement if j == i else variable(j))
        out = plus(out, term)
    return out


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, default=ARCHIVE)
    parser.add_argument('--source-root', type=Path, default=NEW)
    parser.add_argument('--principal-d-input', type=Path,
                        default=WORK / 'equations/horizon238/source_equation.json')
    parser.add_argument('--companion-d-input', type=Path,
                        default=WORK / 'equations/horizon237/source_equation.json')
    parser.add_argument('--output', type=Path,
                        default=WORK / 'verification/HORIZON_LITERAL_BINDING_AUDIT.json')
    args = parser.parse_args()
    source_root = args.source_root
    archive_sha = sha(args.archive)
    require(archive_sha == '38dfec4f7db8ba4af921fe101714da6a569a3afce1d916325eb550160372c913',
            'unexpected predecessor archive')
    with zipfile.ZipFile(args.archive) as z:
        old = json.loads(z.read(PREFIX + 'factorial_free_affine/raw_source.json'))
    new = read(source_root / 'raw_source.json')
    require(set(old) == set(new), 'raw top-level key change')
    for k in old:
        if k != 'residuals':
            require(old[k] == new[k], 'unexpected raw metadata change: ' + k)
    require(len(old['residuals']) == len(new['residuals']), 'raw row count changed')
    names = {v['name']: i for i, v in enumerate(new['variables'])}
    require(len(names) == len(new['variables']), 'duplicate coordinate name')
    def v(name):
        return variable(names[name])
    labels = defaultdict(list)
    for i, r in enumerate(new['residuals']):
        labels[r['label']].append(i)
    def row(label):
        require(len(labels[label]) == 1, 'nonunique residual: ' + label)
        return polynomial(new['residuals'][labels[label][0]]['terms'])
    t = plus(v('t0'), scalar(16))
    d = v('growth.power_base')
    f = v('crt.growth_majorant_F')
    q = v('pow2.output')
    s = v('beta.odd_square_multiplier')
    zeta = v('radix.odd_square_root_half')
    beta_half = v('beta.odd_square_root_half')
    h = names['cofinal.horizon_root']
    changes_expected = {
        'cofinal.horizon': (
            plus(v('t0'), neg(square(v('cofinal.horizon_root')))), {}),
        'growth.base_definition': (
            plus(d, scale(-2, t), scalar(-2)),
            plus(d, scale(-(1 << 26), plus(scale(2, t), scalar(1))))),
        'radix.odd_square': (
            plus(q, neg(square(plus(scale(2, zeta), scalar(1))))),
            plus(q, scale(-4, zeta), scalar(-1))),
        'beta.odd_square_multiplier': (
            plus(s, neg(square(plus(scale(2, beta_half), scalar(1))))),
            plus(s, scale(-2, beta_half), scalar(-1))),
    }
    differences = []
    for i, (a, b) in enumerate(zip(old['residuals'], new['residuals'])):
        require(set(a) == set(b), 'row metadata key change')
        require({k: val for k, val in a.items() if k != 'terms'} ==
                {k: val for k, val in b.items() if k != 'terms'},
                'row metadata change')
        if a != b:
            require(a['label'] in changes_expected, 'unexpected changed row')
            before, after = changes_expected[a['label']]
            require(polynomial(a['terms']) == before, 'old mutation target mismatch')
            require(polynomial(b['terms']) == after, 'new mutation target mismatch')
            differences.append({'row': i, 'label': a['label']})
    require({e['label'] for e in differences} == set(changes_expected), 'missing changed row')
    require(len(differences) == 4, 'mutation census')
    old_horizon_support = [i for i, r in enumerate(old['residuals'])
                           if any(h in mon for mon in polynomial(r['terms']))]
    require(old_horizon_support == labels['cofinal.horizon'], 'old root not private')
    require(not any(h in mon for r in new['residuals'] for mon in polynomial(r['terms'])),
            'horizon root remains in new raw source')
    require(row('bootstrap.beta_base_square_product') ==
            plus(v('y'), neg(times(f, s))), 'beta product changed')

    x, radius, b, bh, a = [v(name) for name in
                          ('x', 'mul.1', 'choose0.output', 'self_radix.BH', 'shared.A')]
    reps = [plus(variable(i), scalar(1)) for i in range(16, 25)]
    anchor = plus(v('add.380'), scalar(1))
    require(row('self_radix.base_definition') ==
            plus(bh, neg(times(b, plus(scalar(2), *reps)))), 'self-radix base')
    numer = plus(q, scalar(1))
    # Independent semantic request list; this is not read from a certificate.
    requests = [
        (d, t, f, 'index0', 0),
        (b, x, v('pow1.output'), 'index12', 1),
        (bh, x, q, 'index12', 2),
        (numer, plus(radius, t), v('pow3.output'), 'index2', 3),
        (q, t, v('pow4.output'), 'index0', 4),
        (numer, reps[0], v('pow5.output'), 'index3', 3),
        (q, plus(t, scalar(1)), v('pow6.output'), None, 4),
        (numer, reps[1], v('pow7.output'), 'index5', 3),
        (numer, reps[2], v('pow8.output'), 'index6', 3),
        (numer, reps[3], v('pow9.output'), 'index7', 3),
        (numer, reps[4], v('pow10.output'), 'index8', 3),
        (q, plus(v('y'), scalar(1)), v('pow11.output'), 'index9', 4),
        (numer, reps[5], v('pow12.output'), 'index10', 3),
        (numer, reps[6], v('pow13.output'), 'index11', 3),
        (q, x, v('pow14.output'), 'index12', 4),
        (numer, reps[7], v('pow15.output'), 'index13', 3),
        (numer, reps[8], v('pow16.output'), 'index14', 3),
        (numer, anchor, v('pow17.output'), 'index15', 3),
    ]
    atoms = {tuple(sorted(p.items())): p for n, k, m, _, _ in requests for p in (n, k, m)}
    require(row('shared.frame_definition') ==
            plus(v('shared.W'), scalar(-2), *(neg(square(p)) for p in atoms.values())),
            'complete actual-base/index/output square frame')

    # Small gate unfolding, stopping at actual power atoms and A.
    stop = {j for p in atoms.values() for mon in p for j in mon}
    stop.add(names['shared.A'])
    gates = {}
    for i in labels['multiplication']:
        p = polynomial(new['residuals'][i]['terms'])
        outputs = [mon[0] for mon, c in p.items()
                   if len(mon) == 1 and c == 1 and new['variables'][mon[0]]['kind'] == 'gate']
        require(len(outputs) == 1, 'nonfunctional multiplication row')
        output = outputs[0]
        require(output not in gates and all(output not in mon for mon in p if mon != (output,)),
                'nonfunctional multiplication output')
        gates[output] = plus(variable(output), neg(p))
    gates[names['index_addition.D']] = plus(square(a), scalar(-1))
    def expand(p, active=()):
        out = {}
        for mon, c in p.items():
            term = scalar(c)
            for j in mon:
                if j in gates and j not in stop:
                    require(j not in active, 'cyclic gate')
                    term = times(term, expand(gates[j], active + (j,)))
                else:
                    term = times(term, variable(j))
            out = plus(out, term)
        return out
    require(not expand(row('index_addition.D_definition')), 'derived Pell D identity')
    pairs = {}
    for _, k, _, prefix, _ in requests:
        if prefix is not None:
            require(prefix not in pairs or pairs[prefix] == k, 'principal index inconsistency')
            pairs[prefix] = k
    pooled = {}
    for prefix, k in pairs.items():
        xp, yp = v(prefix + '.X'), v(prefix + '.Y')
        norm = plus(square(xp), square(yp), neg(times(square(a), square(yp))), scalar(-1))
        require(expand(row(prefix + '.norm1')) == norm, 'principal Pell norm')
        pooled = plus(pooled, square(plus(xp, scalar(-1))), square(plus(yp, neg(k))))
    pooled = plus(pooled, neg(times(plus(a, scalar(-1)), v('cap.pooled_quotient'))))
    require(row('cap.pooled_index_residue') == pooled, 'actual indices in pooled orientation')
    for i, base in enumerate((d, b, bh, numer, q)):
        expected = plus(scale(2, times(a, base)), neg(square(base)), scalar(-1), neg(v(f'base{i}.T')))
        require(expand(row(f'base{i}.T_definition')) == expected, 'actual base modulus')
    for i, (base, k, output, prefix, modulus) in enumerate(requests):
        if prefix is None:
            xp = plus(times(a, v('index0.X')), times(plus(square(a), scalar(-1)), v('index0.Y')))
            yp = plus(v('index0.X'), times(a, v('index0.Y')))
        else:
            xp, yp = v(prefix + '.X'), v(prefix + '.Y')
        expected = plus(xp, neg(times(a, yp)), times(base, yp), neg(output),
                        neg(times(v(f'base{modulus}.T'), v(f'pow{i}.quotient'))))
        require(expand(row(f'pow{i}.power_congruence')) == expected, 'actual power request')

    terminal = {}
    for profile in ('principal', 'companion'):
        directory = source_root / profile
        source = read(directory / 'mutated_source.json')
        cert = read(directory / 'final_certificate.json')
        final = read(directory / 'equation.json')
        ps = [polynomial(r['terms']) for r in source['residuals']]
        removed = []
        deleted = []
        for pivot in cert['pivots']:
            i, j = pivot['variable'], pivot['row']
            replacement = polynomial(pivot['replacement'])
            require(ps[j].get((i,)) == 1, 'nonmonic terminal pivot')
            require(all(i not in mon for mon in ps[j] if mon != (i,)), 'nonlinear terminal pivot')
            require(plus(variable(i), neg(ps[j])) == replacement, 'incorrect terminal restoration')
            ps = [sub(p, i, replacement) for p in ps]
            require(not ps[j], 'pivot not zero after replacement')
            removed.append(i)
            deleted.append(j)
        hidx = cert['unconstrained_removed']
        hrow = cert['deleted_zero_row']
        require(source['variables'][hidx]['name'] == 'cofinal.horizon_root', 'wrong private coordinate removed')
        require(source['residuals'][hrow]['label'] == 'cofinal.horizon', 'wrong zero row removed')
        require(not ps[hrow] and not any(hidx in mon for p in ps for mon in p), 'root not private and free')
        removed.append(hidx)
        deleted.append(hrow)
        keepv = [i for i in range(len(source['variables'])) if i not in removed]
        keepr = [i for i in range(len(ps)) if i not in deleted]
        require(keepv == cert['retained_original_variables'], 'unexpected variable deletion')
        require(keepr == cert['retained_original_rows'], 'unexpected residual deletion')
        require(final['variables'] == [source['variables'][i] for i in keepv], 'final variable remap')
        renumber = {old: new for new, old in enumerate(keepv)}
        require(len(final['residuals']) == len(keepr), 'final row count')
        for newrow, oldrow in zip(final['residuals'], keepr):
            require(newrow['label'] == source['residuals'][oldrow]['label'], 'residual label remap')
            expected = {tuple(renumber[i] for i in mon): c for mon, c in ps[oldrow].items()}
            require(polynomial(newrow['terms']) == expected, 'terminal substituted residual differs')
        next_source = args.principal_d_input if profile == 'principal' else args.companion_d_input
        require(read(next_source) == final, 'D contraction uses different input')
        final_names = {entry['name'] for entry in final['variables']}
        require('cofinal.horizon_root' not in final_names, 'horizon coordinate still counted')
        terminal[profile] = {
            'verified_before_D_variables': len(final['variables']),
            'verified_before_D_residuals': len(final['residuals']),
            'deleted_source_coordinate': hidx,
            'deleted_source_row': hrow,
            'equation_sha256': sha(directory / 'equation.json'),
            'D_input_identical': True,
        }
    result = {
        'status': 'passed',
        'predecessor_archive_sha256': archive_sha,
        'new_raw_source_sha256': sha(source_root / 'raw_source.json'),
        'exact_raw_changed_rows': differences,
        'all_other_raw_rows_and_metadata_identical': True,
        'actual_t': 't0 + 16',
        'actual_growth_base': '2^26 * (2*(t0+16)+1)',
        'raw_growth_base_coordinate': names['growth.power_base'],
        'raw_horizon_coordinate': h,
        'distinct_actual_frame_atoms': len(atoms),
        'power_requests_checked': len(requests),
        'principal_pairs_checked': len(pairs),
        'base_moduli_checked': 5,
        'horizon_root_private_before_and_absent_after': True,
        'terminal_deletions': terminal,
        'producer_or_predecessor_checker_imports': False,
        'scope': 'Raw semantic binding, unchanged metadata, actual signed power/frame identities, terminal affine and private-root deletion. Intermediate lineage, D contraction, mathematical proofs and logical calibration are separate.',
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
