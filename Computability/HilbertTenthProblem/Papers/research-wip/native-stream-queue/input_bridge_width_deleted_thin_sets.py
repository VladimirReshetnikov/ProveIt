"""Promise decision theorem for the literal width-deleted source and affine carry."""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import hashlib
import json
from pathlib import Path

import sympy as sp
import input_bridge_width_descent as width
import pell_kernel_width_deleted_classification as classification


def controller_source():
    base = width.deletion_source()
    extra = [
        ['thin_weight0', '*', 'weight0', 'F0'],
        ['thin_weight1', '*', 'weight1', 'F1'],
        ['thin_weight2', '*', 'weight2', 'F2'],
        ['thin_weight3', '*', 'weight3', 'F3'],
        ['thin_sum01', '+', 'thin_weight0', 'thin_weight1'],
        ['thin_sum23', '+', 'thin_weight2', 'thin_weight3'],
        ['thin_sum', '+', 'thin_sum01', 'thin_sum23'],
        ['thin_offset', '*', 'lambda', 'twice_H'],
        ['thin_left', '+', 'thin_sum', 'thin_offset'],
    ]
    names = base['positive_parameters'] + base['positive_auxiliaries']
    constants = ['weight0', 'weight1', 'weight2', 'weight3', 'lambda', 'delta']
    z = {name: sp.Symbol(name) for name in names+constants}
    schedule = base['instructions']+extra
    env = width.prior.selector.execute(schedule, z)
    polynomial = sum(z[f'weight{i}']*z[f'F{i}'] for i in range(4))
    polynomial += z['lambda']*(z['q']-1)-z['delta']
    assert sp.expand(env['thin_left']-z['delta']-polynomial) == 0
    counts = Counter(row[1] for row in schedule)
    assert len(schedule) == 71 and counts['*'] == 38 and counts['+']+counts['-'] == 33
    return dict(operations=71, multiplications=38, additions_subtractions=33,
                equations=15, positive_existentials_excluding_x=25,
                added_instructions=extra, added_equality=['thin_left', 'delta'],
                controller_source=str(polynomial),
                fixed_integer_numerals=constants,
                source_scope='Literal62 width-deleted source plus the full affine equality; not universal')


def controller_passes(fields, q, coefficients, lam, delta):
    return sum(c*F for c, F in zip(coefficients, fields))+lam*(q-1) == delta


@lru_cache(maxsize=None)
def exceptional_candidates(q):
    """Exhaust the finite positive joint bound; no Pell coordinates searched."""
    t, power = 0, 1
    while power < q:
        power *= 3
        t += 1
    assert power == q and t >= 2
    result = []
    for fields in width.prior.fields_with_joint_bound(q):
        r = sum(F*q**j for j, F in enumerate(fields))
        if r % 2:
            continue
        kind = classification.stratum(fields, t)
        if kind not in ('long1', 'long2', 'long3'):
            continue
        assert classification.valuation(r) == 4*t
        A, D = sum(fields[:2])-q+1, sum(fields[2:])-q+1
        result.append((fields, r, A, D, kind))
    return tuple(result)


def finite_exception_decide(x, coefficients, lam, delta):
    q = 9
    while q < 18*x:
        for fields, r, A, D, kind in exceptional_candidates(q):
            if not controller_passes(fields, q, coefficients, lam, delta):
                continue
            W = 1
            while W <= q:
                if D == 6*x+W*A:
                    assert A+D < q and A != 0
                    assert (A < 0 and q < 6*x) or (kind == 'long3' and W == 1 and q < 18*x)
                    return dict(q=q, W=W, fields=list(fields), r=r, A=A, D=D, stratum=kind)
                W *= 3
        q *= 3
    return None


def decide_under_power_promise(x, coefficients, lam, delta):
    """Always halts/sound on YES; complete if the represented set is powers-of-two-only."""
    assert isinstance(x, int) and x > 0 and len(coefficients) == 4
    assert all(isinstance(c, int) for c in (*coefficients, lam, delta))
    exceptional = finite_exception_decide(x, coefficients, lam, delta)
    if exceptional is not None:
        return dict(accepted=True, branch='finite_nonnative', witness=exceptional)
    h, cs, cf = sum(coefficients)+2*lam, -delta, 0
    for W in (1, 3, 9):
        native = width.fixed_width_decide(x, W, coefficients, h, cs, cf)
        if native['accepted']:
            return dict(accepted=True, branch='fixed_width_native', W=W, reachability=native)
    return dict(accepted=False, branch='no_finite_or_small_width_witness')


def descent_checks():
    x, W, A, D = sp.symbols('x W A D')
    xs = [x+(W-W/3**j)*A/6 for j in range(3)]
    assert sp.expand(xs[0]-4*xs[1]+3*xs[2]) == 0
    for j in range(3):
        assert sp.expand(6*xs[j]+W*A/3**j-(6*x+W*A)) == 0
    powers = [2**j for j in range(25)]
    power_triples = 0
    for a, b, c in combinations(powers, 3):
        assert a-4*b+3*c != 0
        power_triples += 1
    family = []
    for m in range(3, 9):
        W, q = 3**m, 3**(m+1)
        H = (q-1)//2
        x, A, D = 1, 1, W+6
        read0 = read1 = 0
        value, scale = D, 1
        while value:
            digit = value % 3
            read0 += (digit >= 1)*scale
            read1 += (digit == 2)*scale
            value //= 3
            scale *= 3
        fields = [H+1, H, H+read0, H+read1]
        rows = []
        for j in range(3):
            small = W//3**j
            new_x = x+(W-small)*A//6
            assert (W-small)*A % 6 == 0
            rows.append(width.fixture(fields, new_x, small, q)['positive_outer_values'])
        assert rows[0]['x'] < rows[1]['x'] < rows[2]['x']
        assert rows[0]['x']-4*rows[1]['x']+3*rows[2]['x'] == 0
        family.append(dict(m=m, q=q, fields=fields,
                           widths=[row['W'] for row in rows], inputs=[row['x'] for row in rows],
                           kernel_coordinates_unchanged=True))
    return dict(symbolic_affine_relation='x0-4*x1+3*x2=0',
                finite_power_triple_checks=power_triples,
                full_positive_native_families=family,
                scope='Universal no-three-powers argument is the elementary 2-adic proof in the note')


def decision_checks():
    programs = [((0, 0, 0, 0), 0, 0),
                ((0, 0, 0, 0), 0, 1),
                ((1, -1, 1, -1), 0, 0),
                ((2, 1, -1, -2), 1, 1)]
    records = []
    for coefficients, lam, delta in programs:
        for x in range(1, 5):
            result = decide_under_power_promise(x, coefficients, lam, delta)
            if coefficients == (0, 0, 0, 0) and lam == 0 and delta == 1:
                assert not result['accepted']
            records.append(dict(coefficients=list(coefficients), lam=lam, delta=delta, x=x, result=result))
    # Independent bounded projection audit of every admitted exceptional tuple.
    exception_width_cases = 0
    controller_cases = 0
    strata = Counter()
    for q in (9, 27):
        for fields, r, A, D, kind in exceptional_candidates(q):
            W = 1
            while W <= q:
                I = D-W*A
                if I >= 6 and I % 6 == 0:
                    x = I//6
                    assert q < 18*x
                    exception_width_cases += 1
                    strata[kind] += 1
                    for coefficients, lam, delta in programs:
                        direct = controller_passes(fields, q, coefficients, lam, delta)
                        if direct:
                            found = finite_exception_decide(x, coefficients, lam, delta)
                            assert found is not None
                        controller_cases += 1
                W *= 3
    return dict(decision_runs=len(records), records=records,
                bounded_exception_width_cases=exception_width_cases,
                bounded_controller_checks=controller_cases, strata=dict(strata),
                exceptional_field_counts={str(q): len(exceptional_candidates(q)) for q in (9, 27)},
                scope='Decision implementation and finite exceptional projection checks; no arbitrary tested program is assumed powers-of-two-only')


def verify():
    dependencies = [Path(width.__file__), Path(classification.__file__)]
    return dict(status='PASS_WIDTH_DELETED_POWERS_OF_TWO_DECISION_OBSTRUCTION',
                source=controller_source(), descent=descent_checks(), decision=decision_checks(),
                dependency_sha256={p.name: hashlib.sha256(p.read_bytes().replace(b'\r\n', b'\n')).hexdigest()
                                   for p in dependencies},
                theorem='If this fixed affine-controller source represents a subset of positive powers of two, that set is decidable',
                scope='Nonuniversality of this precise width-deleted family; no improved complete universal bound',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(json.dumps(dict(status=result['status'], source_operations=result['source']['operations'],
                         decision_runs=result['decision']['decision_runs'],
                         exception_width_cases=result['decision']['bounded_exception_width_cases'],
                         scope=result['scope']), indent=2))
