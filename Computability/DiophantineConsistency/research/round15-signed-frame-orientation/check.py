#!/usr/bin/env python3
"""Read-only, stdlib-only literal bindings for the JOINT Round15 F/A-sign proof.

No incoming module is imported or executed. The finite controls supplement the
unbounded ordinary argument in PROPOSAL.md; no projected equation is generated.
"""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = 'con-zfc-diophantine-forms/125-unified-binomial-round15/'
DIRECT = SOURCE + 'direct/unified_reparam_derived_shell/'
RAW = SOURCE + 'architecture/unified_derived_shell/raw/raw_audit_input.json'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def load(path):
    return json.loads(path.read_text())


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def poly(terms):
    answer = {}
    for coefficient, monomial in terms:
        key = tuple(sorted(monomial))
        answer[key] = answer.get(key, 0) + coefficient
    return {m: c for m, c in answer.items() if c}


def add(*items):
    result = {}
    for item in items:
        for m, c in item.items():
            result[m] = result.get(m, 0) + c
    return {m: c for m, c in result.items() if c}


def scale(p, coefficient):
    return {m: c * coefficient for m, c in p.items() if c * coefficient}


def mul(p, q):
    return poly([[c * d, list(m + n)] for m, c in p.items() for n, d in q.items()])


def v(index):
    return {(index,): 1}


ONE = {(): 1}


def sub(p, coordinate, replacement):
    result = {}
    for monomial, coefficient in p.items():
        term = {(): coefficient}
        for index in monomial:
            term = mul(term, replacement if index == coordinate else v(index))
        result = add(result, term)
    return result


def reduced(source, row_combination, definitions):
    result = add(*(scale(poly(source['residuals'][i]['terms']), c)
                   for i, c in row_combination))
    for row_index, coordinate in reversed(definitions):
        row = poly(source['residuals'][row_index]['terms'])
        need(row.get((coordinate,)) == 1, 'monic private definition')
        rhs = scale(add(row, scale(v(coordinate), -1)), -1)
        need(all(coordinate not in m for m in rhs), 'acyclic private definition')
        result = sub(result, coordinate, rhs)
    return result


def actual_cuts():
    A, W, Z, U, C, X, Y = v(246), v(245), add(v(247), ONE), v(250), add(v(255), ONE), v(257), v(258)
    F, B, V, slack, q, L, t = v(3), v(5), v(6), v(8), v(179), v(181), add(v(0), scale(ONE, 16))
    n = add(v(4), ONE)
    entries = [
        ('F_square', [[0, 1]], [], add(v(4), scale(mul(F, F), -1))),
        ('B_anchor', [[3, 1]], [], add(B, scale(v(7), -1), scale(slack, -1), scale(ONE, -1))),
        ('q_anchor', [[167, 1]], [], add(q, scale(B, -1), scale(v(185), -1), scale(ONE, -1))),
        ('L_anchor', [[166, 1]], [], add(L, scale(mul(q, v(183)), -1), scale(v(184), -1), scale(ONE, -2))),
        ('factorial_ceiling', [[3, 1], [2, -1]], [[1, 9]], add(mul(F, B), scale(V, -1), scale(slack, -1))),
        ('last_frame_norm', [[204, 1]], [[202, 248], [203, 249]],
         add(mul(A, A), scale(mul(mul(mul(mul(W, W), W), add(W, scale(ONE, 2))), mul(Z, Z)), -1), scale(ONE, -1))),
        ('common_norm', [[206, 1]], [[205, 254]],
         add(mul(U, U), scale(mul(add(mul(A, A), scale(ONE, -1)), mul(v(251), v(251))), -1), scale(ONE, -1))),
        ('comparison_base', [[207, 1]], [], add(v(255), scale(mul(v(251), add(v(252), ONE)), -4))),
        ('comparison_base_mod_U', [[209, 1]], [[208, 256]], add(C, scale(A, -1), scale(mul(U, v(253)), -1))),
        ('t_index_slack', [[210, 1]], [], add(Y, scale(t, -1), scale(v(261), -1))),
        ('t_main_norm', [[212, 1]], [[211, 262]], add(mul(X, X), scale(mul(add(mul(A, A), scale(ONE, -1)), mul(Y, Y)), -1), scale(ONE, -1))),
        ('t_comparison_norm', [[214, 1]], [[213, 263]], add(mul(v(259), v(259)), scale(mul(add(mul(C, C), scale(ONE, -1)), mul(v(260), v(260))), -1), scale(ONE, -1))),
        ('t_abscissa_congruence', [[216, 1]], [[215, 266]], add(v(259), scale(X, -1), scale(mul(U, v(264)), -1))),
        ('t_ordinate_congruence', [[218, 1]], [[217, 267]], add(v(260), scale(t, -1), scale(mul(Y, v(265)), -4))),
        ('F_power_modulus', [[221, 1]], [[219, 269], [220, 270]], add(scale(mul(A, n), 2), scale(mul(n, n), -1), scale(v(268), -1), scale(ONE, -1))),
        ('F_power_congruence', [[224, 1]], [[211, 262], [222, 272], [223, 273]], add(X, mul(add(n, scale(A, -1)), Y), scale(V, -1), scale(mul(v(268), v(271)), -1))),
        ('q_power_modulus', [[262, 1]], [[260, 314], [261, 315]], add(scale(mul(A, q), 2), scale(mul(q, q), -1), scale(v(313), -1), scale(ONE, -1))),
        ('q_power_congruence', [[265, 1]], [[211, 262], [263, 317], [264, 318]], add(X, mul(add(q, scale(A, -1)), Y), scale(L, -1), scale(mul(v(313), v(316)), -1))),
    ]
    ys = [258, 275, 297, 320, 342, 356, 370, 384, 398, 412, 426, 440, 454, 468, 482]
    product = ONE
    for index in ys:
        product = mul(product, v(index))
    entries.append(('common_squared_ordinate_product', [[434, 1]],
                    [[i, i + 77] for i in range(418, 433)] + [[433, 511]],
                    add(v(251), scale(mul(mul(product, product), add(v(510), ONE)), -1))))
    XK, YK, K, N = v(274), v(275), scale(v(25), 2), v(26)
    entries.extend([
        ('endpoint_after_F', [[7, 1]], [], add(v(2), scale(F, -1), scale(v(11), -1), scale(ONE, -1))),
        ('R_constructor', [[10, 1]], [], add(v(25), scale(ONE, -18), scale(v(0), -1), scale(v(1), -1), scale(v(2), -1), scale(F, -1))),
        ('K_index_slack', [[225, 1]], [], add(YK, scale(K, -1), scale(v(278), -1))),
        ('K_main_norm', [[227, 1]], [[226, 279]], add(mul(XK, XK), scale(mul(add(mul(A, A), scale(ONE, -1)), mul(YK, YK)), -1), scale(ONE, -1))),
        ('K_comparison_norm', [[229, 1]], [[228, 280]], add(mul(v(276), v(276)), scale(mul(add(mul(C, C), scale(ONE, -1)), mul(v(277), v(277))), -1), scale(ONE, -1))),
        ('K_abscissa_congruence', [[231, 1]], [[230, 283]], add(v(276), scale(XK, -1), scale(mul(U, v(281)), -1))),
        ('K_ordinate_congruence', [[233, 1]], [[232, 284]], add(v(277), scale(K, -1), scale(mul(YK, v(282)), -4))),
        ('B_power_modulus', [[236, 1]], [[234, 286], [235, 287]], add(scale(mul(A, B), 2), scale(mul(B, B), -1), scale(v(285), -1), scale(ONE, -1))),
        ('B_power_congruence', [[239, 1]], [[226, 279], [237, 289], [238, 290]], add(XK, mul(add(B, scale(A, -1)), YK), scale(N, -1), scale(mul(v(285), v(288)), -1))),
        ('N_square', [[158, 1]], [], add(v(175), scale(mul(N, N), -1))),
        ('N_power_modulus', [[241, 1]], [[158, 175], [240, 292]], add(scale(mul(A, N), 2), scale(mul(N, N), -1), scale(v(291), -1), scale(ONE, -1))),
        ('N_power_congruence', [[244, 1]], [[226, 279], [242, 294], [243, 295]], add(XK, mul(add(N, scale(A, -1)), YK), scale(q, -1), scale(mul(v(291), v(293)), -1))),
    ])
    return entries, ys


def signed_residue_identities():
    """Four universal H*J identities, with the actual t/K pairs and bases."""
    A = v(246)
    for n, X, Y in [(add(v(4), ONE), v(257), v(258)),
                    (v(179), v(257), v(258)),
                    (v(5), v(274), v(275)),
                    (v(26), v(274), v(275))]:
        dY = mul(add(n, scale(A, -1)), Y)
        H, J = add(X, dY), add(X, scale(dY, -1))
        T = add(scale(mul(A, n), 2), scale(mul(n, n), -1), scale(ONE, -1))
        norm = add(mul(X, X), scale(mul(add(mul(A, A), scale(ONE, -1)), mul(Y, Y)), -1), scale(ONE, -1))
        need(add(mul(H, J), scale(ONE, -1), scale(mul(T, mul(Y, Y)), -1)) == norm,
             'universal signed H/J norm identity')
    return 4


def signed_recurrence_controls():
    count = 0
    for A in [-11, -8, -5, 5, 8, 11]:
        for n in [-4, -2, -1, 1, 2, 4]:
            T = 2 * A * n - n * n - 1
            need(T != 0, 'finite nonzero signed modulus')
            x, y = 1, 0
            for k in range(1, 9):
                x, y = A * x + (A * A - 1) * y, x + A * y
                P = n ** k
                for epsilon, delta in [(1, 1), (-1, -1), (1, -1), (-1, 1)]:
                    m = epsilon * x + (n - A) * delta * y
                    residue = (m - P if (epsilon, delta) == (1, 1) else
                               m + P if (epsilon, delta) == (-1, -1) else
                               m * P - 1 if (epsilon, delta) == (1, -1) else m * P + 1)
                    need(residue % T == 0, 'finite signed-center/base quadrant recurrence')
                    count += 1
    return count


def verify(source, guarded, transform, raw, certificate):
    need((len(source['variables']), len(source['residuals'])) == (522, 446), 'whole fixed source shape')
    need(all(type(c) is int and len(m) <= 2 and all(type(i) is int and 0 <= i < 522 for i in m)
             for row in source['residuals'] for c, m in row['terms']), 'complete quadratic body uses only its fixed coordinates')
    names = {3: 'fact0.output', 5: 'choose0.output', 6: 'pow0.output',
             7: 'fact0.remainder', 8: 'fact0.slack', 179: 'pow2.output',
             181: 'pow4.output', 245: 'shared.W', 246: 'shared.A',
             250: 'shared_index.U', 251: 'shared_index.V',
             257: 'index0.X', 258: 'index0.Y', 261: 'index0.YminusK',
             26: 'pow1.output', 274: 'index1.X', 275: 'index1.Y', 278: 'index1.YminusK'}
    need(all(source['variables'][i]['name'] == name for i, name in names.items()), 'actual named semantic ports')
    need(guarded['variables'][:522] == source['variables'] and guarded['residuals'][:446] == source['residuals'], 'entire source body unchanged')
    need((len(guarded['variables']), len(guarded['residuals'])) == (636, 484), 'entire guard layout')
    need(certificate['body_coordinates'] == list(range(522)) and certificate['body_rows'] == list(range(446)), 'fixed entire body maps')
    guards = transform['guards']
    need(len(guards) == 38 and certificate['guard_predicates'] == guards, 'all literal guards bound')
    all_aux = set(range(522, 636))
    need([a for g in guards for a in g['auxiliary']] == list(range(522, 636)), 'disjoint exhaustive triples')
    for index, g in enumerate(guards):
        a, b, c = g['auxiliary']
        need(g['row'] == 446 + index, 'actual guard row')
        expression = poly(g['expression'])
        if g['kind'] == 'nonnegative':
            need(type(g['coordinate']) is int and 0 <= g['coordinate'] < 522
                 and expression == v(g['coordinate']), 'actual scalar sign target')
        elif g['kind'] == 'paired_interval':
            need(len(g['pair']) == 2 and len(set(g['pair'])) == 2
                 and all(type(i) is int and 0 <= i < 522 for i in g['pair'])
                 and expression == mul(v(g['pair'][0]), v(g['pair'][1])), 'actual individual pair product')
        else:
            need(g['kind'] == 'positive_common_V' and expression == add(v(251), scale(ONE, -1)), 'only strict common ordinate predicate')
        need(all(not all_aux.intersection(m) for m in expression), 'guard targets avoid auxiliary coordinates')
        need(guarded['residuals'][g['row']]['label'] == 'domain_guard.' + str(index), 'actual graph label')
        expected = add(expression, poly([[-1, [a, a]], [-1, [b, b]], [-1, [c, c]], [-1, [c]]]))
        need(poly(guarded['residuals'][g['row']]['terms']) == expected, 'entire Legendre graph')
        occurrences = {i for i, row in enumerate(guarded['residuals']) if any(set(m) & {a, b, c} for _, m in row['terms'])}
        need(occurrences == {g['row']}, 'guard triple has no escaping use')
    need(certificate['deleted_guards'] == [guards[2], guards[25]]
         and [g['coordinate'] for g in certificate['deleted_guards']] == [3, 246]
         and [g['auxiliary'] for g in certificate['deleted_guards']] == [[528, 529, 530], [597, 598, 599]], 'exact deleted F/A guards')
    retained = {g['coordinate'] for i, g in enumerate(guards) if i not in [2, 25] and g['kind'] == 'nonnegative'}
    need({0, 1, 7, 8, 11, 183, 184, 185, 247, 252, 261, 278} <= retained
         and not {3, 246} & retained, 'only retained pre-F/A scalar premises')
    need(guards[30]['kind'] == 'positive_common_V' and poly(guards[30]['expression']) == add(v(251), scale(ONE, -1)), 'retained strict common ordinate')
    cuts, ys = actual_cuts()
    expected_cuts = []
    for name, rows, definitions, target in cuts:
        need(reduced(source, rows, definitions) == target, 'actual ideal: ' + name)
        expected_cuts.append(dict(name=name, rows=rows, definitions=definitions, target=[[c, list(m)] for m, c in sorted(target.items())]))
    need(certificate['identities'] == expected_cuts and certificate['seed_ordinates'] == ys, 'whole literal cut certificate')
    budget = transform['square_budget']
    atoms = {tuple(entry['token']): poly(entry['affine']) for entry in budget['atoms']}
    need(len(atoms) == 37 == len(budget['atoms']), '37 distinct frame atoms')
    tokens = {tuple(call[key]) for call in raw['powers'] for key in ['base', 'exponent', 'output']}
    need(tokens == set(atoms) and len(raw['powers']) == 18, 'all original power atoms covered')
    calls = [{key: [[c, list(m)] for m, c in sorted(atoms[tuple(call[key])].items())]
              for key in ['base', 'exponent', 'output']} for call in raw['powers']]
    need(all(all(poly(a[k]) == poly(b[k]) for k in a) for a, b in zip(calls, budget['power_calls'])) and len(budget['power_calls']) == 18, 'all18 affine power interfaces')
    need(certificate['power_calls'] == budget['power_calls'] and certificate['frame_atoms'] == budget['atoms'], 'complete affine interface certificate')
    frame = add(v(245), scale(ONE, -4), *(scale(mul(a, a), -2) for a in atoms.values()))
    need(poly(source['residuals'][445]['terms']) == frame and budget['frame_row'] == 445 and transform['frame_factor'] == 2, 'entire signed square frame')
    expected = {0: dict(base=[[1, []], [1, [4]]], exponent=[[16, []], [1, [0]]], output=[[1, [6]]]),
                4: dict(base=[[1, [179]]], exponent=[[16, []], [1, [0]]], output=[[1, [181]]]),
                1: dict(base=[[1, [5]]], exponent=[[2, [25]]], output=[[1, [26]]]),
                2: dict(base=[[1, [26]]], exponent=[[2, [25]]], output=[[1, [179]]])}
    need(all(calls[i] == entry for i, entry in expected.items()), 'all four actual t and shared K requests')
    need(transform['undoubled_seed_exponents'] == [['v', 1], ['v', 54]], 't remains undoubled')
    need(certificate['premise_order'] == ['retained_anchors', 'signed_square_frame_abs_A', 'common_nonzero_ordinate',
                                        't_absolute_index_only', 'signed_t_q_support', 'F_squared_base_power', 'F_positive',
                                        'K_positive_even', 'K_absolute_index', 'two_shared_K_requests',
                                        'negative_A_contradiction', 'A_positive', 'fresh_deleted_guard_witnesses'], 'joint acyclic theorem interface')
    need(certificate['witness_maps'] == dict(
        forward=dict(fixed_body=list(range(522)), discard_guard_rows=[448, 471], discard_auxiliary=[528, 529, 530, 597, 598, 599]),
        backward=dict(fixed_body=list(range(522)), restore_guard_rows=[448, 471],
                      fresh_auxiliary=[528, 529, 530, 597, 598, 599], theorem='Legendre representations of F>=1 and A>=2'),
        retained_guard_rows=[446 + i for i in range(38) if i not in [2, 25]]), 'both joint fixed-body witness maps')
    signed = signed_residue_identities()
    return dict(source_and_frame_identities=len(cuts) + 1, universal_signed_norm_identities=signed,
                guard_graphs=38, frame_atoms=37, power_interfaces=18, seed_ordinates=15,
                retained_predicates=36, body_variables=522, body_rows=446)


def controls(data, cert):
    trials = []
    for index in [0, 1, 2, 3, 7, 10, 158, 166, 167, 202, 203, 204, 206, 207, 209, 210, 212, 214, 216, 218, 221, 224,
                  225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244,
                  262, 265, 432, 434, 445]:
        copy = deepcopy(data)
        copy[0]['residuals'][index]['terms'].append([1, []])
        copy[1]['residuals'][index] = deepcopy(copy[0]['residuals'][index])
        trials.append(('source_row_' + str(index), copy, cert))
    copy = deepcopy(data)
    copy[0]['residuals'][100]['terms'].append([1, [528]])
    copy[1]['residuals'][100] = deepcopy(copy[0]['residuals'][100])
    trials.append(('deleted_auxiliary_escape', copy, cert))
    copy = deepcopy(data)
    copy[0]['residuals'][100]['terms'].append([1, [597]])
    copy[1]['residuals'][100] = deepcopy(copy[0]['residuals'][100])
    trials.append(('deleted_A_auxiliary_escape', copy, cert))
    copy = deepcopy(data); copy[1]['residuals'][448]['terms'].append([1, []])
    trials.append(('deleted_guard_graph', copy, cert))
    copy = deepcopy(data); copy[1]['residuals'][471]['terms'].append([1, []])
    trials.append(('deleted_A_guard_graph', copy, cert))
    copy = deepcopy(data); copy[2]['square_budget']['atoms'].pop()
    trials.append(('missing_frame_atom', copy, cert))
    copy = deepcopy(data); copy[3]['powers'][4]['exponent'] = ['v', 54]
    trials.append(('support_wrong_index', copy, cert))
    copy = deepcopy(data)
    for term in copy[0]['residuals'][242]['terms']:
        if term == [-1, [26, 275]]:
            term[1] = [26, 258]
    copy[1]['residuals'][242] = deepcopy(copy[0]['residuals'][242])
    trials.append(('second_K_request_wrong_pair', copy, cert))
    copy = deepcopy(data); copy[3]['powers'][2]['exponent'] = ['v', 1]
    trials.append(('second_K_request_wrong_exponent', copy, cert))
    copy = deepcopy(data); altered = deepcopy(cert)
    copy[2]['guards'][3]['coordinate'] = 3
    altered['guard_predicates'][3]['coordinate'] = 3
    trials.append(('false_scalar_target_metadata', copy, altered))
    bad = deepcopy(cert); bad['premise_order'].insert(0, 'all_seed_indices_positive')
    trials.append(('circular_all_seed_premise', data, bad))
    bad = deepcopy(cert); bad['premise_order'].insert(0, 'invoke_F_only_theorem_without_A_guard')
    trials.append(('invalid_F_only_composition', data, bad))
    rejected = []
    for name, altered, certificate in trials:
        try:
            verify(*altered, certificate)
        except ValueError as error:
            rejected.append(dict(name=name, reason=str(error)))
        else:
            raise ValueError('corruption accepted: ' + name)
    return rejected


def main():
    parser = argparse.ArgumentParser(); parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pins = load(HERE / 'SOURCE_PINS.json')
    for name, expected in pins['external_files'].items():
        need(digest(ROOT / name) == expected, 'authenticated external file: ' + name)
    for name, expected in pins['core_files'].items():
        need(digest(HERE / name) == expected, 'authenticated own core: ' + name)
    data = [load(ROOT / (DIRECT + name)) for name in ['source.json', 'guarded.json', 'transform_certificate.json']]
    data.append(load(ROOT / RAW))
    cert = load(HERE / 'CERTIFICATE.json')
    result = verify(*data, cert)
    recurrence_controls = signed_recurrence_controls()
    rejected = controls(data, cert)
    manifest = HERE / 'MANIFEST.json'
    if manifest.exists():
        inventory = load(manifest)['files']
        actual = {str(p.relative_to(HERE)): digest(p) for p in HERE.rglob('*') if p.is_file() and p != manifest}
        need(actual == inventory, 'closed inventory including nested manifests')
    report = dict(status='PASS', optimized=not __debug__, source_pins_sha256=digest(HERE / 'SOURCE_PINS.json'),
                  scope='ordinary JOINT F/A fixed-body guard-existence theorem and literal interfaces only',
                  incoming_code_imported_or_executed=False, projected_equation_generated=False,
                  literal=result, actual_corruptions=rejected, signed_recurrence_controls=recurrence_controls,
                  unbounded_proof='PROPOSAL.md; signed-center/base argument and inherited indexed-Pell lemmas explicitly retained')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps(dict(status='PASS', source_and_frame_identities=result['source_and_frame_identities'],
                          signed_norm_identities=result['universal_signed_norm_identities'],
                          actual_corruptions=len(rejected)), sort_keys=True))


if __name__ == '__main__':
    main()
