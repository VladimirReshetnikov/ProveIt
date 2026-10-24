#!/usr/bin/env python3
"""Independent exact sign, integer restoration, interface and coefficient checks."""
import argparse
import ast
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import re
import sys
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from review_quartics407888 import raw_export
from review_synchronized_certificates import decode, add_term, full_sos


def need(ok, message):
    if not ok:
        raise ValueError(message)


def load(name):
    return json.loads((HERE / name).read_text())


def digest(data):
    return sha256(data).hexdigest()


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def multiply(a, b):
    out = {}
    for m, c in a.items():
        for n, d in b.items():
            add_term(out, tuple(sorted(m + n)), c * d)
    return out


def negative(p):
    return {m: -c for m, c in p.items()}


def inferred_step(parent, step, known):
    v, c = step['variable'], step['coefficient']
    need(type(c) is int and c > 0 and v not in known, 'fresh positive sign pivot')
    rhs = decode(step['rhs'])
    need(all(v not in m for m in rhs), 'sign pivot independent of its right side')
    expected = {(v,): c}
    for m, d in rhs.items():
        add_term(expected, m, -d)
    actual = decode(parent['residuals'][step['row']]['terms'])
    need(actual == expected or actual == negative(expected), 'entire actual sign-row identity')
    if step['kind'] == 'affine_square':
        root = decode(step['square_root'])
        need(all(len(m) <= 1 for m in root) and multiply(root, root) == rhs,
             'entire affine-square identity')
        dependencies = set()
    else:
        need(step['kind'] == 'positive_monomials' and all(d > 0 for d in rhs.values()),
             'nonnegative polynomial coefficients')
        dependencies = {i for m in rhs for i, power in Counter(m).items() if power % 2}
    need(sorted(dependencies) == step['dependencies'] and dependencies <= known,
         'all actual odd-power dependencies already nonnegative')
    known.add(v)


def sign_certificate(parent, sign):
    variables = parent['variables']
    need(sign['parent_sha256'] == digest(canonical(parent)), 'whole667 sign binding')
    guards = sign['guards']
    need(guards == sorted(set(guards)) and len(guards) == 109, 'exact109 retained guards')
    known = set(guards)
    for step in sign['proof_steps']:
        inferred_step(parent, step, known)
    need(sign['known_after_ordinary_steps'] == sorted(known) and len(known) == 533,
         'complete initial533-coordinate sign closure')
    categories = sign['unresolved']
    pieces = [set(categories[k]) for k in ['quotients', 'comparison_coordinates', 'private_products']]
    need(all(not (a & b) for j, a in enumerate(pieces) for b in pieces[:j]), 'disjoint unresolved roles')
    need(set.union(*pieces) == set(range(667)) - known, 'every remaining sign accounted for')
    need(sign['removed_guards'] == sorted(pieces[0]) and len(pieces[0]) == 52,
         'exact52 quotient boundary')
    need(len(pieces[1]) == 30 and len(pieces[2]) == 52, 'exact signed private closure')
    need(all(re.fullmatch(r'index\d+\.(S|R)', variables[i]['name']) for i in pieces[1]),
         'comparison coordinate metadata')
    need(all(variables[i]['kind'] == 'gate' for i in pieces[2]), 'private products are actual gates')
    late = set(sign['late_semantic_quotients'])
    need(late == {i for i in pieces[0] if re.fullmatch(
        r'pow\d+\.quotient|shared_index\.Bquotient', variables[i]['name'])} and len(late) == 22,
        'only separately proved orientation results enter the late stage')
    late_known = known | late
    for step in sign['late_proof_steps']:
        inferred_step(parent, step, late_known)
    need(sign['known_after_late_quotients'] == sorted(late_known) and len(late_known) == 577,
         'late577-coordinate closure conditional on the22 proved orientations')
    return known, late_known


def restoration(raw, parent, cert, known):
    retained = cert['retained_raw_indices']
    need(retained == sorted(set(retained)) and len(retained) == 667, 'retained raw coordinate map')
    need([raw['variables'][i] for i in retained] == parent['variables'], 'all retained metadata bound')
    restored = {v: {(i,): 1} for i, v in enumerate(retained)}
    records = cert['omitted']
    need([r['raw_variable'] for r in records] == sorted(set(range(len(raw['variables']))) - set(retained)),
         'every omitted coordinate has one recipe')
    rows = {r['gate']: r for r in raw['rows'] if r.get('gate') is not None}
    for item in records:
        v = item['raw_variable']
        need(v in rows, 'no omitted free input')
        row = decode(rows[v]['terms'])
        need(row.get((v,)) == 1 and all(v not in m or m == (v,) for m in row), 'raw affine pivot')
        expected = {}
        for m, c in row.items():
            if m == (v,):
                continue
            need(len(m) <= 1 and c < 0 and all(i < v for i in m), 'triangular positive affine recipe')
            if not m:
                add_term(expected, (), -c)
            else:
                need(m[0] in restored, 'earlier raw recipe available')
                for n, d in restored[m[0]].items():
                    add_term(expected, n, -c * d)
        need(expected == decode(item['terms']), 'entire stored restoring polynomial')
        restored[v] = expected
    need(len(restored) == len(raw['variables']), 'all raw variables restored over integers')
    natural = {v for v, p in restored.items()
               if all(c > 0 and set(m) <= known for m, c in p.items())}
    return restored, natural


def interface_certificate(raw, parent, sign, interface, restored, natural):
    names = {v['name']: i for i, v in enumerate(raw['variables'])}
    need(len(names) == len(raw['variables']), 'unique complete raw names')
    start = raw['scale'][0][1]
    need(interface['private_start'] == start == 643, 'actual private boundary')
    need(interface['semantic_prefix_raw_variables'] == list(range(start)) and set(range(start)) <= natural,
         'all643 semantic-prefix variables nonnegative before any macro interpretation')
    need(interface['raw_nonnegative_from_initial_sign_steps'] == sorted(natural), 'entire raw sign closure')
    need(interface['frame'] == raw['scale'] and interface['auxiliary'] == raw['auxiliary']
         and interface['discriminant'] == raw['discriminant'], 'actual common frame references')
    for term in raw['scale'] + raw['auxiliary']:
        need(term[0] == 'v' and term[1] in natural, 'main shared coordinate natural')
    row_by_label = {r['label']: i for i, r in enumerate(raw['rows']) if r.get('gate') is None}
    seed_by_exponent = {tuple(s['exponent']): s for s in raw['seeds']}
    seed_records = interface['seeds']
    need(len(seed_records) == len(seed_by_exponent) == 15, 'all15 seed certificates')
    expected_private_free = {names[x] for x in ['shared.W', 'shared.A', 'shared.Zminus1',
        'shared_index.U', 'shared_index.V', 'shared_index.q4minus1', 'shared_index.Bquotient',
        'shared_index.Vquotient_minus1', 'index_addition.D']}
    expected_private_rows = {row_by_label[x] for x in ['shared.last_norm', 'shared.frame_definition',
        'shared_index.norm', 'shared_index.B_mod_U', 'shared_index.V_positive_product',
        'index_addition.D_definition']}
    omitted_quotients = {names['shared_index.Bquotient']}
    for item in seed_records:
        original = seed_by_exponent[tuple(item['exponent'])]
        need(item['X'] == original['pair'][0] and item['Y'] == original['pair'][1], 'actual seed pair')
        prefix = raw['variables'][item['X'][1]]['name'].removesuffix('.X')
        for label in ['X', 'Y', 'S', 'R', 'YminusK', 'Squotient', 'Rquotient']:
            ref = ['v', names[prefix + '.' + label]]
            need(item[label] == ref, 'all actual seed role references')
            expected_private_free.add(ref[1])
        need(item['X'][1] in natural and item['Y'][1] in natural
             and item['YminusK'][1] in natural, 'main seed bounds have independent sign proofs')
        for label in ['index_at_most_Y', 'norm1', 'norm3', 'S_mod_U', 'R_mod_4Y']:
            need(item['rows'][label] == row_by_label[prefix + '.' + label], 'actual seed row binding')
            expected_private_rows.add(item['rows'][label])
        omitted_quotients.update((item['Squotient'][1], item['Rquotient'][1]))
    need(interface['all_indices'] == raw['indices'] and interface['derivations'] == raw['derivations'],
         'entire16-group/one-derived-pair ledger')
    need(len(interface['powers']) == len(raw['powers']) == 21, 'all21 power calls')
    for j, (actual, expected) in enumerate(zip(interface['powers'], raw['powers'])):
        for field in ['base', 'exponent', 'output']:
            need(actual[field] == expected[field] and actual[field][0] == 'v'
                 and actual[field][1] < start and actual[field][1] in natural,
                 'actual power port precedes private data and is nonnegative')
        q = names['pow' + str(j) + '.quotient']
        need(actual['quotient'] == ['v', q]
             and actual['row'] == row_by_label['pow' + str(j) + '.power_congruence'],
             'actual oriented quotient and power row')
        expected_private_free.add(q)
        expected_private_rows.add(actual['row'])
        omitted_quotients.add(q)
    for name in names:
        if re.fullmatch(r'base\d+\.T', name):
            need(names[name] in natural, 'all natural base moduli retained')
            expected_private_free.add(names[name])
            expected_private_rows.add(row_by_label[name.removesuffix('.T') + '.T_definition'])
    actual_private_free = {i for i, v in enumerate(raw['variables']) if i >= start and v['kind'] != 'gate'}
    defined = {r['gate'] for r in raw['rows'] if r.get('gate') is not None}
    need(defined == {i for i, v in enumerate(raw['variables']) if v['kind'] in ['gate', 'square_difference']},
         'free/defined classification agrees with actual gate pivots')
    need(actual_private_free == set(range(start, len(raw['variables']))) - defined,
         'private free inputs derived from rows, not merely descriptive labels')
    need(interface['private_free_variables'] == sorted(actual_private_free)
         and actual_private_free == expected_private_free and len(actual_private_free) == 142,
         'all142 private free inputs have a proved reconstruction role')
    groups = [interface[k] for k in ['semantic_non_gate_rows', 'private_non_gate_rows', 'all_gate_rows']]
    need(all(g == sorted(set(g)) for g in groups) and sorted(sum(groups, [])) == list(range(len(raw['rows']))),
         'complete disjoint1177-row partition')
    for i in groups[0]:
        row = raw['rows'][i]
        need(row.get('gate') is None and all(v < start for c, m in row['terms'] for v in m),
             'semantic row has no private use')
    need(set(groups[1]) == expected_private_rows and len(groups[1]) == 109, 'all109 private constraints exactly covered')
    need(groups[2] == [i for i, r in enumerate(raw['rows']) if r.get('gate') is not None],
         'all1029 defining gates accounted for')
    identities = {canonical(v): i for i, v in enumerate(raw['variables'])}
    contracted = {identities[canonical(v)]: i for i, v in enumerate(parent['variables'])}
    need(set(sign['removed_guards']) == {contracted[i] for i in omitted_quotients},
         'all52 guard omissions bound to actual checked macro roles')
    return dict(semantic_prefix_variables=643, semantic_constraints=len(groups[0]),
        raw_gate_definitions=len(groups[2]), private_constraints=109, private_free_inputs=142,
        powers=21, exponent_groups=16, seeds=15, derived_pairs=1)


def guard_equation(parent, equation, sign):
    need(equation['domain'] == 'unrestricted integers' and equation['variables'][:667] == parent['variables'],
         'literal original667 coordinates with integer domain')
    need(equation['residuals'][:585] == parent['residuals'], 'all585 original rows unchanged')
    need(len(equation['variables']) == 994 and len(equation['residuals']) == 694, 'whole994/694 inventory')
    for j, v in enumerate(sign['guards']):
        a, b, c = (667 + 3 * j + d for d in range(3))
        expected = {(v,): 1, (a, a): -1, (b, b): -1, (c,): -1, (c, c): -1}
        need(decode(equation['residuals'][585 + j]['terms']) == expected, 'complete private quadratic guard')
        need([equation['variables'][i] for i in [a, b, c]] == [
            {'kind': 'nonnegative_guard', 'name': 'guard.' + str(v) + '.' + s} for s in ['a', 'b', 'c']],
            'private guard-coordinate ownership')


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def comparison_normalization(data):
    """Whole polynomial identities for the explicit common-base lift."""
    need(data['symbols'] == ['A', 'U', 'V', 'q4', 'bq'], 'normalization free symbols')
    env = {name: {(i,): 1} for i, name in enumerate(data['symbols'])}
    def parse(text):
        def visit(node):
            if isinstance(node, ast.Name):
                return env[node.id]
            if isinstance(node, ast.Constant) and type(node.value) is int:
                return {(): node.value} if node.value else {}
            need(isinstance(node, ast.BinOp), 'polynomial normalization syntax')
            a, b = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Mult):
                return multiply(a, b)
            need(isinstance(node.op, (ast.Add, ast.Sub)), 'ring-only normalization operation')
            result = dict(a)
            for m, c in b.items():
                add_term(result, m, -c if isinstance(node.op, ast.Sub) else c)
            return result
        return visit(ast.parse(text, mode='eval').body)
    need(data['schedule'] == [
        ['t', 'A+1'], ['B', '1+4*V*(q4+1)'], ['q4new', 'q4+U*t'],
        ['bqnew', 'bq+4*V*t'], ['Bnew', 'B+4*V*U*t']], 'literal row-coordinate update schedule')
    for name, text in data['schedule']:
        need(name not in env, 'fresh normalization register')
        env[name] = parse(text)
    expected = ['Bnew-(1+4*V*(q4new+1))',
                '(Bnew-A-U*bqnew)-(B-A-U*bq)']
    need(data['zero_identities'] == expected, 'complete required normalization identities')
    need(all(parse(text) == {} for text in expected), 'whole normalized base/progression identities')
    return dict(symbols=5, exact_polynomial_identities=2,
        base_row_residual_preserved=True, q4_progression_identity=True,
        scope='Unbounded ring identities; positivity and Pell comparison witnesses are proved in PROOF.md.')


def signed_lift_controls():
    """Exact small certificates exhibit the sign boundary and the common lift."""
    def pell(a, k):
        x, y = 1, 0
        for _ in range(k):
            x, y = a * x + (a * a - 1) * y, x + a * y
        return x, y
    records = []
    for a, k, n in [(3, 1, 1), (2, 2, 8)]:
        x, y = pell(a, k)
        u, v = pell(a, n)
        need(v > 0 and v % (y * y) == 0, 'fixture positive square divisibility')
        t = ((a - 1) * pow(4 * v, -1, u)) % u
        if not t:
            t = u
        b, q4 = 1 + 4 * v * t, t - 1
        need((b - a) % u == 0 and b > 0, 'fixture actual common-base rows')
        for es in [-1, 1]:
            for er in [-1, 1]:
                found = None
                for h in range(4 * n):
                    s, r = pell(b, h)
                    s, r = es * s, er * r
                    if (s - x) % u == 0 and (r - k) % (4 * y) == 0:
                        found = (s, r)
                        break
                need(found is not None, 'all four signed comparison cases exist')
                s, r = found
                need(s * s - (b * b - 1) * r * r == 1, 'actual signed comparison norm')
                newq4 = q4 + u * (a + 1)
                newbq = (b - a) // u + 4 * v * (a + 1)
                newb = b + 4 * v * u * (a + 1)
                news, newr = pell(newb, k)
                need(newb == 1 + 4 * v * (newq4 + 1) == a + u * newbq,
                     'both normalized common-base row updates')
                need(newb > a and news >= x and newr >= k
                     and (news - x) % u == (newr - k) % (4 * y) == 0,
                     'fresh positive comparison progressions')
                records.append(dict(A=a, k=k, auxiliary_index=n, S_sign=es, R_sign=er,
                    old_Sq_negative=(s - x) // u < 0, old_Rq_negative=(r - k) // (4 * y) < 0,
                    new_base_greater_than_A=True, new_progression_quotients_nonnegative=True))
    return dict(cases=records, scope='Finite diagnostics for the exact signed/private boundary; not the universal proof.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    pins = load('SOURCE_PINS.json')
    for name, pin in pins['sources'].items():
        raw_copy = (HERE / 'source' / name).read_bytes()
        need(digest(raw_copy) == pin['sha256']
             and raw_copy == (ROOT / pin['repository_path']).read_bytes(), 'exact frozen parent copy ' + name)
    for path, expected in pins['independent_checker_sources'].items():
        need(digest((ROOT / path).read_bytes()) == expected, 'pinned independent checker source ' + path)
    build = load('BUILD.json')
    need(digest((HERE / 'build.py').read_bytes()) == build['generator_sha256'], 'literal generator source binding')
    for path, expected in build['sha256'].items():
        need(digest((HERE / path).read_bytes()) == expected, 'complete generated payload ' + path)
    parent, raw, ledger = (load('source/' + s) for s in ['natural667.json', 'raw_builder.json', 'gate_ledger.json'])
    sign, cert, interface = (load(s) for s in ['mixed_sign_certificate.json', 'raw_restoration.json', 'arithmetic_interfaces.json'])
    known, late = sign_certificate(parent, sign)
    previous_guards = load('source/full_domain_conversion.json')['positivity']['guard_indices']
    need(set(sign['guards']) | set(sign['removed_guards']) == set(previous_guards)
         and len(previous_guards) == 161, 'retained/omitted guards partition the exact old161 seeds')
    restored, natural = restoration(raw, parent, cert, known)
    boundary = interface_certificate(raw, parent, sign, interface, restored, natural)
    export = raw_export(raw, ledger, parent)  # exact identities hold over all integers
    equation = load('equation.json')
    guard_equation(parent, equation, sign)
    metrics = full_sos(equation, load('expanded_polynomial.json'))
    normalization = comparison_normalization(load('COMPARISON_NORMALIZATION.json'))
    archive_pin = pins['inherited_arithmetic_archive']
    archive = REPO / archive_pin['repository_path']
    need(digest(archive.read_bytes()) == archive_pin['sha256'], 'whole inherited arithmetic archive')
    with zipfile.ZipFile(archive) as z, tempfile.TemporaryDirectory(prefix='mixed667-independent-') as tmp:
        path = Path(tmp) / 'audit_new.py'
        path.write_bytes(z.read('ConZFC_407_888_Quartics/code/audit_new.py'))
        need(digest(path.read_bytes()) == pins['pinned_raw_arithmetic_auditor_sha256'],
             'exact independent arithmetic auditor bytes')
        arithmetic = module('mixed667_pinned_arithmetic', path)
        parent_checks = module('mixed667_parent_interfaces', ROOT / 'candidates/projected-factorial-radius/check.py')
        class TracedAudit(arithmetic.Audit):
            touched = set()
            def row_poly(self, label, leaves, disc=False):
                self.touched.add(label)
                return super().row_poly(label, leaves, disc)
        scalar = parent_checks.scalar_audit(raw, TracedAudit)
        audit = TracedAudit(raw)
        A, D = raw['scale'][1], raw['discriminant']
        x, y = {(-1,): 1}, {(-2,): 1}
        expected = multiply(x, x)
        add_term(expected, (-2,), -1)
        add_term(expected, (), -1)
        need(audit.row_poly('index_addition.D_definition', {A[1]: x, D[1]: y}) == expected,
             'actual discriminant definition used by derived recurrence')
        need({raw['rows'][i]['label'] for i in interface['private_non_gate_rows']} <= TracedAudit.touched,
             'independent exact arithmetic auditor covers every private constraint')
        scalar['pinned_independent_auditor_sha256'] = digest(path.read_bytes())
    theorem_pin = pins['signed_theorem_archive']
    theorem_archive = REPO / theorem_pin['repository_path']
    need(digest(theorem_archive.read_bytes()) == theorem_pin['sha256'], 'whole reviewed signed theorem archive')
    controls = []
    def reject(label, thunk):
        try:
            thunk()
        except (ValueError, RuntimeError, KeyError, IndexError, TypeError):
            controls.append(label)
        else:
            raise ValueError('corruption accepted: ' + label)
    bad = deepcopy(sign)
    bad['proof_steps'][0]['rhs'][0][0] += 1
    reject('changed actual sign-row coefficient', lambda: sign_certificate(parent, bad))
    bad = deepcopy(sign)
    bad['proof_steps'].insert(1, deepcopy(bad['proof_steps'][0]))
    reject('repeated sign inference', lambda: sign_certificate(parent, bad))
    bad = deepcopy(cert)
    bad['omitted'][0]['terms'][0][0] += 1
    reject('changed raw restoring polynomial', lambda: restoration(raw, parent, bad, known))
    bad = deepcopy(interface)
    bad['powers'].pop()
    reject('missing complete power call', lambda: interface_certificate(raw, parent, sign, bad, restored, natural))
    bad = deepcopy(interface)
    bad['private_free_variables'].pop()
    reject('unaccounted private free input', lambda: interface_certificate(raw, parent, sign, bad, restored, natural))
    bad = deepcopy(interface)
    bad['semantic_non_gate_rows'].append(bad['private_non_gate_rows'].pop())
    reject('private residual misclassified as semantic', lambda: interface_certificate(raw, parent, sign, bad, restored, natural))
    bad = deepcopy(equation)
    bad['residuals'][-1]['terms'][-1][0] += 1
    reject('changed retained guard', lambda: guard_equation(parent, bad, sign))
    bad = load('expanded_polynomial.json')
    bad['terms'][0][0] += 1
    reject('changed whole quartic coefficient', lambda: full_sos(equation, bad))
    bad = load('COMPARISON_NORMALIZATION.json')
    bad['schedule'][3][1] = 'bq+4*V*U*t'
    reject('wrong base-quotient normalization', lambda: comparison_normalization(bad))
    result = dict(status='PASS', optimized_python=bool(sys.flags.optimize), metrics=metrics,
        sign_certificate=dict(guards=109, actual_row_sign_steps=len(sign['proof_steps']),
            initially_nonnegative=len(known), unresolved=134, late_orientation_results=22,
            late_product_steps=len(sign['late_proof_steps']), after_late_orientation=len(late),
            signed_comparison_closure_remaining=90),
        integer_raw_restoration=export, complete_arithmetic_boundary=boundary,
        exact_scalar_interfaces=scalar, rejected_corruptions=controls,
        explicit_comparison_normalization=normalization,
        signed_comparison_lift_controls=signed_lift_controls(),
        scope='Exact complete finite certificates and polynomial. The ordinary proof establishes the unbounded signed-index/reconstruction equivalence; no pointwise all-natural or Lean/internal-ZFC claim.')
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
