#!/usr/bin/env python3
"""Independent addendum audit. Only arithmetic JSON data are consumed.

No author emitter, source program, earlier verifier, or third-party module is
imported or executed. Writes, when requested, are confined to this audit folder.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

# Portable destination guard; this path is not a data dependency.
BASE = Path(__file__).resolve().parents[2] / 'reproducibility'
BASE_PIN = '1bf1225aa950ad1d4f842c8bf098e1935925cd1d52c90453b7696c1321648f95'
MODULUS = 1000003
# total, multiplications, additions/subtractions, positive witnesses, exact degree, top
EXPECTED = {
    'incdec': (603, 239, 364, 60, 2344, 135347),
    'zero3': (478, 184, 294, 58, 1192, 977370),
    'nop': (476, 182, 294, 58, 1192, 977370),
    'positive3': (479, 189, 290, 58, 1192, 977370),
}


def require(test, message):
    if not test:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def unique_keys(items):
    ans = {}
    for key, value in items:
        require(key not in ans, 'duplicate JSON key: ' + key)
        ans[key] = value
    return ans


def read(path):
    return json.loads(path.read_bytes(), object_pairs_hook=unique_keys)


def base_integrity(root, live_base=None):
    manifest_bytes = (root / 'reference' / 'base-MANIFEST.json').read_bytes()
    require(digest(manifest_bytes) == BASE_PIN, 'frozen reference manifest pin')
    records = json.loads(manifest_bytes, object_pairs_hook=unique_keys)['files']
    checked = {}
    expected = {'base-MANIFEST.json'}
    for fixture in EXPECTED:
        for model in ['native', 'phase4']:
            name = fixture + '-' + model + '.json'
            expected.add(name)
            data = (root / 'reference' / name).read_bytes()
            record = records['circuits/' + name]
            require(len(data) == record['bytes'], 'reference byte size: ' + name)
            require(digest(data) == record['sha256'], 'reference SHA256: ' + name)
            checked[name] = digest(data)
    require({p.name for p in (root / 'reference').iterdir() if p.is_file()} == expected,
            'exact eight reference circuits and frozen manifest')
    if live_base is not None:
        require(digest((live_base / 'MANIFEST.json').read_bytes()) == BASE_PIN, 'live base manifest pin')
        for name, record in records.items():
            path = live_base / name
            require(path.resolve().is_relative_to(live_base.resolve()), 'manifest path containment')
            data = path.read_bytes()
            require(len(data) == record['bytes'] and digest(data) == record['sha256'],
                    'live frozen file: ' + name)
    return {'manifest_sha256': BASE_PIN, 'verified_reference_circuits': len(checked),
            'reference_sha256': checked}


def inspect_graph(packet):
    ports = packet['parameters'] + packet['auxiliaries']
    require(all(type(p) is str for p in ports), 'named coordinates')
    require(len(set(ports)) == len(ports), 'unique coordinates')
    known = set(ports)
    parents = {}
    literals = set()
    multiplication_count = 0
    for row in packet['source']:
        require(type(row) is list and len(row) == 4, 'four-column instruction')
        target, operator, left, right = row
        require(type(target) is str and target not in known, 'single-assignment fresh target')
        require(operator in {'+', '-', '*'}, 'arithmetic-only operator')
        refs = []
        for arg in [left, right]:
            if type(arg) is int:
                literals.add(arg)
            else:
                require(type(arg) is str and arg in known, 'closed earlier operand')
                refs.append(arg)
        parents[target] = refs
        known.add(target)
        multiplication_count += operator == '*'
    require(packet['output'] in parents, 'computed output')
    needed = {packet['output']}
    # A single reverse topological scan suffices because all parents are earlier.
    for target, _, _, _ in reversed(packet['source']):
        if target in needed:
            needed.update(parents[target])
    require(known == needed, 'no dead coordinate or gate')
    return {
        'total': len(packet['source']), 'M': multiplication_count,
        'A': len(packet['source']) - multiplication_count,
        'natural_parameters': len(packet['parameters']),
        'positive_witnesses': len(packet['auxiliaries']),
        'integer_literals': sorted(literals),
        'all_coordinates_live': True, 'all_gates_live': True,
    }


def inspect_sos(packet):
    """Verify a complete suffix directly, retaining no author assertion of SOS."""
    pairs = packet['comparisons']
    require(type(pairs) is list and len(pairs) == 20, 'twenty comparisons')
    require(all(type(p) is list and len(p) == 2 for p in pairs), 'comparison arities')
    suffix = packet['source'][-59:]
    require(len(suffix) == 59, '59-row SOS')
    square_names = []
    for index, pair in enumerate(pairs):
        subtraction, square = suffix[index * 2:index * 2 + 2]
        require(subtraction[1:] == ['-'] + pair, 'literal residual operands')
        require(square[1:] == ['*', subtraction[0], subtraction[0]], 'literal residual square')
        square_names.append(square[0])
    sums = {square_names[0]: (1,) + (0,) * 19}
    for index, row in enumerate(suffix[40:], 1):
        target, op, left, right = row
        require(op == '+' and left in sums and right == square_names[index], 'sum all squares once')
        counts = list(sums[left])
        counts[index] += 1
        sums[target] = tuple(counts)
    require(sums.get(packet['output']) == (1,) * 20, 'output is precisely all twenty squares')
    require(packet['output'] == suffix[-1][0], 'last gate is output')
    return len(packet['source']) - 59


# Exact sparse multivariate operations, used only for the tiny affine bridge.
# The four indeterminates below are F, x, theta, Tclean; keys are exponent tuples.
ZERO = (0, 0, 0, 0)
VARS = ['final_positive', 'x', 'theta_positive', 'Tclean']


def polynomial_sum(a, b, sign=1):
    out = dict(a)
    for powers, coefficient in b.items():
        out[powers] = out.get(powers, 0) + sign * coefficient
    return {p: c for p, c in out.items() if c}


def polynomial_product(a, b):
    out = {}
    for pa, ca in a.items():
        for pb, cb in b.items():
            powers = tuple(x + y for x, y in zip(pa, pb))
            out[powers] = out.get(powers, 0) + ca * cb
    return {p: c for p, c in out.items() if c}


def bridge_polynomial(rows, requested_time=False):
    env = {}
    for index, name in enumerate(VARS):
        exponent = tuple(int(i == index) for i in range(4))
        env[name] = {exponent: 1}
    def resolve(arg):
        return {ZERO: arg} if type(arg) is int else env[arg]
    for target, operator, left, right in rows:
        a, b = resolve(left), resolve(right)
        env[target] = (polynomial_product(a, b) if operator == '*' else
                       polynomial_sum(a, b, 1 if operator == '+' else -1))
    result = env[rows[-1][0]]
    if requested_time:
        result = polynomial_sum(result, env['Tclean'], -1)
    return result


def degree_audit(packet):
    """Formal upper bounds, certified by a full univariate specialization.

    Independently compute all coefficients of P((i+2)z) modulo MODULUS, not
    merely the claimed top coefficient. Formal upper bounds never decrease
    when specialized leading terms happen to cancel.
    """
    ports = packet['parameters'] + packet['auxiliaries']
    weights = {name: i + 2 for i, name in enumerate(ports)}
    bounds = {name: 1 for name in ports}
    polynomials = {name: {1: weight} for name, weight in weights.items()}
    top = {name: weight for name, weight in weights.items()}
    trace = []
    def resolve(arg):
        if type(arg) is int:
            return 0, {0: arg % MODULUS} if arg % MODULUS else {}, arg % MODULUS
        return bounds[arg], polynomials[arg], top[arg]
    for target, operator, left, right in packet['source']:
        da, a, ta = resolve(left)
        db, b, tb = resolve(right)
        if operator == '*':
            bound = da + db
            coefficients = {}
            for ia, ca in a.items():
                for ib, cb in b.items():
                    coefficients[ia + ib] = coefficients.get(ia + ib, 0) + ca * cb
            formal_top = ta * tb
        else:
            bound = max(da, db)
            sign = 1 if operator == '+' else -1
            coefficients = dict(a)
            for degree, coefficient in b.items():
                coefficients[degree] = coefficients.get(degree, 0) + sign * coefficient
            formal_top = (ta if da == bound else 0) + sign * (tb if db == bound else 0)
        poly = {d: c % MODULUS for d, c in coefficients.items() if c % MODULUS}
        bounds[target], polynomials[target], top[target] = bound, poly, formal_top % MODULUS
        require(poly.get(bound, 0) == formal_top % MODULUS, 'full coefficient agrees with formal component')
        require(not poly or max(poly) <= bound, 'specialization respects formal bound')
        trace.append([target, bound, formal_top % MODULUS])
    output = packet['output']
    degree = bounds[output]
    full = polynomials[output]
    require(full and max(full) == degree, 'nonzero specialization reaches full formal bound')
    cert = {
        'modulus': MODULUS, 'substitution_weights': weights,
        'formal_degree': degree, 'nonzero_top_coefficient': full[degree],
        'gate_degree_top_trace': trace,
    }
    require(packet['exact_degree_certificate'] == cert, 'entire degree certificate independently matches')
    encoded = json.dumps(sorted(full.items()), separators=(',', ':')).encode()
    return degree, full[degree], {
        'full_specialization_nonzero_coefficients': len(full),
        'full_specialization_sha256': digest(encoded),
        'full_specialization_degree': max(full),
        'formal_top_zero_rows_retained': sum(c == 0 for _, _, c in trace),
    }


def evaluate(packet, assignment, modulus=None):
    values = dict(assignment)
    def resolve(arg):
        return arg if type(arg) is int else values[arg]
    for target, operator, left, right in packet['source']:
        a, b = resolve(left), resolve(right)
        value = a + b if operator == '+' else a - b if operator == '-' else a * b
        values[target] = value if modulus is None else value % modulus
    residuals = [resolve(a) - resolve(b) for a, b in packet['comparisons']]
    direct = sum(r * r for r in residuals)
    require(values[packet['output']] == (direct if modulus is None else direct % modulus), 'direct SOS evaluation')
    if modulus is None:
        require(direct >= 0 and ((direct == 0) == all(r == 0 for r in residuals)), 'integer SOS zero equivalence')
    return values[packet['output']]


def compare_trials(folded, original):
    ports = folded['parameters'] + folded['auxiliaries']
    for trial in range(12):
        assignment = {p: ((i + 3) * (trial + 2) + i * i) % 7 - 3 for i, p in enumerate(ports)}
        require(evaluate(folded, assignment) == evaluate(original, assignment), 'signed all-tuple identity sample')
    for trial in range(32):
        assignment = {p: ((i + 11) ** 3 * 99991 + trial * 65537 * (i + 3) - trial ** 2) % MODULUS
                      for i, p in enumerate(ports)}
        require(evaluate(folded, assignment, MODULUS) == evaluate(original, assignment, MODULUS),
                'modular all-tuple identity sample')


def audit_one(folded, original, expensive=True):
    name = folded['fixture']
    require(name in EXPECTED, 'known fixture')
    require(folded['parameters'] == ['x', 'Tclean'], 'natural interface')
    require(folded['parameters'] == original['parameters'], 'unchanged natural ports')
    require(folded['auxiliaries'] == original['auxiliaries'], 'identical ordered positive witnesses')
    require('T' not in folded['parameters'] + folded['auxiliaries'], 'no leaked raw T coordinate')
    require('y' not in folded['parameters'] + folded['auxiliaries'], 'no leaked y coordinate')
    for key in ['domain', 'forward_final_payload_coordinate', 'native_clock_coordinate',
                'cleaned_target_payload', 'removed_comparison', 'physical_clock_factor',
                'source_pin', 'source_commit', 'source_machine', 'mapping']:
        require(folded[key] == original[key], 'unchanged semantic field: ' + key)
    require(folded['domain'] == 'x,Tclean are natural integers; all listed auxiliaries are strictly positive integers',
            'positive witness domain explicitly preserved')
    factor = folded['physical_clock_factor']
    require(factor in [1, 4], 'native or phase4 clock factor')
    phase = factor == 4
    require(folded['format'] == 'complete-unbounded-clean-clock-literal-folded-v1', 'folded format')
    require(folded['model'] == ('phase4-literal-folded' if phase else 'native-or-spatial-block-literal-folded'),
            'explicit folded model')
    require(folded['folding_base_manifest_sha256'] == BASE_PIN, 'folding base provenance')
    formula = ('768*(final_positive+x)+8*theta_positive+832' if phase else
               '192*(final_positive+x)+2*theta_positive+208')
    require(folded['folded_clock_formula'] == formula, 'literal formula metadata')
    graph = inspect_graph(folded)
    inspect_graph(original)
    fold_end, old_end = inspect_sos(folded), inspect_sos(original)
    core_end = old_end - (7 if phase else 6)
    require(fold_end == core_end + 5, 'five-gate folded bridge')
    require(folded['source'][:core_end] == original['source'][:core_end], 'entire inherited core unchanged')
    require(folded['comparisons'][:19] == original['comparisons'][:19], 'nineteen inherited guards unchanged')
    old_bridge = original['source'][core_end:old_end]
    new_bridge = folded['source'][core_end:fold_end]
    require(sum(row[1] == '*' for row in new_bridge) == 2, 'two paid bridge multiplications')
    require(sum(row[1] != '*' for row in new_bridge) == 3, 'three paid bridge additions')
    require(folded['comparisons'][19] == [new_bridge[-1][0], 'Tclean'], 'folded clean time guard')
    require(original['comparisons'][19] == [old_bridge[-1][0], 'Tclean'], 'original clean time guard')
    require(folded['source'][fold_end:] == original['source'][old_end:], 'entire SOS suffix literally unchanged')
    require(folded['comparisons'] == original['comparisons'], 'entire comparison list literally unchanged')
    old_poly, new_poly = bridge_polynomial(old_bridge), bridge_polynomial(new_bridge)
    expected = {(1, 0, 0, 0): 192 * factor, (0, 1, 0, 0): 192 * factor,
                (0, 0, 1, 0): 2 * factor, ZERO: 208 * factor}
    require(old_poly == new_poly == expected, 'exact coefficientwise bridge identity over Z')
    old_residual = bridge_polynomial(old_bridge, True)
    new_residual = bridge_polynomial(new_bridge, True)
    require(polynomial_product(old_residual, old_residual) == polynomial_product(new_residual, new_residual),
            'coefficientwise identity of final residual squares')
    # All earlier residual pairs reference only the unchanged common core/ports.
    core_names = set(folded['parameters'] + folded['auxiliaries']) | {r[0] for r in folded['source'][:core_end]}
    require(all(type(a) is int or a in core_names for pair in folded['comparisons'][:19] for a in pair),
            'first nineteen residuals exclusively use identical common nodes')
    graph['comparisons'], graph['SOS_gates'] = 20, 59
    expected_total, expected_m, expected_a, witnesses, degree, top = EXPECTED[name]
    require((graph['total'], graph['M'], graph['A'], graph['positive_witnesses']) ==
            (expected_total, expected_m, expected_a, witnesses), 'independently counted expected ledger')
    graph['exact_degree'] = degree
    require(folded['ledger'] == graph, 'entire ledger including integer literals')
    require(len(original['source']) - len(folded['source']) == (2 if phase else 1), 'exact operation saving')
    degree_result = {}
    if expensive:
        computed_degree, computed_top, degree_result = degree_audit(folded)
        require((computed_degree, computed_top) == (degree, top), 'expected exact degree and top coefficient')
        require(original['exact_degree_certificate']['formal_degree'] == degree and
                original['exact_degree_certificate']['nonzero_top_coefficient'] == top,
                'unchanged pinned original degree and component')
        compare_trials(folded, original)
    return {
        'status': 'PASS', **graph, 'unchanged_core_gates': core_end,
        'unchanged_raw_guards': 19, 'folded_bridge_gates': 5,
        'original_bridge_gates': 7 if phase else 6,
        'operations_saved': 2 if phase else 1, 'multiplications_saved': 1 if phase else 0,
        'additions_saved': 1,
        'all_tuple_complete_polynomial_identity': True,
        'affine_clock_coefficients': {'F': 192 * factor, 'x': 192 * factor, 'theta': 2 * factor, 'constant': 208 * factor},
        'formal_top_modulus': MODULUS, 'formal_top_component': top,
        **degree_result,
        'signed_integer_identity_and_SOS_trials': 12 if expensive else 0,
        'modular_identity_and_SOS_trials': 32 if expensive else 0,
    }


def inspect_text(path, packet):
    lines = path.read_text().splitlines()
    require('# Natural ports: ' + ', '.join(packet['parameters']) in lines, 'text natural ports')
    require('# Strictly positive existential ports: ' + ', '.join(packet['auxiliaries']) in lines, 'text witnesses')
    require('# Polynomial output: ' + packet['output'] in lines, 'text output')
    require('# Required equation: ' + packet['output'] + ' = 0' in lines, 'text equation')
    rows = []
    for line in lines:
        if not line.strip() or line.startswith('#'):
            continue
        target, eq, left, op, right = line.split()
        require(eq == '=', 'text equality sign')
        def atom(text):
            try:
                return int(text)
            except ValueError:
                return text
        rows.append([target, op, atom(left), atom(right)])
    require(rows == packet['source'], 'complete text/JSON equality')


def rejection_tests(packet, old):
    labels = []
    def reject(label, mutate, expensive=False):
        changed = copy.deepcopy(packet)
        mutate(changed)
        try:
            audit_one(changed, old, expensive=expensive)
        except (RuntimeError, KeyError, IndexError, TypeError):
            labels.append(label)
        else:
            raise RuntimeError('undetected mutation: ' + label)
    split = len(packet['source']) - 59
    reject('wrong folded constant', lambda c: c['source'][split - 1].__setitem__(3, 65))
    reject('wrong inherited core literal', lambda c: c['source'][0].__setitem__(2, 7))
    reject('removed positive witness', lambda c: c['auxiliaries'].pop())
    reject('nonpositive witness domain', lambda c: c.__setitem__('domain', 'all integers'))
    reject('undeclared input', lambda c: c['source'][0].__setitem__(3, 'undeclared'))
    reject('extra dead gate', lambda c: c['source'].insert(0, ['dead', '+', 'x', 0]))
    reject('removed retained guard', lambda c: c['comparisons'].__delitem__(0))
    reject('wrong SOS square', lambda c: c['source'][split + 1].__setitem__(3, 'x'))
    reject('underreported total', lambda c: c['ledger'].__setitem__('total', c['ledger']['total'] - 1))
    reject('wrong exact-degree claim', lambda c: c['ledger'].__setitem__('exact_degree', 1))
    reject('false top coefficient', lambda c: c['exact_degree_certificate'].__setitem__('nonzero_top_coefficient', 0), True)
    return labels


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--expect', type=Path, help='read-only deterministic replay against this receipt')
    parser.add_argument('--check-live-base', type=Path, help='also authenticate every live frozen-base file before and after')
    args = parser.parse_args()
    root = args.root.resolve()
    require(root != BASE.resolve() and (root / 'audit').resolve() == Path(__file__).resolve().parent,
            'only this new sibling audit output destination')
    before = base_integrity(root, args.check_live_base)
    paths = sorted((root / 'circuits').glob('*.json'))
    require(len(paths) == 8, 'exactly eight folded JSON circuits')
    names, results, artifacts = set(), {}, {}
    packets = {}
    for path in paths:
        packet = read(path)
        fixture = packet['fixture']
        model = 'phase4' if packet['physical_clock_factor'] == 4 else 'native'
        stem = fixture + '-' + model
        require(stem not in names, 'one circuit per fixture/model')
        names.add(stem)
        original_path = root / 'reference' / (stem + '.json')
        original = read(original_path)
        require(packet['folding_parent_sha256'] == digest(original_path.read_bytes()), 'folding parent SHA256')
        results[stem] = audit_one(packet, original)
        text_path = path.with_suffix('.dag.txt')
        inspect_text(text_path, packet)
        packets[stem] = (packet, original)
        for artifact in [path, text_path]:
            artifacts[str(artifact.relative_to(root))] = digest(artifact.read_bytes())
    require(names == {name + '-' + model for name in EXPECTED for model in ['native', 'phase4']}, 'all eight fixture/model cases')
    actual_files = {str(p.relative_to(root)) for p in (root / 'circuits').iterdir() if p.is_file()}
    require(actual_files == set(artifacts), 'no unaudited circuit files')
    emission = read(root / 'receipts' / 'emission.json')
    require(emission['format'] == 'folded-clock-emission-v1', 'emission receipt format')
    require(emission['base_manifest_sha256'] == BASE_PIN, 'emission base pin')
    require(emission['emitted_files'] == artifacts, 'emission receipt hashes')
    require(emission['reference_circuits'] == before['reference_sha256'], 'emission reference hashes')
    require(emission['ledgers'] == {name + '-folded': packet['ledger']
                                   for name, (packet, _) in packets.items()}, 'emission receipt full ledgers')
    mutations = {model: rejection_tests(*packets['nop-' + model]) for model in ['native', 'phase4']}
    after = base_integrity(root, args.check_live_base)
    require(before == after, 'frozen base unchanged throughout audit')
    receipt = {
        'status': 'PASS', 'audit_format': 'independent-clean-clock-five-gate-folding-v1',
        'checker_sha256': digest(Path(__file__).read_bytes()),
        'reference_before': before, 'reference_after': after,
        'author_or_source_python_imported_or_executed': False,
        'third_party_modules_used': False,
        'artifact_sha256': artifacts, 'circuits': results,
        'emission_receipt_sha256': digest((root / 'receipts' / 'emission.json').read_bytes()),
        'deliberate_corruptions_rejected': mutations,
        'complete_gates_audited': sum(r['total'] for r in results.values()),
        'all_tuple_identity_method': 'Exact common-core inheritance plus coefficientwise bridge residual-square identity and independent full SOS expansion.',
        'degree_method': 'Formal upper bounds and full univariate specializations modulo 1000003; nonzero coefficient reaches each full bound.',
        'limitations': [
            'Algebraic signed/modular tests do not materialize positive native/Pell witnesses.',
            'The all-tuple polynomial identity transfers the frozen base zero sets and positive-witness fibers exactly.',
            'The inherited dynamical interpretation remains conditional on the frozen base theorems; no new universal loader or universal operation bound is asserted.',
        ],
    }
    data = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    if args.expect:
        require(args.expect.read_text() == data, 'deterministic audit receipt replay')
    else:
        (root / 'audit' / 'independent_folded_clock_audit.json').write_text(data)
    print(json.dumps({'status': 'PASS', 'mode': 'replay' if args.expect else 'audit',
                      'complete_gates_audited': receipt['complete_gates_audited'],
                      'frozen_reference_circuits_verified_before_and_after': before['verified_reference_circuits'],
                      'live_base_files_verified_before_and_after': 44 if args.check_live_base else 0,
                      'circuits': {k: {'total': v['total'], 'witnesses': v['positive_witnesses'],
                                       'degree': v['exact_degree'], 'top': v['formal_top_component']}
                                   for k, v in results.items()}}, sort_keys=True))


if __name__ == '__main__':
    main()
