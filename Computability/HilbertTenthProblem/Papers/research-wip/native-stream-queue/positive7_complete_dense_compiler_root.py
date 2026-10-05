"""Fresh metadata-only emission of two complete positive7 source families.

No scientific source is imported or executed. Parent JSON rows are inert
data: this file only binds names, emits rows, counts and checks topology.
There is deliberately no arithmetic-row evaluator or degree propagation.
After freezing, preserve this file and its receipt without replaying it.
"""
import hashlib
import json
from collections import Counter
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
PARENT = ROOT / 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_binary_positive_scale.json'
PARENT_PIN = 'ee373e17fdd038a0cf0278513c15c7fede80ae8f35ba64bf919859188b40c628'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def fixed(name):
    return {'fixed': name}


class Rows:
    def __init__(self):
        self.rows = []
        self.blocks = []
        self.stage = ''

    def add(self, name, op, left, right):
        self.rows.append([name, op, left, right])
        self.blocks.append(self.stage)
        return name

    def total(self, label, operands):
        if not operands:
            raise ValueError('empty sum')
        acc = operands[0]
        for j, value in enumerate(operands[1:], 1):
            acc = self.add(label + str(j), '+', acc, value)
        return acc

    def pack(self, label, coefficients, radix):
        # The one literal high zero in the selected-output pack is omitted.
        coefficients = list(coefficients)
        while len(coefficients) > 1 and coefficients[-1] == 0:
            coefficients.pop()
        acc = coefficients[-1]
        for j in range(len(coefficients)-2, -1, -1):
            acc = self.add(label + '_shift' + str(j), '*', acc, radix)
            acc = self.add(label + '_cell' + str(j), '+', acc, coefficients[j])
        return acc

    def power(self, label, base, exponent):
        if exponent < 1:
            raise ValueError('positive fixed exponent required')
        acc = base
        for j, bit in enumerate(bin(exponent)[3:]):
            acc = self.add(label + '_square' + str(j), '*', acc, acc)
            if bit == '1':
                acc = self.add(label + '_multiply' + str(j), '*', acc, base)
        return acc


def census(rows):
    operations = Counter(row[1] for row in rows)
    return {'operations': len(rows), 'M': operations['*'],
            'A': operations['+'] + operations['-']}


def static_graph(rows, supplied, output):
    known = set(supplied)
    if len(known) != len(supplied):
        raise ValueError('duplicate supplied coordinate')
    by_name = {}
    fixed_roles = set()
    for name, op, left, right in rows:
        if name in known or op not in ('+', '-', '*'):
            raise ValueError('duplicate output or bad operation')
        for operand in (left, right):
            if isinstance(operand, str):
                if operand not in known:
                    raise ValueError('unbound register ' + operand)
            elif isinstance(operand, dict):
                if set(operand) != {'fixed'}:
                    raise ValueError('bad fixed-numeral role')
                fixed_roles.add(operand['fixed'])
            elif not isinstance(operand, int):
                raise ValueError('bad operand type')
        known.add(name)
        by_name[name] = [left, right]
    live = set()
    todo = [output]
    while todo:
        value = todo.pop()
        if not isinstance(value, str) or value in live:
            continue
        live.add(value)
        todo.extend(by_name.get(value, []))
    unused_rows = sorted(set(by_name) - live)
    unused_supplied = sorted(set(supplied) - live)
    if unused_rows or unused_supplied:
        raise ValueError({'unused_rows': unused_rows, 'unused_supplied': unused_supplied})
    return {'topology': 'PASS', 'all_rows_live': True,
            'all_supplied_live': True, 'fixed_numeral_roles': sorted(fixed_roles)}


def emit(m, mode, parent):
    if m < 1 or mode not in ('dense7', 'column6'):
        raise ValueError('unsupported family parameter')
    r = Rows()
    r.stage = 'loader_and_initial_mass'
    scaled = r.add('input_scaled', '*', fixed('alpha'), 'x')
    tau = r.add('input_tau', '+', scaled, fixed('gamma'))
    tau2 = r.add('input_tau2', '*', tau, tau)
    mass1 = r.add('initial_mass1', '+', tau2, tau)
    mass2 = r.add('initial_mass2', '+', mass1, 3)
    mass = r.add('initial_mass', '+', mass2, mass2)
    z = [3, tau, tau2, 2, tau, tau2, 1]
    H = ['history' + str(i) for i in range(1, 8)]
    F = ['terminal' + str(i) for i in range(1, 7)]
    terminal_ports = F + [F[0]]
    shats = ['selector_hat' + str(s) for s in range(m)]
    zhats = [['selected_hat' + str(s) + '_' + str(i) for i in range(1, 8)] for s in range(m)]
    r.stage = 'geometry_and_bounds'
    selectors = [r.add('selector' + str(s), '-', shats[s], 1) for s in range(m)]
    selected = [[r.add('selected' + str(s) + '_' + str(i+1), '-', zhats[s][i], 1) for i in range(7)] for s in range(m)]
    J = r.total('selector_sum', selectors)
    D = r.add('height_D', '+', mass, 'height_slack')
    B = r.add('radix_B', '*', fixed('K'), D)
    bm1 = r.add('radix_minus_one', '-', B, 1)
    pm1 = r.add('pack_scale_minus_one', '*', bm1, J)
    P = r.add('pack_scale', '+', pm1, 1)
    dm1 = r.add('height_minus_one', '-', D, 1)
    mu = r.add('range_mask', '*', dm1, J)
    S = r.total('history_sum', H)
    Ztot = r.total('selected_sum', [v for group in selected for v in group])
    bound1 = r.add('global_bound1', '+', S, Ztot)
    bound = r.add('global_bound', '+', bound1, 'global_slack')
    comparisons = [[bound, P]]
    masks = [r.add('selection_mask' + str(s), '*', bm1, selectors[s]) for s in range(m)]
    lanes = [[selectors[s], J, selectors[s]] for s in range(m)]
    lanes.extend([H[i], masks[s], selected[s][i]] for s in range(m) for i in range(7))
    lanes.extend([[S, mu, S], [D, dm1, 0]])
    ell = len(lanes)
    r.stage = 'three_packs'
    packs = [r.pack(label, [lane[j] for lane in lanes], P)
             for j, label in enumerate(('left_pack', 'right_pack', 'output_pack'))]
    r.stage = 'fixed_scale_power'
    T = r.power('native_scale_power', P, ell)
    r.stage = 'native64'
    cert = parent['example']['source'][:64]
    def native_operand(value):
        if not isinstance(value, str):
            return value
        if value in parent['example']['parameters']:
            raise ValueError('unexpected native parameter outside replaced header')
        return 'native_' + value
    header = [
        ['native_q', '*', 16, T],
        ['native_scaled_A', '*', 16, packs[0]],
        ['native_padded_A', '+', 'native_scaled_A', 12],
        ['native_scaled_B', '*', 16, packs[1]],
        ['native_padded_B', '+', 'native_scaled_B', 10],
        ['native_scaled_Z', '*', 16, packs[2]],
        ['native_F3', '+', 'native_scaled_Z', 8],
    ]
    for row in header:
        r.add(*row)
    for name, op, left, right in cert[7:]:
        r.add('native_' + name, op, native_operand(left), native_operand(right))
    native_pairs = [[native_operand(a), native_operand(b)] for a, b in parent['example']['comparisons']]
    comparisons.extend(native_pairs)
    r.stage = 'selected_matrix_action'
    outputs = []
    for i in range(7 if mode == 'dense7' else 6):
        products = []
        for s in range(m):
            for k in range(7):
                products.append(r.add('action_' + str(i+1) + '_' + str(s) + '_' + str(k+1), '*',
                                      fixed('A' + str(s) + '_' + str(i+1) + '_' + str(k+1)), selected[s][k]))
        outputs.append(r.total('action_sum' + str(i+1) + '_', products))
    if mode == 'column6':
        action_mass = r.add('action_mass', '*', fixed('C'), S)
        first_six = r.total('action_first_six', outputs)
        outputs.append(r.add('action_seventh', '-', action_mass, first_six))
    r.stage = 'seven_recurrences'
    end_products = {v: r.add('endpoint_scale_' + v, '*', P, v) for v in F}
    for i in range(7):
        left = r.add('recurrence_left' + str(i+1), '*', B, outputs[i])
        right1 = r.add('recurrence_sum' + str(i+1), '+', H[i], end_products[terminal_ports[i]])
        right = r.add('recurrence_right' + str(i+1), '-', right1, z[i])
        comparisons.append([left, right])
    certificate_rows = len(r.rows)
    certificate_ledger = census(r.rows)
    r.stage = 'combined_sos'
    squares = []
    for j, (left, right) in enumerate(comparisons):
        residual = r.add('final_residual' + str(j), '-', left, right)
        squares.append(r.add('final_square' + str(j), '*', residual, residual))
    output = r.total('final_sum', squares)
    aux = H + F + shats + [v for group in zhats for v in group] + ['height_slack', 'global_slack']
    aux += ['native_' + v for v in parent['example']['auxiliaries']]
    graph = static_graph(r.rows, ['x'] + aux, output)
    stage_ledgers = {}
    for stage in dict.fromkeys(r.blocks):
        stage_ledgers[stage] = census([row for row, owner in zip(r.rows, r.blocks) if owner == stage])
    lam = ell.bit_length() - 1 + ell.bit_count() - 1
    expected = {'M': (74*m+53+lam if mode == 'dense7' else 67*m+54+lam),
                'A': (89*m+54 if mode == 'dense7' else 82*m+61)}
    if any(certificate_ledger[key] != value for key, value in expected.items()):
        raise ValueError({'actual': certificate_ledger, 'expected': expected})
    if len(comparisons) != 23 or len(aux) != 8*m+36:
        raise ValueError('interface count')
    return {'mode': mode, 'm': m, 'lanes': ell, 'lambda': lam,
            'ordinary_parameters': ['x'], 'positive_auxiliaries': aux,
            'fixed_data_requirements': ('positive seven-coordinate letters; fixed dyadic K>max(column sums,m); positive alpha,gamma' if mode == 'dense7' else 'positive seven-coordinate letters with common column sum C; fixed dyadic K>max(C,m); positive alpha,gamma'),
            'source': r.rows, 'certificate_prefix_rows': certificate_rows,
            'comparisons': comparisons, 'output': output, 'lanes_in_order': lanes,
            'ports': {'J': J, 'D': D, 'B': B, 'P': P, 'S': S, 'Ztot': Ztot, 'T': T,
                      'native_packs': packs, 'initial_column': z,
                      'terminal_column': terminal_ports, 'selected_outputs': outputs},
            'certificate_ledger': certificate_ledger, 'polynomial_ledger': census(r.rows),
            'equations': len(comparisons), 'witnesses': len(aux),
            'stages': stage_ledgers, 'static_checks': graph}


def main():
    raw = PARENT.read_bytes()
    if digest(raw) != PARENT_PIN:
        raise ValueError('native receipt pin changed')
    parent = json.loads(raw)
    if census(parent['example']['source'][:64]) != {'operations': 64, 'M': 33, 'A': 31}:
        raise ValueError('native prefix count')
    checks = []
    examples = []
    for m in (1, 2, 3, 4, 8, 16):
        for mode in ('dense7', 'column6'):
            packet = emit(m, mode, parent)
            checks.append({key: packet[key] for key in ('mode', 'm', 'lanes', 'lambda', 'certificate_ledger', 'polynomial_ledger', 'equations', 'witnesses')})
            if m in (1, 8):
                examples.append(packet)
    receipt = {'status': 'fresh metadata-only source emission and static census PASS',
               'parent': {'path': str(PARENT.relative_to(ROOT)), 'sha256': PARENT_PIN,
                          'variant': 'example', 'certificate_rows': [0, 64],
                          'scope': 'inert native prefix and comparison/auxiliary metadata; old SOS excluded'},
               'emitter_sha256': digest(Path(__file__).read_bytes()),
               'generic_ledger': {'ell': '8m+2', 'lambda': 'floor(log2 ell)+popcount(ell)-1',
                   'dense7_certificate': '(74m+53+lambda)M+(89m+54)A',
                   'column6_certificate': '(67m+54+lambda)M+(82m+61)A',
                   'sos_increment': '23M+45A', 'equations': 23, 'positive_witnesses': '8m+36'},
               'static_family_checks': checks, 'examples': examples,
               'scope': {'fixed_roles_are_existential': False, 'numerical_universal_alphabet_supplied': False,
                         'scientific_code_executed': False, 'saved_arrays_evaluated': False,
                         'degree_propagation': False, 'emission_and_topology_only': True}}
    out = Path('/tmp/positive7_complete_dense_compiler_root.json')
    if out.exists():
        raise ValueError('refuse to overwrite receipt')
    out.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({'output': str(out), 'sha256': digest(out.read_bytes()),
                      'static_checks': checks}, indent=2))


if __name__ == '__main__':
    main()
