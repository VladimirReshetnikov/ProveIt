"""Original metadata-only emitter for the complete sparse positive7 family.

Frozen artifacts are read only as literal tables and source-row records.
No source arithmetic, coefficient arithmetic or degree propagation occurs.
Do not replay this emitter after it and its first output have been frozen.
"""
import hashlib
import json
from collections import Counter
from pathlib import Path

WORKSPACE = Path('/home/codex/.codex/worktrees/2a71/Proofs')
WIP = WORKSPACE / 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
INPUTS = {
    'native': ('native_binary_positive_scale.json', 'ee373e17fdd038a0cf0278513c15c7fede80ae8f35ba64bf919859188b40c628'),
    'paired': ('positive7_paired_coefficients_fresh_root_check.json', '3c101ed4aa971e5ba53fa1a386322cb810ac281f91be9b0b0ebdd8cfa3b59d63'),
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def counts(source):
    bins = Counter(row[1] for row in source)
    return {'M': bins['*'], 'A': bins['+']+bins['-'], 'operations': len(source)}


def graph_metadata(source, supplied, final):
    defined = set(supplied)
    if len(defined) != len(supplied):
        raise ValueError('repeated supplied symbol')
    edges = {}
    constants = set()
    for name, op, a, b in source:
        if name in defined or op not in ('*', '+', '-'):
            raise ValueError('invalid definition')
        for value in (a, b):
            if isinstance(value, str):
                if value not in defined:
                    raise ValueError('forward or missing symbol ' + value)
            elif isinstance(value, dict):
                if set(value) != {'fixed'}:
                    raise ValueError('invalid fixed role')
                constants.add(value['fixed'])
            elif not isinstance(value, int):
                raise ValueError('invalid literal operand')
        defined.add(name)
        edges[name] = [a, b]
    live = set()
    pending = [final]
    while pending:
        name = pending.pop()
        if isinstance(name, str) and name not in live:
            live.add(name)
            pending.extend(edges.get(name, []))
    if set(edges)-live or set(supplied)-live:
        raise ValueError('dead graph rows or supplied ports')
    return {'all_rows_live': True, 'all_supplied_live': True,
            'topologically_closed': True, 'named_fixed_roles': sorted(constants)}


def sparse_graph(relators, native, coefficient_record):
    if relators < 0:
        raise ValueError('nonnegative fixed relator count required')
    r = relators
    m = 8+2*r
    ports = [[2,3,4,5,6,7], [2,3,4,5,6,7],
             [1,2,3,4,5,7], [1,2,3,4,5,7]]
    ports += [list(range(1,8)) for _ in range(4)]
    ports += [[4,5,6,7] for _ in range(2*r)]
    w = sum(len(v) for v in ports)
    ell = m+w+2
    rows, owners = [], []
    stage = 'input_and_mass'

    def emit(name, op, left, right):
        rows.append([name, op, left, right])
        owners.append(stage)
        return name

    def total(tag, fields):
        if not fields:
            raise ValueError('empty row sum')
        result = fields[0]
        for index in range(1, len(fields)):
            result = emit(tag+'_'+str(index), '+', result, fields[index])
        return result

    def fixed(name):
        return {'fixed': name}

    scaled = emit('program_scaled', '*', fixed('alpha'), 'x')
    tau = emit('program_tau', '+', scaled, fixed('gamma'))
    tau2 = emit('program_tau_squared', '*', tau, tau)
    mass_a = emit('initial_sum_a', '+', tau2, tau)
    mass_b = emit('initial_sum_b', '+', mass_a, 3)
    mass = emit('initial_mass', '+', mass_b, mass_b)
    initial = [3, tau, tau2, 2, tau, tau2, 1]
    histories = ['H_'+str(i) for i in range(1,8)]
    terminals = ['F_'+str(i) for i in range(1,7)]
    endpoint = terminals+[terminals[0]]
    selector_hats = ['selector_hat_'+str(s) for s in range(m)]
    selection_hats = {(s,i): 'selection_hat_'+str(s)+'_'+str(i)
                      for s in range(m) for i in ports[s]}

    stage = 'geometry_bounds_and_masks'
    selectors = [emit('selector_'+str(s), '-', selector_hats[s], 1) for s in range(m)]
    selected = {key: emit('selected_'+str(key[0])+'_'+str(key[1]), '-', name, 1)
                for key, name in selection_hats.items()}
    J = total('selector_checksum', selectors)
    D = emit('digit_height', '+', mass, 'height_slack')
    B = emit('cell_radix', '*', fixed('K'), D)
    bm1 = emit('cell_mask', '-', B, 1)
    pm1 = emit('lane_scale_minus_one', '*', bm1, J)
    P = emit('lane_scale', '+', pm1, 1)
    dm1 = emit('height_mask', '-', D, 1)
    mu = emit('aggregate_mask', '*', dm1, J)
    S = total('history_mass', histories)
    Ztot = total('selected_mass', list(selected.values()))
    bound_a = emit('joint_bound_a', '+', S, Ztot)
    bound = emit('joint_bound', '+', bound_a, 'global_slack')
    masks = [emit('letter_mask_'+str(s), '*', bm1, selectors[s]) for s in range(m)]
    pairs = [[bound, P]]
    lane_table = [[selectors[s], J, selectors[s]] for s in range(m)]
    lane_table += [[histories[i-1], masks[s], selected[s,i]]
                   for s in range(m) for i in ports[s]]
    lane_table += [[S, mu, S], [D, dm1, 0]]
    if len(lane_table) != ell:
        raise ValueError('lane partition')

    stage = 'three_sparse_packs'
    packs = []
    for side, tag in enumerate(('left', 'right', 'output')):
        top = ell-2 if side == 2 else ell-1
        acc = lane_table[top][side]
        for lane in range(top-1, -1, -1):
            shift = emit(tag+'_shift_'+str(lane), '*', acc, P)
            acc = emit(tag+'_join_'+str(lane), '+', shift, lane_table[lane][side])
        packs.append(acc)

    stage = 'fixed_native_power'
    power = P
    bits = bin(ell)[3:]
    for index, digit in enumerate(bits):
        power = emit('scale_square_'+str(index), '*', power, power)
        if digit == '1':
            power = emit('scale_multiply_'+str(index), '*', power, P)
    T = power

    stage = 'complete_native64'
    header = [
        ['pell_q', '*', 16, T],
        ['pell_scaled_A', '*', 16, packs[0]],
        ['pell_padded_A', '+', 'pell_scaled_A', 12],
        ['pell_scaled_B', '*', 16, packs[1]],
        ['pell_padded_B', '+', 'pell_scaled_B', 10],
        ['pell_scaled_Z', '*', 16, packs[2]],
        ['pell_F3', '+', 'pell_scaled_Z', 8],
    ]
    for row in header:
        emit(*row)
    def prefixed(value):
        if isinstance(value, str):
            if value in native['example']['parameters']:
                raise ValueError('native parameter escaped private header')
            return 'pell_'+value
        return value
    for name, op, a, b in native['example']['source'][7:64]:
        emit('pell_'+name, op, prefixed(a), prefixed(b))
    pairs += [[prefixed(a), prefixed(b)] for a,b in native['example']['comparisons']]

    stage = 'sparse_increment_rows'
    increments = []
    coefficient_occurrences = []
    for row_index in range(6):
        terms = []
        for slot, record in enumerate(coefficient_record['tables']):
            for port, value in enumerate(record['coefficients'][row_index], 1):
                if value == 0:
                    continue
                if port not in ports[slot]:
                    raise ValueError('nonzero paired term needs omitted selected port')
                name = emit('paired_term_'+str(row_index)+'_'+str(slot)+'_'+str(port),
                            '*', value, selected[slot,port])
                terms.append(name)
                coefficient_occurrences.append({'row': row_index+1, 'slot': slot,
                                                'port': port, 'coefficient': value})
        if row_index >= 3:
            for slot in range(8,m):
                for port in (4,5,6,7):
                    terms.append(emit('relator_term_'+str(row_index)+'_'+str(slot)+'_'+str(port),
                                      '*', fixed('relator_delta_'+str(slot)+'_'+str(row_index+1)+'_'+str(port)),
                                      selected[slot,port]))
        increments.append(total('increment_'+str(row_index+1), terms))
    if len(coefficient_occurrences) != 174:
        raise ValueError('paired literal term count')

    stage = 'fused_action_postprocessor'
    a,b,c,d,e,f = increments
    five = total('five_increment_sum', [a,b,c,e,f])
    d5 = emit('five_d', '*', 5, d)
    corrected_sum = emit('increment_weighted_sum', '+', five, d5)
    baseline = emit('baseline_mass', '*', fixed('kappa_minus_one'), S)
    shift_t = emit('offset_T', '-', baseline, corrected_sum)
    E = emit('eight_radices', '*', 8, B)
    BT = emit('scaled_T', '*', B, shift_t)
    Ed = emit('scaled_eight_d', '*', E, d)
    BU = emit('scaled_U', '+', BT, Ed)
    BV = emit('scaled_V', '+', BU, Ed)
    BT2 = emit('twice_scaled_T', '+', BT, BT)
    inner = []
    additions = [a,b,c,None,e,f,None]
    for i, increment in enumerate(additions):
        inner.append(histories[i] if increment is None else
                     emit('history_plus_increment_'+str(i+1), '+', histories[i], increment))
    offsets = [BV, BT, BT, BV, BT, BT2, BU]
    scaled_outputs = []
    for i in range(7):
        product = emit('scaled_history_'+str(i+1), '*', E, inner[i])
        scaled_outputs.append(emit('recurrence_lhs_'+str(i+1), '+', product, offsets[i]))

    stage = 'recurrence_right_sides'
    terminal_products = {F: emit('terminal_product_'+F, '*', P, F) for F in terminals}
    for i in range(7):
        temp = emit('recurrence_rhs_sum_'+str(i+1), '+', histories[i], terminal_products[endpoint[i]])
        rhs = emit('recurrence_rhs_'+str(i+1), '-', temp, initial[i])
        pairs.append([scaled_outputs[i], rhs])
    cut = len(rows)
    certificate = counts(rows)

    stage = 'single_polynomial_finalizer'
    squares = []
    for index,(left,right) in enumerate(pairs):
        residual = emit('comparison_residual_'+str(index), '-', left, right)
        squares.append(emit('comparison_square_'+str(index), '*', residual, residual))
    final = total('polynomial_sum', squares)
    auxiliaries = histories+terminals+selector_hats+list(selection_hats.values())
    auxiliaries += ['height_slack','global_slack']
    auxiliaries += ['pell_'+name for name in native['example']['auxiliaries']]
    metadata = graph_metadata(rows, ['x']+auxiliaries, final)
    lam = ell.bit_length()+ell.bit_count()-2
    wanted = {'M': 420+56*r+lam, 'A': 550+74*r,
              'operations': 970+130*r+lam}
    if certificate != wanted or len(pairs) != 23 or len(auxiliaries) != 96+10*r:
        raise ValueError('family ledger does not match emitted metadata')
    stages = {name: counts([row for row,owner in zip(rows,owners) if owner==name])
              for name in dict.fromkeys(owners)}
    return {'r': r, 'm': m, 'selected_ports': w, 'ell': ell, 'lambda': lam,
            'ordinary_parameters': ['x'], 'ordinary_domain': 'positive integer x',
            'positive_auxiliaries': auxiliaries, 'retained_coordinate_ports': ports,
            'source': rows, 'certificate_prefix_rows': cut, 'comparisons': pairs,
            'output': final, 'lanes_in_order': lane_table,
            'ports': {'initial': initial, 'terminal': endpoint, 'J':J, 'D':D, 'B':B,
                      'P':P, 'S':S, 'Ztot':Ztot, 'T':T, 'native_packs':packs,
                      'six_increments':increments, 'scaled_action_outputs':scaled_outputs},
            'paired_coefficient_occurrences': coefficient_occurrences,
            'certificate_ledger': certificate, 'polynomial_ledger': counts(rows),
            'equations': len(pairs), 'witnesses': len(auxiliaries),
            'stages': stages, 'static_checks': metadata}


def main():
    parsed, inputs = {}, []
    for key,(name,pin) in INPUTS.items():
        path = WIP/name
        raw = path.read_bytes()
        if sha(raw) != pin:
            raise ValueError('changed input bytes '+name)
        parsed[key] = json.loads(raw)
        inputs.append({'path': str(path.relative_to(WORKSPACE)), 'sha256':pin,
                       'bytes':len(raw), 'role':'inert literal data only'})
    if [t['letter'] for t in parsed['paired']['tables']] != ['a+','a-','b+','b-','z1+','z1-','z2+','z2-']:
        raise ValueError('coefficient slot order changed')
    records, examples = [], []
    for r in (0,1,2,3,4,8):
        graph = sparse_graph(r, parsed['native'], parsed['paired'])
        records.append({key: graph[key] for key in ('r','m','selected_ports','ell','lambda','certificate_ledger','polynomial_ledger','equations','witnesses')})
        if r in (0,1,4):
            examples.append(graph)
    receipt = {
        'status':'original metadata-only sparse source emission PASS',
        'emitter_sha256':sha(Path(__file__).read_bytes()), 'inputs':inputs,
        'fixed_data_recipe':[
            'r fixed presentation relators; eight paired letters as pinned table; two signed slots per relator',
            'relator_delta roles are actual integer (S(rho(R_j)^+/-1)-I3) decoder coefficients on ports4,5,6,7',
            'one common kappa from the positive7 lift; kappa_minus_one is its fixed predecessor numeral',
            'fixed dyadic K greater than m and common positive-letter column sum C=8*kappa',
            'alpha,gamma are positive compiler numerals; use inherited program slice values for universal application',
            'all named coefficient roles are fixed numerals, not positive witnesses or arbitrary untyped parameters'],
        'generic_ledger':{'certificate':'(420+56r+lambda)M+(550+74r)A',
                          'ell':'62+10r', 'lambda':'floor(log2 ell)+popcount(ell)-1',
                          'equations':23,'positive_witnesses':'96+10r',
                          'sos_increment':'23M+45A','polynomial_operations':'1038+130r+lambda'},
        'static_shape_censuses':records, 'examples':examples,
        'execution_scope':{'source_arithmetic_evaluated':False,'saved_coefficient_arithmetic_evaluated':False,
                           'degree_propagation':False,'frozen_helper_executed':False,
                           'original_metadata_emission_and_checks_only':True,
                           'numerical_universal_relator_list_supplied':False}}
    destination = Path('/tmp/positive7_complete_sparse_compiler_root.json')
    if destination.exists():
        raise ValueError('refuse to overwrite receipt')
    destination.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'receipt':str(destination),'sha256':sha(destination.read_bytes()),
                      'static_shape_censuses':records},indent=2))


if __name__ == '__main__':
    main()
