#!/usr/bin/env python3
"""Build/check the two shared-reset-arc variants using only literal JSON inputs.
Standard library only. No imports or execution of parent project code.
"""
from pathlib import Path
from collections import Counter
from copy import deepcopy
import hashlib, json
HERE = Path(__file__).resolve().parent
BASE = HERE.parent


def read(path):
    return json.loads(path.read_text())


def write(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def clean(m):
    return {p: n for p, n in m.items() if n}


def initial(net, params):
    return clean({p: sum(c * (1 if k == 'constant' else params[k])
                        for k, c in a.items())
                  for p, a in net['initial_affine'].items()})


def fire(net, marking, t):
    assert all(marking.get(p, 0) >= v for p, v in t['pre'].items()), t['name']
    m = dict(marking)
    for p, v in t['pre'].items():
        m[p] = m.get(p, 0) - v
    loss = sum(m.get(p, 0) for p in t['reset'])
    for p in t['reset']:
        m[p] = 0
    for p, v in t['post'].items():
        m[p] = m.get(p, 0) + v
    assert all(type(v) is int and v >= 0 for v in m.values())
    return clean(m), loss


def compile_shared(direct):
    regs = direct['data_places'][:-2]
    zeros = [t for t in direct['transitions'] if t['kind'] == 'SUB_ZERO']
    gates = ['q:SHARED_GATE_' + p for p in regs]
    posts = ['q:SHARED_POST_' + p for p in regs]
    markers = ['marker:' + t['source_control'] for t in zeros]
    assert not set(gates + posts + markers) & set(direct['places'])
    net = deepcopy(direct)
    net['format'] = 'shared-reset-arcs-unit-net-v1'
    net['places'] += gates + posts + markers
    net['control_places'] += gates + posts
    net['controls'] += [p[2:] for p in gates + posts]
    net['resource_places'] = list(direct['data_places'])
    net['marker_places'] = markers
    # Markers are NOT projected away by the direct net's data-only certificate.
    net['data_places'] += markers
    net['direct_control_places'] = list(direct['control_places'])
    net['counter_places'] = regs
    net['transitions'] = []
    expansion = {}
    for t in direct['transitions']:
        if t['kind'] != 'SUB_ZERO':
            net['transitions'].append(deepcopy(t))
            expansion[t['name']] = [t['name']]
            continue
        assert t['reset'] == [t['reset'][0]]
        p = t['reset'][0]
        assert p in regs and t['pre'] == {'q:' + t['source_control']: 1}
        assert t['post'] == {'q:' + t['target_control']: 1}
        label = t['source_control']
        gate, post, marker = 'q:SHARED_GATE_' + p, 'q:SHARED_POST_' + p, 'marker:' + label
        dispatch = {'name': label + ':dispatch', 'pre': dict(t['pre']),
                    'post': {gate: 1, marker: 1}, 'reset': [],
                    'source_control': label, 'target_control': gate[2:],
                    'kind': 'ZERO_DISPATCH', 'original_zero': t['name'],
                    'tested_counter': p, 'marker': marker}
        ret = {'name': label + ':return', 'pre': {post: 1, marker: 1},
               'post': dict(t['post']), 'reset': [],
               'source_control': post[2:], 'target_control': t['target_control'],
               'kind': 'ZERO_RETURN', 'original_zero': t['name'],
               'tested_counter': p, 'marker': marker}
        net['transitions'] += [dispatch, ret]
        expansion[t['name']] = [dispatch['name'], 'shared_reset_' + p, ret['name']]
    for p in regs:
        net['transitions'].append({'name': 'shared_reset_' + p,
            'pre': {'q:SHARED_GATE_' + p: 1},
            'post': {'q:SHARED_POST_' + p: 1}, 'reset': [p],
            'source_control': 'SHARED_GATE_' + p,
            'target_control': 'SHARED_POST_' + p,
            'kind': 'SHARED_RESET', 'tested_counter': p})
    net['zero_expansion'] = expansion
    net['projection_warning'] = ('data_places includes all ordinary marker places. '
        'The original counter/reserve/budget-only control projection does not apply '
        'to this net without a separate phased proof.')
    return net


def ledger(net):
    ts = net['transitions']
    return {'places': len(net['places']), 'data_places': len(net['data_places']),
      'resource_places': len(net.get('resource_places', net['data_places'])),
      'marker_places': len(net.get('marker_places', [])),
      'control_places': len(net['control_places']), 'transitions': len(ts),
      'ordinary_input_arcs': sum(len(t['pre']) for t in ts),
      'ordinary_output_arcs': sum(len(t['post']) for t in ts),
      'ordinary_arcs': sum(len(t['pre']) + len(t['post']) for t in ts),
      'reset_arcs': sum(len(t['reset']) for t in ts),
      'all_arcs': sum(len(t['pre']) + len(t['post']) + len(t['reset']) for t in ts),
      'max_input_weight': max(v for t in ts for v in t['pre'].values()),
      'max_output_weight': max(v for t in ts for v in t['post'].values()),
      'max_total_incidence_transition': max(len(t['pre']) + len(t['post']) + len(t['reset']) for t in ts),
      'distinct_reset_places': sorted({p for t in ts for p in t['reset']}),
      'transition_kinds': dict(Counter(t['kind'] for t in ts))}


def verify_structure(direct, net):
    ds = {t['name']: t for t in direct['transitions']}
    ts = {t['name']: t for t in net['transitions']}
    assert len(ds) == len(direct['transitions']) and len(ts) == len(net['transitions'])
    assert len(net['places']) == len(set(net['places']))
    assert set(net['data_places']).isdisjoint(net['control_places'])
    assert set(net['data_places']) | set(net['control_places']) == set(net['places'])
    assert direct['initial_affine'] == net['initial_affine'] and direct['target'] == net['target']
    assert direct['parameters'] == net['parameters']
    for t in net['transitions']:
        assert all(v == 1 for v in list(t['pre'].values()) + list(t['post'].values()))
        assert set(t['pre']) | set(t['post']) | set(t['reset']) <= set(net['places'])
        assert sum(p in net['control_places'] for p in t['pre']) == 1
        assert sum(p in net['control_places'] for p in t['post']) == 1
        assert not set(t['reset']) & set(net['marker_places'])
    for name, word in net['zero_expansion'].items():
        old = ds[name]
        if old['kind'] != 'SUB_ZERO':
            assert word == [name] and ts[name] == old
            continue
        d, z, r = map(ts.__getitem__, word)
        p = old['reset'][0]
        marker = 'marker:' + old['source_control']
        assert d['pre'] == old['pre'] and r['post'] == old['post']
        assert d['post'] == {'q:SHARED_GATE_' + p: 1, marker: 1}
        assert z['pre'] == {'q:SHARED_GATE_' + p: 1}
        assert z['post'] == {'q:SHARED_POST_' + p: 1} and z['reset'] == [p]
        assert r['pre'] == {'q:SHARED_POST_' + p: 1, marker: 1}
        assert d['reset'] == r['reset'] == []
    counts = Counter(t['kind'] for t in direct['transitions'])
    I, S, r = counts['INC'], counts['SUB_ZERO'], len(net['counter_places'])
    q = I + S
    a, old = ledger(net), ledger(direct)
    assert a['places'] == q + 4*r + S + 5
    assert a['transitions'] == I + 3*S + 3*r + 4
    assert a['ordinary_arcs'] == old['ordinary_arcs'] + 4*S + 2*r
    assert a['reset_arcs'] == r
    assert a['max_total_incidence_transition'] <= 4
    return dict(q=q, I=I, S=S, r=r)


def invariant(net, marking, loss):
    assert sum(marking.get(p, 0) for p in net['control_places']) == 1
    old = sum(marking.get(p, 0) for p in net['direct_control_places'])
    pending = [(p, marking.get(p, 0)) for p in net['marker_places'] if marking.get(p, 0)]
    assert sum(v for _, v in pending) == 1 - old
    if pending:
        assert len(pending) == 1 and pending[0][1] == 1
        label = pending[0][0][len('marker:'):]
        by = {t['name']: t for t in net['transitions']}
        p = by[label + ':dispatch']['tested_counter']
        assert marking.get('q:SHARED_GATE_' + p, 0) + marking.get('q:SHARED_POST_' + p, 0) == 1
    assert marking.get('budget', 0) - marking.get('reserve', 0) - sum(marking.get(p, 0) for p in net['counter_places']) == loss


def project_marking(net, marking):
    """Exact stuttering decoder at every reachable marking, including open blocks."""
    out = {p: v for p, v in marking.items() if p in net['resource_places'] or p in net['direct_control_places']}
    pending = [p for p in net['marker_places'] if marking.get(p, 0)]
    if pending:
        label = pending[0][len('marker:'):]
        by = {t['name']: t for t in net['transitions']}
        d, ret = by[label + ':dispatch'], by[label + ':return']
        p = d['tested_counter']
        ctrl = d['source_control'] if marking.get('q:SHARED_GATE_' + p, 0) else ret['target_control']
        out['q:' + ctrl] = 1
    return clean(out)


def replay_main(direct, net):
    saved = read(BASE / 'accepting_reset_trace.json')
    params, dmark = saved['parameters'], initial(direct, saved['parameters'])
    mark = initial(net, params)
    ts = {t['name']: t for t in net['transitions']}
    ds = {t['name']: t for t in direct['transitions']}
    index = {t['name']: j for j, t in enumerate(net['transitions'])}
    trace, decoded, loss, zero, source_len, masses = [], [], 0, 0, 0, [sum(dmark.get(p, 0) for p in net['counter_places'])]
    for old_record in saved['trace']:
        old_t = ds[old_record['name']]
        assert clean(old_record['old']) == dmark
        direct_new, old_loss = fire(direct, dmark, old_t)
        assert direct_new == clean(old_record['new']) and old_loss == old_record['reset_loss']
        word = net['zero_expansion'][old_t['name']]
        if old_t['kind'] == 'SUB_ZERO': zero += 1
        if old_t['kind'] in ['INC', 'SUB_POS', 'SUB_ZERO']:
            source_len += 1
            masses.append(sum(direct_new.get(p, 0) for p in net['counter_places']))
        for name in word:
            t = ts[name]
            old_projection = project_marking(net, mark)
            new, dloss = fire(net, mark, t)
            loss += dloss
            invariant(net, new, loss)
            new_projection = project_marking(net, new)
            if t['kind'] in ['ZERO_DISPATCH', 'ZERO_RETURN']:
                assert old_projection == new_projection and dloss == 0
            else:
                original = t['name'] if t['kind'] != 'SHARED_RESET' else old_t['name']
                pnew, ploss = fire(direct, old_projection, ds[original])
                assert pnew == new_projection and ploss == dloss
                decoded.append(original)
            trace.append({'step': len(trace), 'transition': index[name], 'name': name,
                          'old': mark, 'new': new, 'reset_loss': dloss, 'cumulative_loss': loss})
            mark = new
        assert mark == direct_new
        dmark = direct_new
    assert mark == net['target'] and loss == 0 and zero == 29
    assert decoded == [t['name'] for t in saved['trace']]
    assert len(trace) == len(saved['trace']) + 2*zero == 446
    counts = Counter(t['name'] for t in saved['trace'])
    F = sum(saved['trace'][-1]['old'].get(p, 0) for p in net['counter_places'])
    source_records = [x for x in saved['trace'] if ds[x['name']]['kind'] in ['INC', 'SUB_POS', 'SUB_ZERO']]
    F = sum(source_records[-1]['new'].get(p, 0) for p in net['counter_places'])
    C, H = sum(params.values()), max(masses)
    assert source_len == 328 and H == 25 and F == 11
    min_duration = source_len + F - C + 2*H + len(net['counter_places']) + 2 + 2*zero
    assert min_duration == len(trace) and saved['fuel'] == H-C == 19
    artifact = {'parameters': params, 'fuel': saved['fuel'], 'length': len(trace),
        'source_instructions': source_len, 'source_zero_branches': zero,
        'peak_counter_mass': H, 'terminal_counter_mass': F, 'cumulative_loss': loss,
        'trace': trace, 'decoded_direct_word': decoded}
    write(HERE / 'three-counter/accepting_reset_trace_N446.json', artifact)
    return {k:v for k,v in artifact.items() if k not in ['trace', 'decoded_direct_word']}


def transform_schema(schema, direct):
    """Transform only an unpadded canonical-minimum source schema.

    Source branch order must agree with direct-net source-transition order.
    Validate the E/Q/D coefficient maps at every step, using the direct net's
    source control codes, and validate omitted zero-branch tested coordinates.
    This API deliberately rejects all-duration/padded inputs rather than
    relabeling their zero set as a canonical minimum certificate.
    """
    if schema.get('format') != 'canonical-minimum-reset-outcome-v1':
        raise ValueError('Expected an unpadded canonical-minimum-reset-outcome-v1 schema')
    if 'padding_index' in schema or 'padding_index' in schema.get('variables', {}):
        raise ValueError('Padded/all-duration schemas are not supported')
    duration_rows = [row for row in schema.get('affine_squares', [])
                     if row.get('name') == 'minimum_reset_duration']
    if len(duration_rows) != 1:
        raise ValueError('Expected exactly one minimum_reset_duration affine-square row')
    h = schema['external_time']
    if type(h) is not int or h < 1:
        raise ValueError('Expected a positive exact source-instruction horizon')
    stride = schema['variables']['per_step']
    branches = [t for t in direct['transitions'] if t['kind'] in ['INC', 'SUB_POS', 'SUB_ZERO']]
    if len(branches) != schema['variables']['branch_count']:
        raise ValueError('Source branch count does not match direct net')
    labels = list(dict.fromkeys(t['source_control'] for t in branches))
    q = len(labels)
    if direct['controls'][:q] != labels:
        raise ValueError('Direct control ordering does not match source label ordering')
    code = {label: j for j, label in enumerate(direct['controls'][:q+1])}
    enter = [t for t in direct['transitions'] if t['name'] == 'enter']
    if len(enter) != 1 or schema['entry_code'] != code[enter[0]['target_control']]:
        raise ValueError('Schema entry control code does not match direct net')
    if schema['halt_code'] != q or schema['terminal_code'] != q:
        raise ValueError('Schema halt/terminal code does not match direct source numbering')
    def normalized(terms):
        coefficients = Counter()
        for index, coefficient in terms:
            coefficients[index] += coefficient
        return {index: value for index, value in coefficients.items() if value}
    for j in range(h):
        for name, attr in [('E', None), ('Q', 'source_control'), ('D', 'target_control')]:
            expected = {j*stride+b: 1 if attr is None else code[t[attr]]
                        for b,t in enumerate(branches)
                        if attr is None or code[t[attr]] != 0}
            form = schema['linear_forms'].get(f'{name}:{j}')
            if form is None or normalized(form) != expected:
                raise ValueError(f'Source branch/control ordering mismatch in {name}:{j}')
    out = deepcopy(schema)
    zeros = [b for b, t in enumerate(branches) if t['kind'] == 'SUB_ZERO']
    for b, t in enumerate(branches):
        nulls = [i for i, v in enumerate(schema['variables']['base_offsets_by_branch'][b]) if v is None]
        assert len(nulls) == (1 if t['kind'] == 'SUB_ZERO' else 0)
        if nulls: assert direct['data_places'][nulls[0]] == t['reset'][0]
    out['linear_forms']['SOURCE_ZERO_COUNT'] = [[j*stride+b, 1] for j in range(h) for b in zeros]
    duration = [row for row in out['affine_squares'] if row['name'] == 'minimum_reset_duration']
    assert len(duration) == 1  # already validated before any transformation
    duration[0]['name'] = 'minimum_shared_reset_duration'
    duration[0]['affine']['forms'].append(['SOURCE_ZERO_COUNT', -2])
    out['format'] = 'canonical-minimum-shared-reset-outcome-v1'
    out['scope'] = ('Externally fixed exact SOURCE-instruction horizon h, not shared-net firing horizon. '
        'Same witness coordinates, equations and products as the direct canonical-peak schema; '
        'duration affine row is reduced by twice the selected source zero-branch count. '
        'This is a canonical outcome projection, not a generic marker-free trace certificate.')
    out['shared_reset_metadata'] = {'extra_firings_per_source_zero': 2,
        'source_zero_branch_selector_offsets': zeros,
        'witness_count_unchanged': True, 'equation_count_unchanged': True,
        'no_new_independent_variable_for_Z': True,
        'input_mode': 'validated unpadded canonical minimum',
        'source_branch_order': 'validated E/Q/D coefficient maps against direct source-transition and control order at every step',
        'marker_projection': 'Not used: certificate is indexed by decoded source instructions.'}
    assert out['variables'] == schema['variables'] and out['ledger'] == schema['ledger']
    assert out['quadratic_products'] == schema['quadratic_products']
    assert len(out['affine_squares']) == len(schema['affine_squares'])
    return out


def verify_peak_witness(net, h1):
    """Evaluate the entire h=328 polynomial from h=1 local form templates.
    No enormous schema is materialized; all affine squares/products are checked.
    """
    old = read(BASE / 'accepting_peak_witness.json')
    h = old['external_source_instructions']
    x = dict(old['nonzero_coordinates'])
    stride, r = h1['variables']['per_step'], h1['variables']['register_count']
    base = h*stride
    assert old['variable_count'] == h*(stride+2)
    params = dict(old['parameters'], N=446)
    all_forms, squares, products, Z = [], 0, 0, 0
    def v(j, idx):
        return x.get(j*stride+idx if idx < stride else base+2*j+idx-stride, 0)
    def affine(a, j, forms):
        return (a['constant'] + sum(c*forms[name] for name,c in a['forms'])
            + sum(c*v(j, idx) for idx,c in a['variables'])
            + sum(c*params[name] for name,c in a['parameters']))
    for j in range(h):
        f = {name:sum(c*v(j, idx) for idx,c in terms) for name,terms in h1['linear_forms'].items()}
        all_forms.append(f)
        assert f['E:0'] == 1
        assert f['Q:0'] == (h1['entry_code'] if j == 0 else all_forms[j-1]['D:0'])
        for i in range(r):
            expected = params[['L','R'][i]] if j == 0 and i < 2 else (0 if j == 0 else all_forms[j-1][f'NEW{i}:0'])
            assert f[f'OLD{i}:0'] == expected
        C = params['L'] + params['R']
        previous_peak = C if j == 0 else sum(all_forms[j-1][f'NEW{i}:0'] for i in range(r)) + v(j-1,stride+1)
        peak = previous_peak + v(j,stride) - sum(f[f'NEW{i}:0'] for i in range(r)) - v(j,stride+1)
        assert peak == 0
        prefix_peak = C + sum(v(k,stride) for k in range(j+1)) - sum(f[f'NEW{i}:0'] for i in range(r)) - v(j,stride+1)
        assert prefix_peak == 0
        squares += r+3
        Z += f['SOURCE_ZERO_COUNT']
        for product in h1['quadratic_products']:
            left, right = affine(product['left'],j,f), affine(product['right'],j,f)
            assert left >= 0 and right >= 0 and left*right == 0, product['name']
            products += 1
    assert all_forms[-1]['D:0'] == h1['halt_code']
    C = params['L'] + params['R']
    F = sum(all_forms[-1][f'NEW{i}:0'] for i in range(r))
    residual = params['N'] + C - 3*F - 2*v(h-1,stride+1) - h-r-2 - 2*Z
    assert residual == 0 and Z == 29, (residual, Z, C, F, sum(v(j,stride+1) for j in range(h)))
    squares += 2
    assert squares == 6*h+2 and products == 762*h
    out = deepcopy(old)
    out['parameters']['N'] = 446
    out['shared_reset_duration_adjustment'] = {'source_zero_branches':29, 'added_firings':58}
    write(HERE / 'three-counter/accepting_peak_witness_N446.json', out)
    return {'h': h, 'natural_witnesses': len(range(old['variable_count'])),
        'affine_squares_evaluated': squares, 'quadratic_products_evaluated': products,
        'polynomial_value':0, 'source_zero_count_from_selectors':Z,
        'same_sparse_witness_coordinates_as_direct': True}


def verify_prime_templates_and_count():
    root = BASE / 'two-counter/source'
    virtual, physical, certs = read(root/'virtual3.json'), read(root/'literal2.json'), read(root/'macro_certificates.json')['prime_macros']
    expected = {}
    cuts = physical['virtual_cuts']
    dst = lambda l: physical['halt'] if l == virtual['halt'] else cuts[l]
    for c in certs:
        l, p, pr = c['virtual_label'], c['prime'], c['prefix']
        row = virtual['rows'][l]
        assert c['op'] == row[0] and p == [2,3,5][row[1]]
        if row[0] == 'ADD':
            expected[pr+'drain'] = ['SUB',0,pr+'mul0',pr+'restore']
            for i in range(p): expected[pr+'mul'+str(i)] = ['ADD',1,pr+'mul'+str(i+1) if i+1 < p else pr+'drain']
            expected[pr+'restore'] = ['SUB',1,pr+'put',dst(row[2])]
            expected[pr+'put'] = ['ADD',0,pr+'restore']
            assert cuts[l] == pr+'drain'
        else:
            for i in range(p):
                expected[pr+'rem'+str(i)] = ['SUB',0,pr+'rem'+str(i+1) if i+1 < p else pr+'group',pr+'quo' if i == 0 else pr+f'r{i}_drain']
            expected[pr+'group'] = ['ADD',1,pr+'rem0']
            expected[pr+'quo'] = ['SUB',1,pr+'qput',dst(row[2])]
            expected[pr+'qput'] = ['ADD',0,pr+'quo']
            for a in range(1,p):
                expected[pr+f'r{a}_drain'] = ['SUB',1,pr+f'r{a}_put0',pr+f'r{a}_tail0']
                for i in range(p): expected[pr+f'r{a}_put{i}'] = ['ADD',0,pr+f'r{a}_put{i+1}' if i+1 < p else pr+f'r{a}_drain']
                for i in range(a): expected[pr+f'r{a}_tail{i}'] = ['ADD',0,pr+f'r{a}_tail{i+1}' if i+1 < a else dst(row[3])]
            assert cuts[l] == pr+'rem0'
    assert expected == physical['rows']
    # Execute only 328 small virtual steps; analytically account for huge prime macros.
    state, regs, n, H, pos, inc, zero, rows = virtual['entry'], [6,0,0], 64,64,0,0,0,[]
    while state != virtual['halt']:
        assert len(rows) < 10000
        op,i,*targets = virtual['rows'][state]
        p = [2,3,5][i]
        oldn = n
        if op == 'ADD':
            ni, np = 2*p*n, (p+1)*n
            n *= p
            regs[i] += 1
            target = targets[0]
            H = max(H,n)
        else:
            q,a = divmod(n,p)
            if a == 0:
                ni, np = 2*q, n+q
                n = q
                assert regs[i] > 0
                regs[i] -= 1
                target = targets[0]
            else:
                ni = np = n+q
                assert regs[i] == 0
                target = targets[1]
        assert n == 2**regs[0]*3**regs[1]*5**regs[2]
        inc += ni; pos += np; zero += 2
        rows.append({'virtual_step':len(rows),'label':state,'encoded_A_before':oldn,
            'encoded_A_after':n,'physical_ADD':ni,'physical_SUB_positive':np,
            'physical_SUB_zero':2,'physical_instructions':ni+np+2,'mass_peak_through_step':H})
        state = target
    h = inc+pos+zero
    reference = read(root/'accepting_example.json')
    assert inc == reference['physical_ADD'] and pos == reference['physical_SUB_positive']
    assert zero == reference['physical_SUB_zero'] == 656 and h == reference['physical_instructions']
    assert H == reference['largest_A_at_virtual_cuts']
    assert len(rows) == reference['virtual_instructions'] == 328
    direct = h+n-64+2*H+4
    shared = direct+2*zero
    assert shared == 857788604036217896
    out = {'input':{'raw_A':64},'virtual_instructions':len(rows),'physical_source_instructions':h,
      'physical_ADD':inc,'physical_SUB_positive':pos,'physical_SUB_zero':zero,
      'peak_counter_mass':H,'terminal_counter_mass':n,'minimum_fuel':H-64,
      'direct_minimum_duration':direct,'shared_minimum_duration':shared,
      'added_shared_firings':2*zero,'literal_physical_rows_template_checked':len(expected),
      'macro_steps':rows,'giant_physical_trace_enumerated':False}
    write(HERE/'two-counter/accepting_macro_count_A64.json',out)
    return {k:v for k,v in out.items() if k != 'macro_steps'}


def verify_schema_rejections(direct, schema):
    cases = []
    bad = deepcopy(schema)
    bad['format'] = 'canonical-all-reset-durations-natural-v1'
    cases.append(('all-duration format', bad))
    bad = deepcopy(schema)
    bad['variables']['padding_index'] = bad['variables']['count']
    cases.append(('padding coordinate', bad))
    bad = deepcopy(schema)
    bad['padding_index'] = bad['variables']['count']
    cases.append(('top-level padding coordinate', bad))
    bad = deepcopy(schema)
    bad['affine_squares'] = [r for r in bad['affine_squares'] if r['name'] != 'minimum_reset_duration']
    cases.append(('missing duration row', bad))
    bad = deepcopy(schema)
    bad['affine_squares'].append(deepcopy([r for r in bad['affine_squares'] if r['name'] == 'minimum_reset_duration'][0]))
    cases.append(('duplicate duration row', bad))
    for name in ['E:0', 'Q:0', 'D:0']:
        bad = deepcopy(schema)
        bad['linear_forms'][name][0][1] += 1
        cases.append(('mismatched '+name+' branch map', bad))
    rejected = []
    for name, bad in cases:
        try:
            transform_schema(bad, direct)
        except ValueError:
            rejected.append(name)
        else:
            raise AssertionError('Schema API accepted invalid input: ' + name)
    return rejected


def main():
    receipt = {'status':'passed','inputs':{},'variants':{}}
    for name, parent in [('three-counter',BASE),('two-counter',BASE/'two-counter')]:
        path = parent/'reset_net.json'
        direct = read(path)
        net = compile_shared(direct)
        counts = verify_structure(direct,net)
        out = HERE/name
        write(out/'reset_net.json',net)
        write(out/'net_ledger.json',ledger(net))
        direct_schema = read(parent/'canonical_peak_schema_h1.json')
        schema = transform_schema(direct_schema,direct)
        write(out/'canonical_peak_schema_h1.json',schema)
        receipt['inputs'][str(path.relative_to(BASE))] = sha(path)
        receipt['inputs'][str((parent/'canonical_peak_schema_h1.json').relative_to(BASE))] = sha(parent/'canonical_peak_schema_h1.json')
        receipt['variants'][name] = {'source_counts':counts,'ledger':ledger(net),
            'canonical_peak_h1_ledger':schema['ledger'],
            'initial_affine_preserved':True,'structure_check':'passed'}
        if name == 'three-counter':
            receipt['schema_api_rejection_tests'] = verify_schema_rejections(direct, direct_schema)
            receipt['three_counter_trace'] = replay_main(direct,net)
            receipt['three_counter_peak_polynomial'] = verify_peak_witness(net,schema)
    receipt['two_counter_macro_example'] = verify_prime_templates_and_count()
    write(HERE/'verification_receipt.json',receipt)
    print(json.dumps(receipt,indent=2))


if __name__ == '__main__':
    main()
