# Portable locally authored code; upstream Python is never imported or executed.
# See PROVENANCE.json and PORTABILITY.md for all transformations.
"""Paid ordinary-input and exact unary queue loaders.

Only JSON data from the pinned recoder130 receipt is loaded. No upstream
Python is imported or executed. Every native recoder comparison is retained.
All supplied inputs are positive integers. Six external ports are x and the
five program-slice parameters; the other 106 coordinates are existential.
"""
from pathlib import Path
import hashlib
import json
HERE = Path(__file__).resolve().parent
RECEIPT_SHA256 = '175c498990a8e63de7a91d1e3d321ef90a19f129f305074f0c6de10967d0a182'
EXTERNAL_NAMES = ('x', 'a_e', 'p_e', 's_e', 'C_e', 'L_e')
CANONICAL_NS = 'canonical_input_bits'
EXPONENT_NS = 'unrestricted_tape_exponent'

def _require(condition, message):
    if not condition:
        raise ValueError(message)

def frozen_recoder():
    """Read the authenticated source as inert data and validate its shape."""
    data = (HERE / 'input_recoder130_receipt.json').read_bytes()
    _require(hashlib.sha256(data).hexdigest() == RECEIPT_SHA256, 'recoder130 receipt SHA-256 mismatch')
    packet = json.loads(data)['certificate']
    _require(packet['parameters'] == ['x', 'z'], 'unexpected recoder ports')
    _require(len(packet['source']) == 130 and len(packet['comparisons']) == 34, 'incomplete recoder source/comparisons')
    _require(len(packet['auxiliaries']) == len(set(packet['auxiliaries'])) == 49, 'incomplete recoder auxiliary set')
    _require(packet['source'][:3] == [['q2', '*', 'q', 'q'], ['Q', '*', 'q2', 'q2'], ['B', '*', 8, 'Q']], 'unexpected recoder prefix')
    _require(not any(('q2' in row[2:] for row in packet['source'][3:])), 'private old power register has another consumer')
    known = set(packet['parameters'] + packet['auxiliaries'])
    for name, op, left, right in packet['source']:
        _require(name not in known and op in ('+', '-', '*'), 'malformed source')
        _require(all((isinstance(v, int) or v in known for v in (left, right))), 'non-topological source')
        known.add(name)
    _require(all((a in known and b in known for a, b in packet['comparisons'])), 'unknown comparison port')
    return packet

def build_recoder(dag, width, namespace, input_port, output_port):
    """Emit the complete generic k>=4 recoder, without exponent restrictions.

    The width is fixed source data, never a variable exponent. The supplied
    input/output may be positive computed ports; the native auxiliary set is
    always fresh and entirely positive. The result includes all 34 pairs.
    """
    _require(isinstance(width, int) and (not isinstance(width, bool)) and (width >= 4), 'generic recoder width must be a fixed integer >=4')
    packet = frozen_recoder()
    aux = {name: dag.input(namespace + '__' + name) for name in packet['auxiliaries']}
    env = dict(aux, x=input_port, z=output_port)
    env['Q'] = dag.power(env['q'], width)
    env['B'] = dag.mul(dag.recipe('pow2', width - 1), env['Q'])

    def operand(value):
        return dag.const(value) if isinstance(value, int) else env[value]
    operations = {'+': dag.add, '-': dag.sub, '*': dag.mul}
    for name, op, left, right in packet['source'][3:]:
        env[name] = operations[op](operand(left), operand(right))
    pairs = [(env[left], env[right]) for left, right in packet['comparisons']]
    return {'width': width, 'namespace': namespace, 'auxiliaries': aux, 'registers': env, 'residuals': pairs, 'comparison_names': [namespace + ':' + a + '=' + b for a, b in packet['comparisons']], 'raw_source_operations': 128 + width.bit_length() + width.bit_count() - 2, 'power_chain_length': width.bit_length() + width.bit_count() - 2}

def literal_pair_recipe(dag, literal_genera):
    """Fixed V=val_LSB(E(b:00) E(x:00)), represented without expansion."""
    genera = literal_genera.get('genera', literal_genera)
    alphabet = genera['alphabet']
    size = len(alphabet)
    _require(size == 1013 and [s['id'] for s in alphabet] == list(range(size)), 'expected complete literal normalized U15 alphabet with 1013 symbols')
    start = genera['canonical_symbols']['0']
    y, z = (start['b'], start['x'])
    _require((y, z) == (300, 539), 'unexpected literal repeated-pair IDs')
    _require(alphabet[y]['name'] == 'b:00' and alphabet[z]['name'] == 'x:00', 'repeated pair does not match the literal initial source word')
    _require(alphabet[y]['width'] == alphabet[z]['width'] == 1, 'the two original input symbols must have width one')
    a = 28 * (size + 1)
    b = 7 * a
    k = 2 * b

    def gval(n):
        return dag.recipe('mul', dag.const(2), dag.recipe('geom4', n))
    middle = dag.recipe('mul', dag.recipe('pow2', 2 * a - 5), gval(7))
    tail = dag.recipe('mul', dag.recipe('pow2', 2 * a + 10), gval(a - 4))
    base = dag.recipe('mul', dag.recipe('pow2', 7), dag.recipe('add', dag.recipe('add', gval(a - 3), middle), tail))
    first = dag.recipe('mul', base, dag.recipe('pow2', 14 * y))
    second = dag.recipe('mul', base, dag.recipe('pow2', b + 14 * z))
    value = dag.recipe('add', first, second)
    return {'V': value, 'K': dag.recipe('pow2', k), 'K_minus_one': dag.recipe('sub', dag.recipe('pow2', k), dag.const(1)), 'alphabet_size': size, 'a': a, 'symbol_width': b, 'pair_width': k, 'pair_symbol_ids': [y, z], 'E_base': base}

def build(dag, literal_genera, external=None):
    """Compose both full recoders and the exact input loader.

    Return value and width ports plus comparison pairs. The caller MUST put
    every pair and the native-width equality into its integer-unit finalizer.
    Program parameters are external coordinates fixed per represented set,
    never existential choices depending on x. This function emits no native
    history or finalizer and makes no universality cost claim on its own.
    """
    external = {} if external is None else dict(external)
    _require(not set(external) - set(EXTERNAL_NAMES), 'unknown external port')
    ext = {name: external[name] if name in external else dag.input(name, role='external') for name in EXTERNAL_NAMES}
    one = dag.const(1)
    u = dag.add(ext['x'], one)
    spread = dag.input(CANONICAL_NS + '__spread')
    canonical = build_recoder(dag, 32, CANONICAL_NS, u, spread)
    c = canonical['registers']
    residuals = list(canonical['residuals'])
    labels = list(canonical['comparison_names'])
    outer_inputs = {}

    def witness(name):
        ref = dag.input('input_loader__' + name)
        outer_inputs[name] = ref
        return ref

    def compare(left, right, label):
        residuals.append((left, right))
        labels.append(label)
    beta = witness('canonical_beta')
    compare(dag.add(c['input_slack'], beta), dag.add(u, one), 'canonical_input_bits:input_slack+beta=u+1')
    N = witness('N')
    m0 = dag.const(2 ** 32 - 1)
    lhs = dag.mul(m0, N)
    term0 = dag.mul(m0, ext['a_e'])
    term1 = dag.mul(dag.mul(ext['p_e'], dag.const(3941247658)), c['modulus'])
    term2 = dag.mul(dag.mul(ext['p_e'], dag.const((2 ** 32 - 1) * -4194240)), spread)
    term3 = dag.mul(dag.mul(dag.mul(ext['p_e'], m0), ext['s_e']), c['Q'])
    compare(lhs, dag.total([term0, term1, term2, term3]), 'ordinary_frame:exact_LSB_right_tape')
    literal = literal_pair_recipe(dag, literal_genera)
    exponent = build_recoder(dag, literal['pair_width'], EXPONENT_NS, one, one)
    e = exponent['registers']
    residuals.extend(exponent['residuals'])
    labels.extend(exponent['comparison_names'])
    ell, v, g = (witness(name) for name in ('ell', 'v', 'g'))
    compare(dag.add(dag.mul(e['Bm1'], v), ell), e['J'], 'unrestricted_tape_exponent:(B-1)v+ell=J')
    compare(dag.add(ell, g), e['Bm1'], 'unrestricted_tape_exponent:ell+g=B-1')
    compare(ell, dag.add(N, one), 'unrestricted_tape_exponent:ell=N+1')
    T = witness('T')
    compare(dag.mul(literal['K'], T), e['Q'], 'unary_scale:K*T=Q1')
    X = witness('X')
    queue_left = dag.mul(literal['K_minus_one'], X)
    queue_right = dag.add(dag.mul(literal['K_minus_one'], ext['C_e']), dag.mul(dag.mul(ext['L_e'], literal['V']), dag.sub(T, one)))
    compare(queue_left, queue_right, 'unary_queue:(K-1)X=(K-1)C_e+L_e*V*(T-1)')
    target_width = dag.mul(ext['L_e'], T)
    _require(len(residuals) == 75, 'loader comparison census mismatch')
    return {'X': X, 'target_width': target_width, 'residuals': residuals, 'residual_labels': labels, 'params': ext, 'namespaces': {CANONICAL_NS: canonical, EXPONENT_NS: exponent, 'input_loader': outer_inputs}, 'N': N, 'T': T, 'u': u, 'spread': spread, 'literal': literal, 'existential_count': 106, 'external_count': 6, 'width_equality_required': True, 'raw_loader_source_operations': 311, 'expected_after_zero_one_simplification': {'operations': 310, 'multiplications': 173, 'additions_subtractions': 137}}
