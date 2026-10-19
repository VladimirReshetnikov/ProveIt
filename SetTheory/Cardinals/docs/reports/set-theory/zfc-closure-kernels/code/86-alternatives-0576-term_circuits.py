"""Proof-carrying constructor circuits for exact C254 term certificates.

Stdlib-only verifier: the trusted fixed specification is loaded separately from
source50's spec254.json. Candidate certificates cannot select its templates.
There is no arena interning, constructor search or global uniqueness test.
No binary codec, compiler or TM state count is claimed.
"""
from dataclasses import dataclass
import json
from pathlib import Path

FORMAT = 'term-c254-circuit-v1'
ARITY = (0, 1, 1, 2, 3, 3, 3, 3, 2, 3, 4, 3)


@dataclass(frozen=True)
class Circuit:
    arity: int
    steps: tuple  # (tag, left-register, right-register), local postorder
    root: int


def compile_templates(definitions):
    """Compile only the finite trusted source templates, never candidate data.

    Circuit registers0..arity-1 are parameters; register arity is literalZ.
    Subsequent registers are explicit constructor witnesses. Static sharing is
    of fixed symbolic expressions only, independently of all candidate arenas.
    """
    zero = ('z',)
    def primitive(tag, left, right):
        return zero if (tag, left, right) == (0, zero, zero) else (tag, left, right)
    def expand(name, args):
        if name in ('wim', 'wel', 'wal', 'weq'):
            return primitive(('wim', 'wel', 'wal', 'weq').index(name), *args)
        f = primitive(1, zero, zero)
        if name == 'wn':
            return primitive(0, args[0], f)
        if name == 'wa':
            return primitive(0, primitive(0, args[0], primitive(0, args[1], f)), f)
        if name == 'wex':
            return primitive(0, primitive(2, args[0], primitive(0, args[1], f)), f)
        spec = definitions[name]
        env = dict(zip(spec['parameters'], args, strict=True))
        def expr(term):
            if type(term) is int:
                if term == 0:
                    return zero
                if term == 1:
                    return f
                raise ValueError('unexpected fixed literal')
            if type(term) is str:
                return f if term == 'F' else env[term]
            return expand(term[0], [expr(t) for t in term[1:]])
        return expr(spec['term'])
    tables = {}
    for tag in (*range(3, 11), 11):
        name = 'bundle' if tag == 11 else 'rho' + str(tag - 2)
        arity = ARITY[tag]
        params = [('p', i) for i in range(arity)]
        tree = expand(name, params)
        slots = {param: i for i, param in enumerate(params)}
        slots[zero] = arity
        steps = []
        def emit(term):
            if term in slots:
                return slots[term]
            tag, left, right = term
            li, ri = emit(left), emit(right)
            out = arity + 1 + len(steps)
            steps.append((tag, li, ri))
            slots[term] = out
            return out
        root = emit(tree)
        tables[tag] = Circuit(arity, tuple(steps), root)
    return tables


def load_templates(spec_path):
    """Trusted caller selects the attributed fixed spec, not the certificate."""
    return compile_templates(json.loads(Path(spec_path).read_text())['definitions'])


class Invalid(ValueError):
    pass


def require(condition, reason):
    if not condition:
        raise Invalid(reason)


def validate_nodes(nodes, stats):
    require(type(nodes) is list and bool(nodes) and nodes[0] == ['z'], 'zero_node')
    for i, node in enumerate(nodes[1:], 1):
        stats['node_records'] += 1
        require(type(node) is list and len(node) == 4 and node[0] == 'b', 'node_shape')
        _, tag, left, right = node
        require(type(tag) is int and 0 <= tag < 4, 'node_tag')
        require(all(type(j) is int and 0 <= j < i for j in (left, right)), 'node_reference')
        require((tag, left, right) != (0, 0, 0), 'zero_alias')


def constructor(nodes, out, tag, left, right, stats):
    """Check one supplied record; no search or candidate interning index."""
    stats['constructor_checks'] += 1
    if tag == 0 and left == 0 and right == 0:
        return out == 0
    return nodes[out] == ['b', tag, left, right]


def distinguish(nodes, left, right, path, stats):
    if type(path) is not list or not all(type(b) is int and b in (0, 1) for b in path):
        return False
    for bit in path:
        if left == 0 or right == 0 or nodes[left][1] != nodes[right][1]:
            return False
        stats['path_edges'] += 1
        left, right = nodes[left][2 + bit], nodes[right][2 + bit]
    if left == 0 or right == 0:
        return (left == 0) != (right == 0)
    return nodes[left][1] != nodes[right][1]


def is_falsity(nodes, root):
    """Recognizes every positive copy of the exact numeric1 term."""
    return nodes[root] == ['b', 1, 0, 0]


def verify_certificate(cert, templates, goal=None, *, stats=None):
    """Default accepts only fixedF. templates is trusted, finite, fixed theory data.

    goal is a trusted caller's positive-control ID; cert['goal'] has no effect.
    """
    if stats is None:
        stats = {}
    stats.update(node_records=0, constructor_checks=0, circuit_steps=0,
                 path_edges=0, proof_rows=0, template_searches=0,
                 arena_uniqueness_comparisons=0, reason=None)
    try:
        require(type(cert) is dict and cert.get('format') == FORMAT, 'format')
        nodes = cert['nodes']
        validate_nodes(nodes, stats)
        if goal is not None:
            require(type(goal) is int and 0 <= goal < len(nodes), 'control_goal')
        rows = cert['proof_rows']
        require(type(rows) is list, 'proof_list')
        formulas = []
        for i, row in enumerate(rows):
            stats['proof_rows'] += 1
            require(type(row) is dict, 'proof_row')
            tag, args, children, out = row['tag'], row['args'], row['children'], row['formula']
            require(type(tag) is int and 0 <= tag < 12, 'proof_tag')
            require(type(args) is list and len(args) == ARITY[tag], 'proof_arity')
            require(all(type(j) is int and 0 <= j < len(nodes) for j in args), 'argument')
            require(type(out) is int and 0 <= out < len(nodes), 'claimed_formula')
            require(type(children) is list and len(children) ==
                    (2 if tag == 1 else 1 if tag == 2 else 0), 'premise_arity')
            require(all(type(j) is int and 0 <= j < i for j in children), 'premise_reference')
            if tag == 0:
                require(out == 0, 'truth')
                require(row.get('constructor_ids', []) == [], 'unexpected_circuit')
            elif tag == 1:
                require(out == args[0], 'mp_conclusion')
                require(constructor(nodes, formulas[children[1]], 0,
                                    formulas[children[0]], out, stats), 'mp_major')
                require(row.get('constructor_ids', []) == [], 'unexpected_circuit')
            elif tag == 2:
                require(constructor(nodes, out, 2, args[0], formulas[children[0]], stats), 'gen')
                require(row.get('constructor_ids', []) == [], 'unexpected_circuit')
            else:
                if tag == 11:
                    paths = row['gate_paths']
                    require(type(paths) is list and len(paths) == 2, 'gate_witness_arity')
                    require(distinguish(nodes, args[2], args[0], paths[0], stats), 'bundle_gate_1')
                    require(distinguish(nodes, args[2], args[1], paths[1], stats), 'bundle_gate_2')
                circuit = templates[tag]
                ids = row['constructor_ids']
                require(type(ids) is list and len(ids) == len(circuit.steps), 'circuit_length')
                require(all(type(j) is int and 0 <= j < len(nodes) for j in ids), 'circuit_id')
                values = list(args) + [0]
                for node, (kind, left, right) in zip(ids, circuit.steps, strict=True):
                    stats['circuit_steps'] += 1
                    require(constructor(nodes, node, kind, values[left], values[right], stats),
                            'circuit_constructor')
                    values.append(node)
                require(out == values[circuit.root], 'circuit_root')
            formulas.append(out)
        require(bool(formulas), 'empty_proof')
        require(formulas[-1] == goal if goal is not None else is_falsity(nodes, formulas[-1]),
                'fixed_or_control_endpoint')
        return True
    except (Invalid, ValueError, TypeError, KeyError, IndexError) as error:
        stats['reason'] = str(error)
        return False
