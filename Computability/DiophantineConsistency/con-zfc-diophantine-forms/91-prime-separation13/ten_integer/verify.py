#!/usr/bin/env python3
"""Read-only, standard-library audit of the three-operation simplification.

verify_all() returns a JSON-serializable dictionary and writes no files.
The checks are explicit exceptions and therefore survive Python -O.
"""
from pathlib import Path
import collections
import copy
import functools
import hashlib
import json
import types

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    'predecessor': (480, 477, 1245324),
    'linear': (484, 481, 1179788),
    'cubic': (487, 484, 1114252),
    'sixterm': (521, 518, 1081125),
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def load_module(name, path):
    # Compile directly to avoid creating bytecode-cache files in the archive.
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return module


def parent_path(variant):
    return ROOT/'upstream'/('upstream/integer10.json' if variant == 'predecessor'
                            else 'integer10_'+variant+'.json')


def graph_check(body):
    """Check counts, references, liveness, and the syntactic degree bound."""
    degree = []
    counts = collections.Counter()
    seen_variables = set()
    for i, node in enumerate(body['nodes']):
        kind = node['kind']
        if kind == 'variable':
            need(node['name'] in body['variables'], 'undeclared variable')
            seen_variables.add(node['name'])
            value = 1
        elif kind in ('fixed', 'literal'):
            value = 0
        else:
            need(kind in ('add', 'sub', 'mul'), 'unknown operation')
            a, b = node['left'], node['right']
            need(type(a) is int and type(b) is int and 0 <= a < i and 0 <= b < i,
                 'invalid topological operand')
            value = degree[a]+degree[b] if kind == 'mul' else max(degree[a], degree[b])
            counts[kind] += 1
        degree.append(value)
    need(seen_variables == set(body['variables']) and len(body['variables']) == 10,
         'exactly ten declared, used variables')
    need(dict(counts) == body['operation_counts'], 'operation histogram')
    need(sum(counts.values()) == body['total_operations'], 'operation count')
    need(degree[body['output']] == body['degree_upper_bound'], 'syntactic degree bound')
    live, todo = set(), [body['output']]
    while todo:
        i = todo.pop()
        if i in live:
            continue
        need(type(i) is int and 0 <= i < len(body['nodes']), 'invalid live node')
        live.add(i)
        n = body['nodes'][i]
        if n['kind'] in ('add', 'sub', 'mul'):
            todo.extend((n['left'], n['right']))
    need(len(live) == len(body['nodes']), 'dead nodes in delivered graph')
    for i in body['named_nodes'].values():
        need(type(i) is int and 0 <= i < len(body['nodes']), 'invalid named node')
    return sum(counts.values())


class Poly:
    """Small exact sparse polynomials in four formal variables."""
    zero = (0, 0, 0, 0)

    def __init__(self, terms=None):
        self.terms = {e: c for e, c in (terms or {}).items() if c}

    @classmethod
    def lift(cls, x):
        return x if isinstance(x, cls) else cls({cls.zero: int(x)})

    @classmethod
    def variable(cls, i):
        e = [0]*4
        e[i] = 1
        return cls({tuple(e): 1})

    def __add__(self, other):
        out = dict(self.terms)
        for e, c in self.lift(other).terms.items():
            out[e] = out.get(e, 0)+c
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({e: -c for e, c in self.terms.items()})

    def __sub__(self, other):
        return self+-self.lift(other)

    def __rsub__(self, other):
        return self.lift(other)+-self

    def __mul__(self, other):
        out = {}
        for a, c in self.terms.items():
            for b, d in self.lift(other).terms.items():
                e = tuple(x+y for x, y in zip(a, b))
                out[e] = out.get(e, 0)+c*d
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        need(type(n) is int and n >= 0, 'polynomial exponent')
        out = Poly.lift(1)
        for _ in range(n):
            out = out*self
        return out

    def __eq__(self, other):
        return self.terms == self.lift(other).terms


def local_polynomial(body, output, cut_names):
    """Expand only a small local expression above named formal cut points."""
    cuts = {body['named_nodes'][name]: Poly.variable(i)
            for i, name in enumerate(cut_names)}
    need(len(cuts) == len(cut_names), 'aliased local cut points')

    @functools.lru_cache(None)
    def visit(i):
        if i in cuts:
            return cuts[i]
        n = body['nodes'][i]
        k = n['kind']
        if k == 'literal':
            return Poly.lift(n['value'])
        need(k in ('add', 'sub', 'mul'), 'unexpected uncut local leaf')
        a, b = visit(n['left']), visit(n['right'])
        return a+b if k == 'add' else a-b if k == 'sub' else a*b

    return visit(output)


class Contexts:
    """Exact term interning; no hashes stand in for equality.

    Products are flattened into multisets of factors. This proves the shared
    power rewrite by associativity and commutativity, without expanding the
    enormous full polynomial. Adds are commuted, but never distributed.
    """
    def __init__(self):
        self.index, self.keys = {}, []

    def intern(self, key):
        if key not in self.index:
            self.index[key] = len(self.keys)
            self.keys.append(key)
        return self.index[key]

    def operation(self, kind, a, b):
        if kind == 'mul':
            counts = collections.Counter()
            for x in (a, b):
                key = self.keys[x]
                counts.update(dict(key[1]) if key[0] == 'mul' else {x: 1})
            return self.intern(('mul', tuple(sorted(counts.items()))))
        if kind == 'add':
            a, b = sorted((a, b))
        return self.intern((kind, a, b))

    def graph(self, body, cut_delta=False, variables=None):
        variables = variables or {}
        out = []
        for i, n in enumerate(body['nodes']):
            kind = n['kind']
            if cut_delta and i == body['named_nodes']['Delta']:
                value = self.intern(('certified_equal_subexpression', 'Delta'))
            elif kind == 'variable' and n['name'] in variables:
                value = variables[n['name']]
            elif kind in ('variable', 'fixed'):
                value = self.intern((kind, n['name']))
            elif kind == 'literal':
                value = self.intern((kind, n['value']))
            else:
                value = self.operation(kind, out[n['left']], out[n['right']])
            out.append(value)
        return out


def exact_rewrite_check(parent, new):
    """Exact local ring identities plus equality of their full DAG contexts."""
    # First certify that the discriminant's four arguments have not changed.
    context = Contexts()
    old_terms, new_terms = context.graph(parent), context.graph(new)
    delta_inputs = ('g', 'cap', 'K', 'CKL')
    for name in delta_inputs:
        need(old_terms[parent['named_nodes'][name]] == new_terms[new['named_nodes'][name]],
             'changed discriminant argument '+name)
    g, cap, k, ckl = [Poly.variable(i) for i in range(4)]
    delta_left = 8*cap**3*g*k**2-g**2*(32*ckl**2*cap**3+g**2*k**2)
    delta_right = 8*g*cap**3*(k**2-4*g*ckl**2)-g**4*k**2
    need(delta_left == delta_right, 'exact discriminant ring identity')
    need(local_polynomial(parent, parent['named_nodes']['Delta'], delta_inputs) == delta_left,
         'parent discriminant transcription')
    need(local_polynomial(new, new['named_nodes']['Delta'], delta_inputs) == delta_right,
         'new discriminant transcription')

    # Replacing the certified Delta by one common formal atom proves that
    # the remainder of the old and new norm inputs agrees. Multiplicative
    # factor interning also checks S^5=S^2*S^3 in its actual graph context.
    context = Contexts()
    old_terms = context.graph(parent, cut_delta=True)
    new_terms = context.graph(new, cut_delta=True)
    center = 'center' if 'center' in parent['named_nodes'] else 'shifted_center'
    norm_inputs = ('guard', 'lucas', center, 'Sigma')
    for name in norm_inputs:
        need(old_terms[parent['named_nodes'][name]] == new_terms[new['named_nodes'][name]],
             'changed norm argument '+name)
    a0, a1, z, sigma = [Poly.variable(i) for i in range(4)]
    norm_left = (z**2-sigma**2*(a0+a1))**2-4*sigma**4*a0*a1
    norm_right = (z**2+sigma**2*(a0-a1))**2-4*z**2*sigma**2*a0
    need(norm_left == norm_right, 'exact two-root norm ring identity')
    need(local_polynomial(parent, parent['output'], norm_inputs) == norm_left,
         'parent norm transcription')
    need(local_polynomial(new, new['output'], norm_inputs) == norm_right,
         'new norm transcription')
    return {'exact_local_ring_identities': True,
            'exact_unchanged_contexts': True,
            'shared_power_context_checked': True,
            'result': 'The two literal DAGs compute the identical polynomial over Z.'}


def source_checks():
    """Use the retained source's exact algebra and coefficient certificates.

    This calls only its read-only functions, never its file-writing main().
    Degree attainment is checked against the actual supplied integers.
    """
    source = load_module('ten_integer_upstream_verifier', ROOT/'upstream/verify.py')
    bounds, fixed = source.algebra(), source.fixed_values()
    old = json.loads(parent_path('predecessor').read_text())
    required = {'halfA': 16384, 'A': 16384, 'B1': 7942, 'C': 1,
                'xi': 2, 'Sigma': 81922, 'Theta': 81925, 'guard': 294619,
                'lucas': 458818, 'E': 32774, 'G': 81930, 'H': 98321}
    report = {}
    for variant, (parent_count, _, degree) in EXPECTED.items():
        body = json.loads(parent_path(variant).read_text())
        need(graph_check(body) == parent_count, 'source operation count '+variant)
        need(body.get('exact_degree', body['degree_upper_bound']) == degree,
             'source stated exact degree '+variant)
        if variant != 'predecessor':
            need(bounds[variant]['final_degree_bound'] == degree,
                 'source exact sparse degree bound '+variant)
            context = Contexts()
            terms = context.graph(body)
            shifted_m = terms[body['named_nodes']['shifted_m']]
            old_terms = context.graph(old, variables={'m': shifted_m})
            need(terms[body['output']] == old_terms[old['output']],
                 'exact source polynomial shear identity '+variant)
        leaders = {}
        for prime in (1000003, 1000033, 1000037):
            dg, lc = source.degree_leaders(old, fixed, prime)
            lead = {name: lc[i] for name, i in old['named_nodes'].items()}
            for name, expected in required.items():
                need(dg[old['named_nodes'][name]] == expected and lead[name] != 0,
                     'source attained prefix degree '+name)
            if variant == 'predecessor':
                need(dg[old['output']] == degree, 'predecessor degree bound')
                final = lc[old['output']]
            elif variant == 'linear':
                defect = -16*lead['E']**2*lead['G']**2*lead['H']**2
                final = lead['Sigma']**4*defect**2
            elif variant == 'cubic':
                core = 48*lead['C']**8*lead['xi']**2*lead['A']**2
                defect = core*lead['G']**2*lead['H']**2
                final = lead['Sigma']**4*defect**2
            else:
                final = -4*lead['Sigma']**4*lead['guard']*lead['lucas']
            leaders[str(prime)] = final % prime
            need(leaders[str(prime)] != 0, 'source attained final degree '+variant)
        report[variant] = {'exact_degree': degree,
                           'nonzero_leading_coefficients_mod_primes': leaders}
    return {'fixed_integer_payloads_verified': len(fixed), 'variants': report}


def negative_controls():
    """Valid, equally sized corrupted graphs must fail the exact checker."""
    parent = json.loads(parent_path('predecessor').read_text())
    new = json.loads((ROOT/'integer10_predecessor.json').read_text())
    corruptions = []
    reversed_subtraction = copy.deepcopy(new)
    n = reversed_subtraction['nodes'][reversed_subtraction['output']]
    need(n['kind'] == 'sub', 'negative-control output is a subtraction')
    n['left'], n['right'] = n['right'], n['left']
    corruptions.append(('reversed_final_subtraction', reversed_subtraction))
    changed_context = copy.deepcopy(new)
    for n in changed_context['nodes']:
        if n['kind'] == 'variable' and n['name'] in ('g0', 'c0'):
            n['name'] = 'c0' if n['name'] == 'g0' else 'g0'
    corruptions.append(('permuted_prefix_variables', changed_context))
    rejected = []
    for label, bad in corruptions:
        graph_check(bad)  # Both changes preserve a valid graph and its count.
        try:
            exact_rewrite_check(parent, bad)
        except ValueError:
            rejected.append(label)
        else:
            raise ValueError('exact checker accepted negative control '+label)
    return rejected


def verify_all():
    pins = json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for name, expected in pins['files'].items():
        raw = (ROOT/name).read_bytes()
        need(len(raw) == expected['bytes'] and hashlib.sha256(raw).hexdigest() == expected['sha256'],
             'copied source changed: '+name)
    optimizer = load_module('ten_integer_optimizer', ROOT/'optimize.py')
    runner = load_module('ten_integer_builder', ROOT/'optimize_shears.py')
    summary = json.loads((ROOT/'SUMMARY.json').read_text())
    variants = {}
    for variant, (old_count, new_count, degree) in EXPECTED.items():
        parent_raw = parent_path(variant).read_bytes()
        parent = json.loads(parent_raw)
        new_raw = (ROOT/('integer10_'+variant+'.json')).read_bytes()
        new = json.loads(new_raw)
        need(graph_check(new) == new_count, 'optimized count '+variant)
        need(parent['total_operations'] == old_count, 'parent count '+variant)
        need(new['exact_degree'] == degree, 'preserved exact degree '+variant)
        need(runner.serialize(runner.build_variant(variant, parent)) == new_raw,
             'deterministic optimized graph reproduction '+variant)
        exact = exact_rewrite_check(parent, new)
        diagnostic = optimizer.verify(parent, new, saving=3)
        receipt = json.loads((ROOT/('CHECKS_'+variant+'.json')).read_text())
        need(receipt == summary[variant], 'receipt/summary agreement '+variant)
        for key, value in diagnostic.items():
            need(receipt[key] == value, 'diagnostic receipt mismatch '+variant+' '+key)
        need(receipt['exact_polynomial_check'] == exact, 'exact receipt mismatch '+variant)
        need(receipt['parent_sha256'] == hashlib.sha256(parent_raw).hexdigest(),
             'parent receipt digest '+variant)
        need(receipt['new_sha256'] == hashlib.sha256(new_raw).hexdigest(),
             'output receipt digest '+variant)
        variants[variant] = {'parent_operations': old_count, 'operations': new_count,
                             'exact_degree': degree, 'finite_modular_diagnostics': diagnostic['modular_checks'],
                             **exact}
    inherited = source_checks()
    return {'status': 'PASS', 'source_files_pinned': len(pins['files']),
            'variants': variants, 'source_degree_and_coefficient_checks': inherited,
            'equally_sized_corrupted_graphs_rejected': negative_controls(),
            'scope': 'Exact local polynomial identities, exact context matching and source degree/data certificates. Finite modular evaluations are transcription diagnostics. The inherited unbounded compiler/refutation calibration is not proved by these computations.'}


if __name__ == '__main__':
    print(json.dumps(verify_all(), indent=2))
