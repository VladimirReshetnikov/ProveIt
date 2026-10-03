"""Complete direct U15: factor the computed history index, 334 raw / 532 ordinary.

Every supplied coordinate and the complete polynomial are unchanged from536.
The three computed truth fields become proof-only reconstruction data rather
than charged live registers. The factorization is an integer polynomial identity.
"""
if not __debug__:
    raise RuntimeError('This research compiler requires assertions; omit -O')
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
import importlib.util
import json
from pathlib import Path
import random

PARENT_FILE = 'u15_packed_joint_affine536.py'
PARENT_SHA = 'eaaf3d99e74efeec26b7ad50842ac95fc89273f5ba37a52d45e9cca0e8fde330'
OLD = [
 ('native__padded_A', '+', 'native__scaled_A', 12),
 ('native__F1', '-', 'native__padded_A', 'native__F3'),
 ('native__F2', '-', 'native__padded_B', 'native__F3'),
 ('computed_q_minus_A', '-', 'native__q', 'native__padded_A'),
 ('computed_F0_plus_one', '-', 'computed_q_minus_A', 'native__F2'),
 ('native__F0', '-', 'computed_F0_plus_one', 1),
 ('native__bs_p0', '*', 'native__q', 'native__F3'),
 ('native__bs_p1', '+', 'native__F2', 'native__bs_p0'),
 ('native__bs_p2', '*', 'native__q', 'native__bs_p1'),
 ('native__bs_p3', '+', 'native__F1', 'native__bs_p2'),
 ('native__bs_p4', '*', 'native__q', 'native__bs_p3'),
 ('native__bs_packed', '+', 'native__F0', 'native__bs_p4')]
NEW = [
 ('packed_A_plus_one', '+', 'native__scaled_A', 13),
 ('packed_q_minus_one', '-', 'native__q', 1),
 ('packed_q_plus_one', '+', 'native__q', 1),
 ('packed_z_term', '*', 'packed_q_minus_one', 'native__F3'),
 ('packed_b_term', '+', 'native__padded_B', 'packed_z_term'),
 ('packed_b_product', '*', 'packed_q_plus_one', 'packed_b_term'),
 ('packed_inner', '+', 'packed_A_plus_one', 'packed_b_product'),
 ('native__bs_packed', '*', 'packed_q_minus_one', 'packed_inner')]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def exact(a, b):
    if type(a) is not type(b): return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(type(k) is str and exact(a[k], b[k]) for k in a)
    if type(a) in (list, tuple): return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def flag(x, name):
    require(type(x) is bool, name + ' must be an exact Boolean')
    return x


def _path(root=None):
    here = Path(__file__).resolve().parent
    root = here if root is None else Path(root).resolve()
    path = here / PARENT_FILE if (here / PARENT_FILE).is_file() else root / PARENT_FILE
    require(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == PARENT_SHA,
            'Pinned536 source changed or missing')
    return root, path


def _local_identity():
    # Sparse exact polynomials in (scaled_A, q, padded_B, F3).
    zero = (0, 0, 0, 0)
    inputs = ('native__scaled_A', 'native__q', 'native__padded_B', 'native__F3')
    def evaluate(rows):
        env = {n: {tuple(int(i == j) for i in range(4)): 1} for j, n in enumerate(inputs)}
        def get(x): return env[x] if type(x) is str else ({zero: x} if x else {})
        for n, op, a, b in rows:
            aa, bb = get(a), get(b)
            cc = {}
            if op == '*':
                for i, u in aa.items():
                    for j, v in bb.items():
                        k = tuple(x + y for x, y in zip(i, j))
                        cc[k] = cc.get(k, 0) + u * v
            else:
                cc = dict(aa)
                for i, v in bb.items(): cc[i] = cc.get(i, 0) + (v if op == '+' else -v)
            env[n] = {i: v for i, v in cc.items() if v}
        return env['native__bs_packed']
    before, after = evaluate(OLD), evaluate(NEW)
    require(before == after, 'Packed-index polynomial identity failed')
    return [[list(k), v] for k, v in sorted(after.items())]


def _certificate(old, new):
    terms = _local_identity()
    require(old['parameters'] == new['parameters'] and old['auxiliaries'] == new['auxiliaries'],
            'Coordinates changed')
    nodes = {}
    def intern(key):
        if key not in nodes: nodes[key] = len(nodes)
        return nodes[key]
    def fingerprints(p):
        env = {n: intern(('input', n)) for n in p['parameters'] + p['auxiliaries']}
        def get(x): return env[x] if type(x) is str else intern(('constant', x))
        for n, op, a, b in p['polynomial_source']:
            aa, bb = get(a), get(b)
            if op in ('+', '*'): aa, bb = sorted((aa, bb))
            env[n] = intern(('proved packed index',)) if n == 'native__bs_packed' else intern((op, aa, bb))
        return ([(get(a), get(b)) for a, b in p['comparisons']],
                {n: get(v) for n, v in p['registers'].items()},
                {n: get(v) for n, v in p['tag_registers'].items()},
                {n: get(v) for n, v in p['computed_loader_fields'].items()}, get(p['output']))
    require(fingerprints(old) == fingerprints(new), 'Complete polynomial/residual identity failed')
    return dict(index_monomials=terms, full_polynomial_identity=True,
                unchanged_residuals=len(new['comparisons']), expression_nodes=len(nodes))


@lru_cache(None)
def _bundle(root_text, path_text):
    root, path = _path(root_text)
    require(str(path) == path_text, 'Parent path changed')
    spec = importlib.util.spec_from_file_location('_factored532_parent', path)
    parent = importlib.util.module_from_spec(spec); spec.loader.exec_module(parent)
    packets, parents, certificates = {}, {}, {}
    # Use the authenticated parent's existing source finalizer, with explicit root.
    utility = parent._context(root)[1]['parent']
    for ordinary in (False, True):
        old = parent.build(ordinary, root=root)
        p = deepcopy(old)
        rows = {n: (n, op, a, b) for n, op, a, b in p['source']}
        require(all(exact(rows.get(r[0]), r) for r in OLD), 'Incoming packed-index block changed')
        private = {r[0] for r in OLD} - {'native__bs_packed'}
        removed = {r[0] for r in OLD}
        for n, op, a, b in p['source']:
            if n not in removed: require(a not in private and b not in private, 'Private packed register escaped')
        for a, b in p['comparisons']: require(a not in private and b not in private, 'Private comparison escaped')
        require(exact(p['computed_definitions'], OLD[1:6]), 'Truth reconstruction changed')
        require(exact(p['computed_truth_fields'], ('native__F0', 'native__F1', 'native__F2')), 'Truth fields changed')
        p['proof_only_truth_reconstruction'] = dict(
            scope='Historical computed truth fields; these are not emitted gates or new witnesses.',
            rows=deepcopy(OLD[:6]), fields=p.pop('computed_truth_fields'))
        p.pop('computed_definitions')
        p['source'] = utility._sort([r for r in p['source'] if r[0] not in removed] + NEW,
                                    p['parameters'] + p['auxiliaries'])
        p.update(kind='factored_history_index_complete_u15',
                 canonical_parent=dict(file=PARENT_FILE, sha256=PARENT_SHA),
                 source_lineage=dict(p['source_lineage'], **{PARENT_FILE: PARENT_SHA}),
                 parent_relation='Identical complete polynomial and coordinates to536 on every supplied tuple.',
                 scope='Complete fixed-arity ordinary valid-program first-halt relation; no new87 bound.')
        utility._finish(p)
        certificate = _certificate(old, p)
        require(p['ledger']['polynomial']['operations'] == (532 if ordinary else 334), 'Wrong complete cost')
        require(old['ledger']['polynomial']['M'] == p['ledger']['polynomial']['M'], 'Multiplication count changed')
        require(p['ledger']['formal_degree_upper_bound'] == 1936, 'Degree changed')
        packets[ordinary], parents[ordinary], certificates[ordinary] = p, old, certificate
    return dict(parent=parent, utility=utility, packets=packets, parents=parents, certificates=certificates)


def _context(root=None):
    root, path = _path(root)
    bundle = _bundle(str(root), str(path))
    bundle['parent']._context(root)
    return root, bundle


def build(ordinary=False, *, root=None):
    flag(ordinary, 'ordinary')
    return deepcopy(_context(root)[1]['packets'][ordinary])


def canonical_parent(ordinary=False, *, root=None):
    flag(ordinary, 'ordinary')
    return deepcopy(_context(root)[1]['parents'][ordinary])


def checked(packet, *, root=None):
    require(type(packet) is dict, 'Complete canonical packet required')
    ordinary = flag(packet.get('ordinary'), 'ordinary')
    require(exact(packet, _context(root)[1]['packets'][ordinary]), 'Noncanonical factored-index packet')
    return packet


def polynomial_source(packet, *, root=None):
    return deepcopy(checked(packet, root=root)['polynomial_source'])


def evaluate(packet, values, *, signed=False, root=None):
    p = checked(packet, root=root)
    _, bundle = _context(root); utility = bundle['utility']
    values = utility._assignment(p, values, signed)
    return utility.execute(p['polynomial_source'], values)[p['output']]


def identity(packet, values, *, signed=False, root=None):
    p = checked(packet, root=root)
    _, bundle = _context(root); utility = bundle['utility']
    values = utility._assignment(p, values, signed)
    old = bundle['parents'][p['ordinary']]
    a, b = [utility.execute(q['polynomial_source'], values) for q in (p, old)]
    rr = [utility.at(a, x) - utility.at(a, y) for x, y in p['comparisons']]
    ro = [utility.at(b, x) - utility.at(b, y) for x, y in old['comparisons']]
    require(a[p['output']] == b[old['output']] and rr == ro, 'Full polynomial identity failed')
    require(a['native__bs_packed'] == b['native__bs_packed'], 'Index changed')
    return dict(common_output=a[p['output']], residuals=rr)


def verify(root=None):
    root, bundle = _context(root)
    rng = random.Random(532334); counts = Counter(); forms = []
    def reject(fn):
        try: fn()
        except (ValueError, TypeError, KeyError): counts['malformed_calls_rejected'] += 1; return
        raise AssertionError('Malformed call accepted')
    for ordinary in (False, True):
        p = build(ordinary, root=root)
        for case in range(48):
            signed = case >= 24
            v = {n: rng.randrange(-4, 5) if signed else rng.randrange(1, 7)
                 for n in p['parameters'] + p['auxiliaries']}
            answer = identity(p, v, signed=signed, root=root)
            counts['complete_identities'] += 1; counts['signed_cases'] += signed
            counts['residual_identities'] += len(answer['residuals'])
        v = {n: 1 for n in p['parameters'] + p['auxiliaries']}
        for n in v:
            for bad in (True, 1.0, None):
                vv = dict(v); vv[n] = bad
                reject(lambda vv=vv: evaluate(p, vv, root=root))
        for bad in (0, 1, None, 'yes', 0.0):
            reject(lambda bad=bad: build(bad, root=root))
            reject(lambda bad=bad: evaluate(p, v, signed=bad, root=root))
        for key in ('source', 'comparisons', 'ledger', 'proof_only_truth_reconstruction', 'canonical_parent'):
            changed = deepcopy(p); changed[key] = None
            reject(lambda changed=changed: checked(changed, root=root))
        for method in (build, canonical_parent):
            original = method(ordinary, root=root); altered = method(ordinary, root=root)
            altered['source'].clear()
            require(exact(original, method(ordinary, root=root)), 'Cache leaked')
            counts['defensive_copy_checks'] += 1
        altered = polynomial_source(p, root=root); altered.clear()
        require(exact(polynomial_source(p, root=root), p['polynomial_source']), 'Source cache leaked')
        counts['defensive_copy_checks'] += 1
        forms.append(dict(ordinary=ordinary, compiler=p, certificate=bundle['certificates'][ordinary]))
    return dict(status='PASS_COMPLETE_U15_532', source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                parent_sha256=PARENT_SHA, counts=dict(counts), forms=forms)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify(args.root)))
    path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    else: require(exact(result, json.loads(path.read_text())), 'Saved receipt differs')
    print(json.dumps(dict(status=result['status'], counts=result['counts'],
                         ledgers=[f['compiler']['ledger'] for f in result['forms']]), indent=2))
