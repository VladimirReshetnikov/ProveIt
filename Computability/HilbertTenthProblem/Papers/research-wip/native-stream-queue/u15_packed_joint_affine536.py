"""Complete U15 joint-affine compiler: 338 raw / 536 ordinary operations.

The immediate 561 arithmetic parent has the identical full polynomial.
The original 611 ancestor is related through its paid loader graph and
factor-two tape residuals; that is a separate zero-set correspondence.
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

PARENT_FILE = 'u15_packed_downstream561.py'
PARENT_SHA = 'c4411ccfc9b62b1d8efe366686b99d4287031378b3acc0f5c07a1c10c52ef126'
AFFINE_FILE = 'u15_packed_joint_affine586.py'
AFFINE_SHA = '3467d394885167260ca7f85f2b23033661de056bdba1959a45c9fc15ff516d2a'
CUTS = ('J', 'S', 'Dir', 'W', 'WD', 'Qdev', 'Ndev')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def exact(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(type(k) is str and exact(a[k], b[k]) for k in a)
    if type(a) in (list, tuple):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def flag(value, name):
    require(type(value) is bool, name + ' must be an exact Boolean')
    return value


def _paths(root=None):
    here = Path(__file__).resolve().parent
    root = here if root is None else Path(root).resolve()
    paths = []
    for name, wanted in ((PARENT_FILE, PARENT_SHA), (AFFINE_FILE, AFFINE_SHA)):
        path = here / name if (here / name).is_file() else root / name
        require(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == wanted,
                'Pinned source changed or missing: ' + name)
        paths.append(path)
    return root, paths


def _load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _affine(packet, node):
    # Independent 30-coordinate expansion, including the exact hat offset.
    rows = {n: (op, a, b) for n, op, a, b in packet['source']}
    memo = {}
    def form(x):
        if type(x) is int:
            return (0,) * 29 + (x,)
        if x in memo:
            return memo[x]
        if x.startswith('edge') and x[4:].isdigit():
            i = int(x[4:])
            require(0 <= i < 29, 'Unknown edge')
            return tuple(int(j == i) for j in range(30))
        require(x in rows, 'Unpaid affine input')
        op, a, b = rows[x]
        aa, bb = form(a), form(b)
        if op in ('+', '-'):
            result = tuple(u + (v if op == '+' else -v) for u, v in zip(aa, bb))
        elif not any(aa[:29]):
            result = tuple(aa[29] * v for v in bb)
        else:
            require(not any(bb[:29]), 'Nonlinear affine projection')
            result = tuple(bb[29] * v for v in aa)
        memo[x] = result
        return result
    return form(node)


def _certificate(old, new):
    require(old['parameters'] == new['parameters'] and old['auxiliaries'] == new['auxiliaries'],
            'Coordinate interface changed')
    require(old['rules'] == new['rules'] and old['table'] == new['table'], 'Machine changed')
    vectors = {}
    for name in CUTS:
        before = _affine(old, old['registers'][name])
        after = _affine(new, new['registers'][name])
        column = {'S': 1, 'Dir': 3, 'W': 4, 'Qdev': 0, 'Ndev': 2}.get(name)
        weights = [1 if name == 'J' else r[3] * r[4] if name == 'WD'
                   else r[column] - (7 if name in ('Qdev', 'Ndev') else 0)
                   for r in new['rules']]
        require(before == after == tuple(weights) + (-sum(weights),), 'Affine identity failed')
        vectors[name] = list(after)
    nodes = {}
    def intern(key):
        if key not in nodes:
            nodes[key] = len(nodes)
        return nodes[key]
    def fingerprints(packet):
        cut = {packet['registers'][name]: name for name in CUTS}
        env = {n: intern(('input', n)) for n in packet['parameters'] + packet['auxiliaries']}
        def get(x):
            return env[x] if type(x) is str else intern(('constant', x))
        for n, op, a, b in packet['polynomial_source']:
            aa, bb = get(a), get(b)
            if op in ('+', '*'):
                aa, bb = sorted((aa, bb))
            env[n] = intern(('cut', cut[n])) if n in cut else intern((op, aa, bb))
        return ([(get(a), get(b)) for a, b in packet['comparisons']],
                {n: get(v) for n, v in packet['registers'].items()},
                {n: get(v) for n, v in packet['tag_registers'].items()},
                {n: get(v) for n, v in packet['computed_loader_fields'].items()},
                get(packet['output']))
    require(fingerprints(old) == fingerprints(new), 'Full downstream polynomial identity failed')
    return dict(exact_affine_vectors=vectors, unchanged_comparisons=len(old['comparisons']),
                full_polynomial_identity=True, expression_nodes=len(nodes))


@lru_cache(None)
def _bundle(root_text, parent_text, affine_text):
    root, paths = _paths(root_text)
    require([str(p) for p in paths] == [parent_text, affine_text], 'Source path changed')
    parent = _load(paths[0], '_joint536_parent')
    affine = _load(paths[1], '_joint536_affine')
    packets, parents, certificates = {}, {}, {}
    for ordinary in (False, True):
        old = parent.build(ordinary, root=root)
        packet, local = affine.rewrite(old)
        # The generic scout uses JSON-style rows. Canonical maintained packets
        # use tuples, matching the frozen complete compiler interfaces.
        for key in ('source', 'comparisons', 'polynomial_source'):
            packet[key] = [tuple(row) for row in packet[key]]
        substitutions = {old['registers'][name]: packet['registers'][name] for name in CUTS}
        ancestor_map = deepcopy(old['comparison_map'])
        for record in ancestor_map:
            if record['new_index'] is not None:
                record['child_pair'] = tuple(substitutions.get(x, x) for x in record['child_pair'])
                require(record['child_pair'] == packet['comparisons'][record['new_index']],
                        'Ancestor residual map became stale')
        packet.pop('comparison_map', None)
        packet.update(
            kind='joint_affine_complete_u15',
            canonical_parent={'file': PARENT_FILE, 'sha256': PARENT_SHA},
            graph_ancestor=deepcopy(old['canonical_parent']),
            ancestor_comparison_map=ancestor_map,
            source_lineage=dict(old['source_lineage'], **{PARENT_FILE: PARENT_SHA, AFFINE_FILE: AFFINE_SHA}),
            parent_relation='Exact full polynomial identity with downstream561 on every supplied tuple. '
                            'Separate positive graph restoration to centered611 preserves its entire zero set.',
            scope='Complete fixed-arity ordinary valid-program first-halt relation; no external horizon or new87 bound.')
        parent._finish(packet)
        certificate = _certificate(old, packet)
        require(old['ledger']['polynomial']['operations'] - packet['ledger']['polynomial']['operations'] == 25,
                'Expected 25 saved additions')
        require(old['ledger']['polynomial']['M'] == packet['ledger']['polynomial']['M'], 'Multiplications changed')
        require(packet['ledger']['polynomial']['operations'] == (536 if ordinary else 338), 'Wrong complete cost')
        require(packet['ledger']['formal_degree_upper_bound'] == 1936, 'Degree upper bound changed')
        packets[ordinary], parents[ordinary] = packet, old
        certificates[ordinary] = dict(source=certificate, local=local,
                                      exact_degree=deepcopy(parent._context(root)['degrees'][ordinary]))
    return dict(parent=parent, packets=packets, parents=parents, certificates=certificates)


def _context(root=None):
    root, paths = _paths(root)
    bundle = _bundle(str(root), *(str(p) for p in paths))
    bundle['parent']._context(root)
    return root, bundle


def build(ordinary=False, *, root=None):
    flag(ordinary, 'ordinary')
    return deepcopy(_context(root)[1]['packets'][ordinary])


def canonical_parent(ordinary=False, *, root=None):
    flag(ordinary, 'ordinary')
    return deepcopy(_context(root)[1]['parents'][ordinary])


def graph_ancestor(ordinary=False, *, root=None):
    flag(ordinary, 'ordinary')
    root, bundle = _context(root)
    return bundle['parent'].canonical_parent(ordinary, root=root)


def checked(packet, *, root=None):
    require(type(packet) is dict, 'Complete canonical packet required')
    ordinary = flag(packet.get('ordinary'), 'ordinary')
    require(exact(packet, _context(root)[1]['packets'][ordinary]), 'Noncanonical joint-affine packet')
    return packet


def polynomial_source(packet, *, root=None):
    return deepcopy(checked(packet, root=root)['polynomial_source'])


def evaluate(packet, values, *, signed=False, root=None):
    p = checked(packet, root=root)
    _, bundle = _context(root)
    parent = bundle['parent']
    values = parent._assignment(p, values, signed)
    return parent.execute(p['polynomial_source'], values)[p['output']]


def identity(packet, values, *, signed=False, root=None):
    p = checked(packet, root=root)
    _, bundle = _context(root)
    parent = bundle['parent']
    v = parent._assignment(p, values, signed)
    old = bundle['parents'][p['ordinary']]
    a = parent.execute(p['polynomial_source'], v)
    b = parent.execute(old['polynomial_source'], v)
    rr = [parent.at(a, x) - parent.at(a, y) for x, y in p['comparisons']]
    ro = [parent.at(b, x) - parent.at(b, y) for x, y in old['comparisons']]
    require(a[p['output']] == b[old['output']] and rr == ro, 'Full parent identity failed')
    return dict(common_output=a[p['output']], residuals=rr)


def restore_ancestor_assignment(packet, values, *, signed=False, root=None):
    p = checked(packet, root=root)
    root, bundle = _context(root)
    return bundle['parent'].restore_assignment(bundle['parents'][p['ordinary']], values, signed=signed, root=root)


def project_ancestor_assignment(packet, values, *, signed=False, require_graph=True, root=None):
    p = checked(packet, root=root)
    root, bundle = _context(root)
    return bundle['parent'].project_assignment(bundle['parents'][p['ordinary']], values,
                                              signed=signed, require_graph=require_graph, root=root)


def ancestor_identity(packet, values, *, signed=False, root=None):
    p = checked(packet, root=root)
    same = identity(p, values, signed=signed, root=root)
    root, bundle = _context(root)
    result = bundle['parent'].identity(bundle['parents'][p['ordinary']], values, signed=signed, root=root)
    require(same['common_output'] == result['child_output'], 'Ancestor composition failed')
    return result


def verify(root=None):
    root, bundle = _context(root)
    rng = random.Random(536338)
    counts, forms = Counter(), []
    def reject(fn):
        try:
            fn()
        except (ValueError, TypeError, KeyError):
            counts['malformed_calls_rejected'] += 1
            return
        raise AssertionError('Malformed input accepted')
    for ordinary in (False, True):
        p = build(ordinary, root=root)
        for case in range(96):
            signed = case >= 48
            v = {n: rng.randrange(-4, 5) if signed else rng.randrange(1, 7)
                 for n in p['parameters'] + p['auxiliaries']}
            answer = ancestor_identity(p, v, signed=signed, root=root)
            restored = restore_ancestor_assignment(p, v, signed=signed, root=root)
            require(project_ancestor_assignment(p, restored, signed=signed, root=root) == v, 'Ancestor roundtrip failed')
            counts['whole_parent_and_ancestor_identities'] += 1
            counts['signed_cases'] += signed
            counts['individual_parent_residual_identities'] += len(answer['residuals'])
        v = {n: 1 for n in p['parameters'] + p['auxiliaries']}
        for name in v:
            for bad in (True, 1.0, None):
                changed = dict(v); changed[name] = bad
                reject(lambda changed=changed: evaluate(p, changed, root=root))
        for bad in (0, 1, 0.0, None, 'yes'):
            reject(lambda bad=bad: build(bad, root=root))
            reject(lambda bad=bad: evaluate(p, v, signed=bad, root=root))
            reject(lambda bad=bad: project_ancestor_assignment(p, restore_ancestor_assignment(p, v, root=root), require_graph=bad, root=root))
        for i, row in enumerate(p['source']):
            changed = deepcopy(p); changed['source'][i] = (*row[:3], 1.0)
            reject(lambda changed=changed: checked(changed, root=root))
        for key in ('ancestor_comparison_map', 'computed_loader_fields', 'ledger', 'registers', 'canonical_parent', 'source_lineage'):
            changed = deepcopy(p)
            if type(changed[key]) is list: changed[key] = tuple(changed[key])
            else: changed[key]['tamper'] = 1
            reject(lambda changed=changed: checked(changed, root=root))
        for method in (build, canonical_parent, graph_ancestor):
            original = method(ordinary, root=root)
            changed = method(ordinary, root=root); changed['source'].clear()
            require(exact(method(ordinary, root=root), original), 'Public packet cache leaked')
            counts['defensive_copy_checks'] += 1
        changed = polynomial_source(p, root=root); changed.clear()
        require(exact(polynomial_source(p, root=root), p['polynomial_source']), 'Source cache leaked')
        counts['defensive_copy_checks'] += 1
        forms.append(dict(ordinary=ordinary, compiler=p, certificate=bundle['certificates'][ordinary]))
    return dict(status='PASS_COMPLETE_U15_536', source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                parent_sha256=PARENT_SHA, affine_sha256=AFFINE_SHA, counts=dict(counts), forms=forms,
                scope='Complete polynomial identity to561 and composed positive graph bijection to611; no new87 bound.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify(args.root)))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    else:
        require(exact(result, json.loads(path.read_text())), 'Saved receipt differs')
    print(json.dumps(dict(status=result['status'], counts=result['counts'],
                         ledgers=[f['compiler']['ledger'] for f in result['forms']]), indent=2))
