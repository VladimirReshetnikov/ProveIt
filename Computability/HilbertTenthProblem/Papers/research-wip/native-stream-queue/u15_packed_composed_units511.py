"""Complete direct U15 compositions: 511 ordinary / 323 raw operations.

The optional ungrouped source retains the parent's identical polynomial in
523 / 325 operations and exact degree1936. Grouping native units preserves
the full integer zero set, with exact degrees4881 ordinary /3464 raw.
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

PINS = {
 'u15_packed_factored_index532.py': 'ed716945027275990e5aff1f7d4d180533af3e44b2a8c1862c3db4a7db7cf954',
 'u15_joint_binary_affine_rewrite.py': 'ffc6c36ee9ee4fc5701d9d6c9422e4fbc29aaa7f9bbea4e768fc1e2831aa2e44',
 'u15_packed_unit_product524.py': '667de9e6648af91c2fa1fe22801786fb78fd82156bce3132be05e9f10e513611',
}
PARENT_FILE = 'u15_packed_factored_index532.py'


def require(ok, message):
    if not ok: raise ValueError(message)


def exact(a, b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys() == b.keys() and all(type(k) is str and exact(a[k], b[k]) for k in a)
    if type(a) in (list, tuple): return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def flag(x, name):
    require(type(x) is bool, name + ' must be an exact Boolean')
    return x


def _paths(root=None):
    here = Path(__file__).resolve().parent
    root = here if root is None else Path(root).resolve()
    paths = []
    for name, wanted in PINS.items():
        path = here / name if (here / name).is_file() else root / name
        require(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == wanted,
                'Pinned composition dependency changed or missing: ' + name)
        paths.append(path)
    return root, paths


def _load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def _degree_sos(p):
    records = []
    for prime in (1000000007, 1000000009):
        env = {n: (0 if n in p['fixed_parameters'] else 1, (i % 7) + 1,
                   {n} if n in p['fixed_parameters'] else set())
               for i, n in enumerate(p['parameters'] + p['auxiliaries'])}
        def get(x): return env[x] if type(x) is str else (0, x, set())
        for n, op, a, b in p['polynomial_source']:
            da, ca, sa = get(a); db, cb, sb = get(b)
            if op == '*': env[n] = (da + db, ca * cb % prime, sa | sb)
            else:
                d = max(da, db)
                env[n] = (d, ((ca if da == d else 0) + (cb if db == d else 0) * (1 if op == '+' else -1)) % prime,
                          (sa if da == d else set()) | (sb if db == d else set()))
        d, c, deps = env[p['output']]
        require(d == 1936 and c and not deps, 'SOS exact-degree certificate failed')
        records.append(dict(prime=prime, degree=d, leading_coefficient=c, fixed_parameter_dependencies=[]))
    return dict(exact_degree=1936, certificates=records)


def _normalize(p):
    for key in ('source', 'comparisons', 'polynomial_source'): p[key] = [tuple(r) for r in p[key]]
    return p


@lru_cache(None)
def _bundle(root_text, *path_texts):
    root, paths = _paths(root_text)
    require(tuple(map(str, paths)) == path_texts, 'Dependency path changed')
    parent, affine, unit = [_load(p, '_composed511_' + str(i)) for i, p in enumerate(paths)]
    packets, parents, intermediates, certificates = {}, {}, {}, {}
    for ordinary in (False, True):
        old = parent.build(ordinary, root=root)
        intermediate, proof = affine.rewrite(old)
        _normalize(intermediate)
        require(intermediate['parameters'] == old['parameters'] and intermediate['auxiliaries'] == old['auxiliaries'],
                'Affine composition changed coordinates')
        require(intermediate['ledger']['polynomial']['operations'] == (523 if ordinary else 325), 'Wrong SOS cost')
        for grouped in (False, True):
            p = unit.rewrite(intermediate) if grouped else deepcopy(intermediate)
            _normalize(p)
            require(p['parameters'] == old['parameters'] and p['auxiliaries'] == old['auxiliaries'], 'Unit composition changed coordinates')
            p.update(kind='composed_affine_index_unit_u15', grouped_units=grouped,
                     canonical_parent=dict(file=PARENT_FILE, sha256=PINS[PARENT_FILE]),
                     source_lineage=dict(p['source_lineage'], **PINS),
                     composition=dict(affine_helper='u15_joint_binary_affine_rewrite.py',
                                      unit_helper='u15_packed_unit_product524.py' if grouped else None,
                                      arithmetic_parent_operations=intermediate['ledger']['polynomial']['operations']),
                     parent_relation=('Same full supplied integer zero set as532 via exact affine identity and protected unit grouping.'
                                      if grouped else 'Identical complete polynomial to532 on all supplied tuples.'),
                     scope='Complete fixed-arity ordinary valid-program first-halt relation; unchanged positive coordinates; no new87 bound.')
            wanted = (511 if ordinary else 323) if grouped else (523 if ordinary else 325)
            require(p['ledger']['polynomial']['operations'] == wanted, 'Wrong complete cost')
            degree = unit.degree_audit(p) if grouped else _degree_sos(p)
            require(degree['exact_degree'] == ((4881 if ordinary else 3464) if grouped else 1936), 'Wrong exact degree')
            packets[ordinary, grouped] = p
            certificates[ordinary, grouped] = dict(affine=proof, degree=degree,
                                                  full_integer_zero_equivalence=True,
                                                  full_polynomial_identity=not grouped)
        parents[ordinary], intermediates[ordinary] = old, intermediate
    return dict(parent=parent, affine=affine, unit=unit, packets=packets,
                parents=parents, intermediates=intermediates, certificates=certificates)


def _context(root=None):
    root, paths = _paths(root)
    bundle = _bundle(str(root), *(str(p) for p in paths))
    bundle['parent']._context(root)
    return root, bundle


def build(ordinary=False, *, grouped=True, root=None):
    flag(ordinary, 'ordinary'); flag(grouped, 'grouped')
    return deepcopy(_context(root)[1]['packets'][ordinary, grouped])


def canonical_parent(ordinary=False, *, root=None):
    flag(ordinary, 'ordinary')
    return deepcopy(_context(root)[1]['parents'][ordinary])


def checked(p, *, root=None):
    require(type(p) is dict, 'Complete canonical packet required')
    key = (flag(p.get('ordinary'), 'ordinary'), flag(p.get('grouped_units'), 'grouped_units'))
    require(exact(p, _context(root)[1]['packets'][key]), 'Noncanonical composed U15 packet')
    return p


def polynomial_source(p, *, root=None):
    return deepcopy(checked(p, root=root)['polynomial_source'])


def evaluate(p, values, *, signed=False, root=None):
    p = checked(p, root=root); _, bundle = _context(root); unit = bundle['unit']
    values = unit._assignment(p, values, signed)
    return unit.execute(p['polynomial_source'], values)[p['output']]


def identity(p, values, *, signed=False, root=None):
    """Check complete output formula; grouped output need not equal parent off zeros."""
    p = checked(p, root=root); _, bundle = _context(root); unit = bundle['unit']
    values = unit._assignment(p, values, signed)
    old = bundle['parents'][p['ordinary']]; middle = bundle['intermediates'][p['ordinary']]
    a, b, c = [unit.execute(q['polynomial_source'], values) for q in (old, middle, p)]
    residuals = [unit.at(a, x) - unit.at(a, y) for x, y in old['comparisons']]
    middle_residuals = [unit.at(b, x) - unit.at(b, y) for x, y in middle['comparisons']]
    require(residuals == middle_residuals and a[old['output']] == b[middle['output']], 'Complete affine identity failed')
    if not p['grouped_units']:
        require(c[p['output']] == a[old['output']], 'Ungrouped polynomial changed')
        return dict(parent_output=a[old['output']], child_output=c[p['output']], residuals=residuals,
                    same_polynomial=True)
    product = 1
    for m in p['unit_factors']:
        factor = 1 + m['residual_sign'] * residuals[m['old_index']]
        require(factor == c[m['factor']], 'Composed unit factor identity failed')
        if m['kind'] != 'checksum': require(factor % 4 != 3, 'Protected norm residue failed')
        product *= factor
    remaining = 0
    for m in p['unit_retained_comparison_map']:
        x, y = p['comparisons'][m['new_index']]
        r = unit.at(c, x) - unit.at(c, y)
        require(r == residuals[m['old_index']], 'Retained composed residual changed')
        remaining += r * r
    expected = remaining + (product - 1) ** 2 if p['finalizer'] == 'sos' else product * (1 + remaining) - 1
    require(product == c[p['unit_product_register']] and expected == c[p['output']], 'Whole unit finalizer identity failed')
    require((a[old['output']] == 0) == (expected == 0), 'Zero-set equivalence failed')
    return dict(parent_output=a[old['output']], child_output=expected, unit_product=product,
                remaining_square_sum=remaining, residuals=residuals, same_polynomial=False)


def verify(root=None):
    root, bundle = _context(root); rng = random.Random(511323); counts = Counter(); forms = []
    def reject(fn):
        try: fn()
        except (ValueError, TypeError, KeyError): counts['malformed_calls_rejected'] += 1; return
        raise AssertionError('Malformed call accepted')
    for ordinary in (False, True):
        for grouped in (False, True):
            p = build(ordinary, grouped=grouped, root=root)
            for case in range(24):
                signed = case >= 12
                v = {n: rng.randrange(-4, 5) if signed else rng.randrange(1, 6)
                     for n in p['parameters'] + p['auxiliaries']}
                result = identity(p, v, signed=signed, root=root)
                counts['complete_output_identities'] += 1; counts['signed_cases'] += signed
                counts['original_residual_checks'] += len(result['residuals'])
            v = {n: 1 for n in p['parameters'] + p['auxiliaries']}
            for n in list(v)[::3]:
                for bad in (True, 1.0, None):
                    vv = dict(v); vv[n] = bad
                    reject(lambda vv=vv: evaluate(p, vv, root=root))
            for bad in (0, 1, 0.0, None, 'yes'):
                reject(lambda bad=bad: build(bad, grouped=grouped, root=root))
                reject(lambda bad=bad: build(ordinary, grouped=bad, root=root))
                reject(lambda bad=bad: evaluate(p, v, signed=bad, root=root))
            for key in ('source', 'polynomial_source', 'comparisons', 'composition', 'source_lineage', 'ledger', 'canonical_parent'):
                altered = deepcopy(p); altered[key] = None
                reject(lambda altered=altered: checked(altered, root=root))
            altered = build(ordinary, grouped=grouped, root=root); altered['source'].clear()
            require(exact(build(ordinary, grouped=grouped, root=root), p), 'Packet cache leaked')
            altered = polynomial_source(p, root=root); altered.clear()
            require(exact(polynomial_source(p, root=root), p['polynomial_source']), 'Source cache leaked')
            counts['defensive_copy_checks'] += 2
            forms.append(dict(ordinary=ordinary, grouped=grouped, compiler=p,
                              certificate=bundle['certificates'][ordinary, grouped]))
    return dict(status='PASS_COMPLETE_U15_511', source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                dependency_pins=PINS, counts=dict(counts), forms=forms)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path); parser.add_argument('--write', action='store_true')
    args = parser.parse_args(); result = json.loads(json.dumps(verify(args.root)))
    path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    else: require(exact(result, json.loads(path.read_text())), 'Saved receipt differs')
    print(json.dumps(dict(status=result['status'], counts=result['counts'],
                         forms=[dict(ordinary=f['ordinary'], grouped=f['grouped'], ledger=f['compiler']['ledger'],
                                     exact_degree=f['certificate']['degree']['exact_degree']) for f in result['forms']]), indent=2))
