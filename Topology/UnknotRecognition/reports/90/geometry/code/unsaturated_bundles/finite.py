"""Terminal handlebody census for unsaturated interval-bundle attachments.

The finite model does not authenticate a three-manifold or its embedded
decomposition.  The native adapter supplies that separate source obligation.
No numerical genus, crosscap number or multiplicity is a loop bound here.
"""

from collections import Counter
import hashlib
import json


def encode(value):
    """Portable exact integers, including values beyond Python's decimal cap."""
    if type(value) is int:
        return hex(value)
    if isinstance(value, dict):
        return {k: encode(v) for k, v in value.items()}
    if isinstance(value, list):
        return [encode(v) for v in value]
    return value


def decode(value):
    if isinstance(value, str) and value.startswith(('0x', '-0x')):
        return int(value, 16)
    if isinstance(value, dict):
        return {k: decode(v) for k, v in value.items()}
    if isinstance(value, list):
        return [decode(v) for v in value]
    return value


def digest(model):
    payload = json.dumps(encode(model), sort_keys=True, separators=(',', ':'))
    return hashlib.sha256(payload.encode()).hexdigest()


def _integer(value, minimum=None):
    if type(value) is not int or (minimum is not None and value < minimum):
        raise ValueError('invalid exact integer')
    return value


def validate_model(model):
    if type(model) is not dict or set(model) != {'cores', 'bases', 'attachments'}:
        raise ValueError('invalid finite model schema')
    for name in model:
        if type(model[name]) is not list:
            raise ValueError('model fields must be lists')
    cores, bases, seen = {}, {}, set()
    for core in model['cores']:
        if type(core) is not dict or set(core) != {'id', 'genus'}:
            raise ValueError('invalid core record')
        key = _integer(core['id'], 0)
        _integer(core['genus'], 0)
        if key in cores:
            raise ValueError('duplicate core identifier')
        cores[key] = core
    for base in model['bases']:
        if type(base) is not dict or set(base) != {
                'id', 'chi', 'boundary', 'orientable', 'multiplicity'}:
            raise ValueError('invalid base record')
        key = _integer(base['id'], 0)
        chi = _integer(base['chi'])
        boundary = _integer(base['boundary'], 0)
        _integer(base['multiplicity'], 1)
        if type(base['orientable']) is not bool or key in bases:
            raise ValueError('invalid orientation or duplicate base identifier')
        deficit = 2 - chi - boundary
        if base['orientable']:
            if deficit < 0 or deficit % 2:
                raise ValueError('invalid orientable surface type')
        elif deficit < 1:
            raise ValueError('invalid nonorientable surface type')
        bases[key] = base
    by_base = {key: [] for key in bases}
    for edge in model['attachments']:
        if type(edge) is not dict or set(edge) != {'id', 'base', 'core', 'kind'}:
            raise ValueError('invalid attachment record')
        key = _integer(edge['id'], 0)
        base, core = _integer(edge['base'], 0), _integer(edge['core'], 0)
        if key in seen or base not in bases or core not in cores:
            raise ValueError('invalid attachment incidence')
        seen.add(key)
        if edge['kind'] not in ('interval', 'circle'):
            raise ValueError('unknown attachment kind')
        by_base[base].append(edge)
    for key, attachments in by_base.items():
        base = bases[key]
        c = sum(edge['kind'] == 'circle' for edge in attachments)
        if c > base['boundary']:
            raise ValueError('too many attached boundary circles')
        if attachments and base['multiplicity'] != 1:
            raise ValueError('an attached actual base has multiplicity one')
        if base['boundary'] == 0 and attachments:
            raise ValueError('a closed base has no boundary attachments')
        if c == base['boundary'] and any(
                edge['kind'] == 'interval' for edge in attachments):
            raise ValueError('intervals cannot remain on a saturated boundary')
    return cores, bases, by_base


def census(model, *, check=lambda: None):
    """Compute the exact terminal census under the geometric input contract.

    COMPLETE is conditional on every core being the indicated handlebody and
    every base being its genuine embedded orientable interval bundle. The
    result does not retain transported boundary markings or a homeomorphism.
    """
    check()
    cores, bases, by_base = validate_model(model)
    closed = sorted(key for key, base in bases.items() if base['boundary'] == 0)
    if closed:
        return dict(status='INCONCLUSIVE', reason='closed_bundle_base', bases=closed)
    saturated = sorted(key for key, base in bases.items()
        if by_base[key] and sum(e['kind'] == 'circle' for e in by_base[key])
        == base['boundary'])
    if saturated:
        return dict(status='INCONCLUSIVE', reason='saturated_bundle_base', bases=saturated)
    nodes = [('core', key) for key in cores]
    nodes += [('base', key) for key in bases if by_base[key]]
    parent = {node: node for node in nodes}

    def root(node):
        while parent[node] != node:
            parent[node] = parent[parent[node]]
            node = parent[node]
        return node

    for edge in model['attachments']:
        check()
        left, right = root(('core', edge['core'])), root(('base', edge['base']))
        if left != right:
            parent[max(left, right)] = min(left, right)
    groups = {}
    for node in nodes:
        groups.setdefault(root(node), []).append(node)
    local = {}
    for key, edges in by_base.items():
        if edges:
            a = sum(edge['kind'] == 'interval' for edge in edges)
            c = len(edges) - a
            local[key] = dict(base=key, intervals=a, circles=c,
                             one_handles=a - bases[key]['chi'],
                             residual_rank=1 - bases[key]['chi'] - c)
    joined, histogram = [], Counter()
    for key, vertices in sorted(groups.items()):
        check()
        core_ids = sorted(v for t, v in vertices if t == 'core')
        base_ids = sorted(v for t, v in vertices if t == 'base')
        attached = sorted(e['id'] for e in model['attachments']
                          if root(('core', e['core'])) == key)
        cycle_rank = len(attached) - len(vertices) + 1
        residual_rank = sum(local[b]['residual_rank'] for b in base_ids)
        genus = sum(cores[c]['genus'] for c in core_ids) + residual_rank + cycle_rank
        if min(cycle_rank, residual_rank, genus) < 0:
            raise ArithmeticError('invalid relative handle count')
        joined.append(dict(cores=core_ids, bases=base_ids, attachments=attached,
                           cycle_rank=cycle_rank, residual_rank=residual_rank,
                           genus=genus))
        histogram[genus] += 1
    isolated = []
    for key, base in sorted(bases.items()):
        check()
        if not by_base[key]:
            genus, copies = 1 - base['chi'], base['multiplicity']
            histogram[genus] += copies
            isolated.append(dict(base=key, genus=genus, multiplicity=copies))
    euler = sum((1 - g) * count for g, count in histogram.items())
    expected = (sum(1 - core['genus'] for core in cores.values())
        + sum(base['chi'] * base['multiplicity'] for base in bases.values())
        - sum(e['kind'] == 'interval' for e in model['attachments']))
    if euler != expected:
        raise ArithmeticError('relative handlebody Euler check failed')
    components = sum(histogram.values())
    return dict(status='COMPLETE',
        census=dict(histogram=[dict(genus=g, multiplicity=n)
                              for g, n in sorted(histogram.items())],
                    components=components, ball_components=histogram[0],
                    one_ball=(components == 1 and histogram[0] == 1),
                    euler_characteristic=euler, joined=joined, isolated=isolated,
                    reductions=[local[key] for key in sorted(local)]))


def make_certificate(model, *, check=lambda: None):
    result = census(model, check=check)
    if result['status'] == 'COMPLETE':
        result['certificate'] = dict(schema='unsaturated-bundles-v1',
            input_sha256=digest(model), census=result['census'])
    return result
