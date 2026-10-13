"""Independent negative Euler relaxations and complete quadrilateral branch trees.

Unlike a compatible sector, a relaxation may allow several quadrilateral types
in one tetrahedron. Its nonnegative matching cone is a superset: a negative
Euler bound excludes every admissible surface supported there, whereas a
positive relaxed point has no topological meaning without compatibility checks.
This module verifies only negative statements. It imports no LP solver, search
producer, sector constructor or ray enumerator.
"""
from collections import OrderedDict
from hashlib import sha256
from itertools import product
from math import prod
import json

from .normal_surface_geometry import _prepare
from .normal_euler_verify import _reference_model, _rational


_REPLAY_CACHE_LIMIT = 256


class _CallbackRaised(BaseException):
    def __init__(self, error):
        self.error = error
        self.traceback = error.__traceback__


def _safe_call(function, triangulation, certificate, check):
    def guarded():
        try:
            check()
        except BaseException as error:
            raise _CallbackRaised(error) from None
    try:
        return function(triangulation, certificate, guarded)
    except _CallbackRaised as interruption:
        raise interruption.error.with_traceback(interruption.traceback) from None
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, OverflowError):
        return False


def _mask(value, tetrahedra, check):
    """Strict JSON mask; repeated tetrahedra are allowed, repeated pairs are not."""
    if type(value) is not list or len(value) > 3*tetrahedra:
        raise ValueError('expected a quadrilateral type mask')
    result = []
    previous = (-1, -1)
    for pair in value:
        check()
        if (type(pair) is not list or len(pair) != 2
                or any(type(x) is not int for x in pair)
                or not 0 <= pair[0] < tetrahedra or not 0 <= pair[1] < 3):
            raise ValueError('invalid quadrilateral mask entry')
        entry = tuple(pair)
        if entry <= previous:
            raise ValueError('mask entries must be unique and sorted')
        result.append(entry)
        previous = entry
    return tuple(result)


def _digest(triangulation):
    return sha256(json.dumps(triangulation, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def _header(certificate, schema, digest):
    return (type(certificate) is dict
            and type(certificate.get('schema')) is str and certificate['schema'] == schema
            and type(certificate.get('status')) is str and certificate['status'] == 'NO_POSITIVE_EULER'
            and type(certificate.get('source_sha256')) is str and certificate['source_sha256'] == digest)


def _dual(value, rows):
    if type(value) is not list or len(value) != rows:
        raise ValueError('dual does not cover the reconstructed matching rows')
    return tuple(_rational(x) for x in value)


def _dominates(matrix, dual, objective, columns, check):
    for j in columns:
        check()
        if sum(row[j]*coefficient for row, coefficient in zip(matrix, dual)) < objective[j]:
            return False
    return True


def _cached(cache, key, build, check):
    """Bounded source-local exact values, never cached acceptance decisions."""
    check()
    if key in cache:
        cache.move_to_end(key)
        return cache[key]
    value = build()
    if _REPLAY_CACHE_LIMIT:
        cache[key] = value
        if len(cache) > _REPLAY_CACHE_LIMIT:
            cache.popitem(last=False)
    return value


def _dual_image(matrix, dual, width, check):
    image = []
    for j in range(width):
        check()
        image.append(sum(row[j]*coefficient for row, coefficient in zip(matrix, dual)))
    return tuple(image)


def _euler_objective(linear, groups, potentials, weights, anchors, check):
    objective = list(linear)
    if anchors is None:
        for group, weight in zip(groups, weights):
            check()
            for j in range(len(linear)):
                objective[j] -= weight*min(potentials[c][j] for c in group)
    else:
        for anchor, weight in zip(anchors, weights):
            check()
            for j, value in enumerate(potentials[anchor]):
                objective[j] -= weight*value
    return tuple(objective)


def _source_dominates(source_model, dual, anchors, columns, check):
    matrix, linear, groups, potentials, weights = source_model['model']
    images = source_model.setdefault('dual_images', OrderedDict())
    objectives = source_model.setdefault('objectives', OrderedDict())
    # Parsed exact rational tuples identify duals; equivalent encodings share
    # arithmetic only after the caller has validated every supplied field.
    image = _cached(images, dual, lambda: _dual_image(matrix, dual, len(linear), check), check)
    objective = _cached(objectives, anchors, lambda: _euler_objective(
        linear, groups, potentials, weights, anchors, check), check)
    for j in columns:
        check()
        if image[j] < objective[j]:
            return False
    return True


def _leaf(prepared, digest, certificate, check, *, expected_mask=None, source_model=None):
    check()
    if not (type(certificate) is dict and
            certificate.get('schema') in ('normal-euler-relaxation-v1', 'normal-euler-relaxation-v2')
            and _header(certificate, certificate['schema'], digest)):
        return False
    common = {'schema', 'status', 'source_sha256', 'allowed_types', 'proof_kind'}
    kind = certificate.get('proof_kind')
    if type(kind) is not str or kind not in ('envelope', 'anchors'):
        return False
    if set(certificate) != common | ({'multipliers'} if kind == 'envelope' else {'duals'}):
        return False
    mask = _mask(certificate['allowed_types'], len(prepared['tetrahedra']), check)
    if expected_mask is not None and mask != expected_mask:
        return False
    # The source-only reconstruction is valid for multiple allowed Q types:
    # compatibility is deliberately relaxed, but matching is never changed.
    if certificate['schema'] == 'normal-euler-relaxation-v2':
        if source_model is None:
            source_model = {}
        if 'model' not in source_model:
            full = tuple((t, q) for t in range(len(prepared['tetrahedra'])) for q in range(3))
            source_model['model'] = _reference_model(prepared, full, check)
        matrix, linear, groups, potentials, weights = source_model['model']
        columns = tuple(3*t+q for t, q in mask)
    else:
        matrix, linear, groups, potentials, weights = _reference_model(prepared, mask, check)
        columns = range(len(mask))
    def dominates(dual, anchors):
        if certificate['schema'] == 'normal-euler-relaxation-v2':
            return _source_dominates(source_model, dual, anchors, columns, check)
        objective = _euler_objective(linear, groups, potentials, weights, anchors, check)
        return _dominates(matrix, dual, objective, columns, check)
    if kind == 'envelope':
        dual = _dual(certificate['multipliers'], len(matrix))
        valid = dominates(dual, None)
        check()
        return valid
    records = certificate['duals']
    if type(records) is not list or len(records) != prod(map(len, groups)):
        return False
    for anchors, record in zip(product(*groups), records):
        check()
        if (type(record) is not dict or set(record) != {'anchors', 'multipliers'}
                or type(record['anchors']) is not list
                or any(type(x) is not int for x in record['anchors'])
                or record['anchors'] != list(anchors)):
            return False
        dual = _dual(record['multipliers'], len(matrix))
        if not dominates(dual, anchors):
            return False
    check()
    return True


def verify_euler_relaxation_certificate(triangulation, certificate, *, check=lambda: None):
    """Prove no positive canonical Euler value anywhere in the supplied mask.

    All source matching equations are retained. The mask may allow multiple
    types in a tetrahedron. A negative relaxation excludes every compatible
    sector contained in that mask; it makes no claim about omitted types or
    diagram provenance. Malformed packets return False; caller exceptions
    propagate unchanged, including exceptions used for malformed-input errors.

    Version 1 reconstructs the model on the given mask. Version 2 fixes the
    model on all three quadrilateral types at every source tetrahedron, with
    the full cycle-row and anchor conventions, but tests dual inequalities
    only on allowed mask columns. Reusing a v2 dual on a smaller mask is sound
    because its source rows and Euler objectives have not changed.
    """
    return _safe_call(_verify_relaxation, triangulation, certificate, check)


def _verify_relaxation(triangulation, certificate, check):
    check()
    prepared = _prepare(triangulation, check)
    return _leaf(prepared, _digest(triangulation), certificate, check)


def verify_euler_branch_tree(triangulation, certificate, *, check=lambda: None):
    """Verify complete admissible coverage of a root mask by a flat preorder tree.

    A split chooses a currently ambiguous tetrahedron. Its implicit children
    retain each allowed type there in ascending order, keeping all other mask
    entries. A zero quad count belongs to every child, so these choices cover
    all admissible vectors. Leaf bounds are checked against exactly their
    derived context. Nodes contain no trusted masks, child counts or pointers.
    Version 1 and version 2 negative leaves may be mixed. The full source model
    needed by version 2 is reconstructed at most once during a tree replay.
    Independently computed full dual products and Euler objectives each retain
    at most 256 entries within this call. Every field and every current-mask
    inequality is checked again, including on cache hits.
    """
    return _safe_call(_verify_tree, triangulation, certificate, check)


def _verify_tree(triangulation, certificate, check):
    check()
    prepared = _prepare(triangulation, check)
    digest = _digest(triangulation)
    if (not _header(certificate, 'normal-euler-branch-tree-v1', digest)
            or set(certificate) != {'schema', 'status', 'source_sha256', 'allowed_types', 'nodes'}
            or type(certificate['nodes']) is not list):
        return False
    count = len(prepared['tetrahedra'])
    root = _mask(certificate['allowed_types'], count, check)
    pending = [root]
    source_model = {}
    for node in certificate['nodes']:
        check()
        if not pending or type(node) is not dict or type(node.get('kind')) is not str:
            return False
        mask = pending.pop()
        if node['kind'] == 'negative':
            if (set(node) != {'kind', 'certificate'}
                    or not _leaf(prepared, digest, node['certificate'], check,
                                 expected_mask=mask, source_model=source_model)):
                return False
        elif node['kind'] == 'split':
            if (set(node) != {'kind', 'tetrahedron'}
                    or type(node['tetrahedron']) is not int
                    or not 0 <= node['tetrahedron'] < count):
                return False
            tetrahedron = node['tetrahedron']
            choices = tuple(q for t, q in mask if t == tetrahedron)
            if len(choices) < 2:
                return False
            # Reverse push gives ascending children in the flat preorder.
            for choice in reversed(choices):
                pending.append(tuple(pair for pair in mask
                                     if pair[0] != tetrahedron or pair[1] == choice))
        else:
            return False
    check()
    return not pending
