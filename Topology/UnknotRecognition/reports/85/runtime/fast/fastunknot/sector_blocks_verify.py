"""Independent replay of coordinate-block canonical Euler certificates.

The checker uses the existing uncontracted dense source model.  It does not
import the block producer, its RREF basis canonicalizer, or its union-find.
Local ray coverage is delegated to the existing independent Q verifier.
"""

from .normal_sector_verify import (
    _allowed, _digest, _kernel, dense_sector_model, dense_reference_rays, verify_sector_exhaustion,
)
from .normal_surface_geometry import _coordinates, NormalOrbitError
from .integer_codec import encoded_integer


def _restricted_dense_model(model, indices, check):
    """Restrict the independently reconstructed model, keeping source authority."""
    triangle_columns = 4 * len(model['prepared']['tetrahedra'])
    columns = list(range(triangle_columns)) + [triangle_columns + i for i in indices]
    constraints = [[row[i] for i in indices] for row in model['constraints']]
    return dict(prepared=model['prepared'], support=[model['support'][i] for i in indices],
                matrix=[[row[i] for i in columns] for row in model['matrix']],
                potentials=[[row[i] for i in indices] for row in model['potentials']],
                groups=model['groups'], constraints=constraints,
                basis=_kernel(constraints, len(indices), check))


def verify_block_euler(triangulation, certificate, *, check=lambda: None):
    """Verify the advertised canonical Euler statement, never a knot claim."""
    check()
    if type(certificate) is not dict:
        return False
    schema = certificate.get('schema')
    if schema not in ('normal-sector-block-euler-v1',
                      'normal-sector-block-positive-euler-v1'):
        return False
    if certificate.get('source_sha256') != _digest(triangulation):
        return False
    try:
        support = _allowed(certificate.get('allowed_types'), len(triangulation['tetrahedra']))
        model = dense_sector_model(triangulation, support, check=check)
    except (ValueError, KeyError, TypeError, NormalOrbitError):
        return False
    if schema == 'normal-sector-block-positive-euler-v1':
        try:
            analysed = _coordinates(model['prepared'], certificate.get('coordinates'), check)
        except NormalOrbitError:
            return False
        rows = analysed['rows']
        permitted = set(support)
        if any(row[4 + typ] and (t, typ) not in permitted
               for t, row in enumerate(rows) for typ in range(3)):
            return False
        if not any(row[4 + typ] for row in rows for typ in range(3)):
            return False
        if any(min(rows[c // 4][c % 4] for c in group) != 0
               for group in model['groups'].values()):
            return False
        return analysed['euler_characteristic'] > 0
    entries = certificate.get('blocks')
    if type(entries) is not list:
        return False
    blocks = []
    seen = set()
    for entry in entries:
        check()
        if type(entry) is not dict or type(entry.get('indices')) is not list:
            return False
        indices = entry['indices']
        if (not indices or any(type(i) is not int or not 0 <= i < len(support) for i in indices)
                or indices != sorted(set(indices)) or seen.intersection(indices)):
            return False
        seen.update(indices)
        blocks.append(indices)
        proof = entry.get('certificate')
        if (type(proof) is not dict or proof.get('phase') != 'quadrilateral'
                or proof.get('status') != 'NO_POSITIVE_EULER'
                or proof.get('allowed_types') != [list(support[i]) for i in indices]):
            return False
    # Every source-kernel vector must split into the displayed coordinate
    # subspaces.  Checking the independent dense basis suffices by linearity.
    for vector in model['basis']:
        check()
        if any(value and i not in seen for i, value in enumerate(vector)):
            return False
        for indices in blocks:
            for equation in model['constraints']:
                check()
                if sum(equation[i] * vector[i] for i in indices):
                    return False
    for entry in entries:
        check()
        if not verify_sector_exhaustion(triangulation, entry['certificate'], check=check):
            return False
    return True


def verify_block_ray_certificate(triangulation, certificate, *, check=lambda: None):
    """Check exact Q or standard ray coverage with local dense reconstructions."""
    check()
    if (type(certificate) is not dict
            or certificate.get('schema') != 'normal-sector-block-rays-v1'
            or certificate.get('source_sha256') != _digest(triangulation)
            or certificate.get('phase') not in ('quadrilateral', 'standard')):
        return False
    try:
        support = _allowed(certificate.get('allowed_types'), len(triangulation['tetrahedra']))
        model = dense_sector_model(triangulation, support, check=check)
    except (ValueError, KeyError, TypeError, NormalOrbitError):
        return False
    entries = certificate.get('blocks')
    if type(entries) is not list:
        return False
    seen, blocks = set(), []
    for entry in entries:
        check()
        if type(entry) is not dict or type(entry.get('indices')) is not list:
            return False
        indices = entry['indices']
        if (not indices or any(type(i) is not int or not 0 <= i < len(support) for i in indices)
                or indices != sorted(set(indices)) or seen.intersection(indices)):
            return False
        seen.update(indices)
        blocks.append(indices)
    for vector in model['basis']:
        check()
        if any(value and i not in seen for i, value in enumerate(vector)):
            return False
        for indices in blocks:
            for equation in model['constraints']:
                check()
                if sum(equation[i] * vector[i] for i in indices):
                    return False
    if certificate['phase'] == 'standard':
        # A global vertex may carry nonconstant triangle-potential differences
        # in at most one submitted cluster.  Projection of the full dense basis
        # spans every local matching subspace by the checks above.
        for corners in model['groups'].values():
            check()
            anchor = model['potentials'][corners[0]]
            varying = 0
            for indices in blocks:
                if any(sum((model['potentials'][c][i] - anchor[i]) * vector[i]
                           for i in indices)
                       for c in corners[1:] for vector in model['basis']):
                    varying += 1
            if varying > 1:
                return False
    for entry, indices in zip(entries, blocks):
        check()
        submitted = entry.get('quadrilaterals')
        if (type(submitted) is not list
                or any(type(row) is not list or len(row) != len(indices) for row in submitted)):
            return False
        try:
            submitted = [tuple(encoded_integer(value) for value in row) for row in submitted]
        except (ValueError, TypeError):
            return False
        if any(value < 0 for row in submitted for value in row):
            return False
        if len(set(submitted)) != len(submitted):
            return False
        local = _restricted_dense_model(model, indices, check)
        expected = dense_reference_rays(local, certificate['phase'], check=check)
        if set(submitted) != set(expected):
            return False
    return True
