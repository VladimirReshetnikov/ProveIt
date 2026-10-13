"""Exact intrinsic coordinates for a single shared nonnegative port.

This polynomial preprocessor preserves synchronized feasible vectors and all
linear objectives. It does not enumerate rays, select geometric separators,
or decide whether a normal surface is an essential disc. In particular, local
rays must be recomputed after restriction to the common image subspace.
"""

from dataclasses import dataclass
from fractions import Fraction as Q


def _q(value):
    if isinstance(value, (bool, float)) or not isinstance(value, (int, str, Q)):
        raise ValueError('exact rational input required')
    return Q(value)


def _matrix(rows, width):
    result = tuple(tuple(_q(x) for x in row) for row in rows)
    if any(len(row) != width for row in result):
        raise ValueError('matrix width mismatch')
    return result


def _dot(a, b):
    return sum((x*y for x, y in zip(a, b)), Q(0))


def _rref(rows, width, check):
    a = [list(row) for row in rows if any(row)]
    pivots = []
    for j in range(width):
        check()
        i = len(pivots)
        p = next((p for p in range(i, len(a)) if a[p][j]), None)
        if p is None:
            continue
        a[i], a[p] = a[p], a[i]
        scale = a[i][j]
        a[i] = [x/scale for x in a[i]]
        for k in range(len(a)):
            check()
            if k != i and a[k][j]:
                scale = a[k][j]
                a[k] = [x-scale*y for x, y in zip(a[k], a[i])]
        pivots.append(j)
        if len(pivots) == len(a):
            break
    return tuple(tuple(row) for row in a[:len(pivots)]), tuple(pivots)


def _kernel(rows, width, check):
    a, pivots = _rref(rows, width, check)
    basis = []
    for j in range(width):
        check()
        if j not in pivots:
            v = [Q(0)]*width
            v[j] = Q(1)
            for row, pivot in zip(a, pivots):
                v[pivot] = -row[j]
            basis.append(tuple(v))
    return tuple(basis)


@dataclass(frozen=True)
class PortBlock:
    """The cone x >= 0, A x = 0, with pair conflicts and port P x >= 0."""

    n: int
    equations: tuple
    ports: tuple
    conflicts: tuple = ()

    def __post_init__(self):
        if type(self.n) is not int or self.n < 1:
            raise ValueError('positive coordinate count required')
        object.__setattr__(self, 'equations', _matrix(self.equations, self.n))
        object.__setattr__(self, 'ports', _matrix(self.ports, self.n))
        if not self.ports or any(x < 0 for row in self.ports for x in row):
            raise ValueError('entrywise nonnegative nonempty port matrix required')
        pairs = set()
        for pair in self.conflicts:
            if (len(pair) != 2 or any(type(j) is not int or not 0 <= j < self.n for j in pair)
                    or pair[0] == pair[1]):
                raise ValueError('invalid coordinate conflict')
            pairs.add(tuple(sorted(pair)))
        object.__setattr__(self, 'conflicts', tuple(sorted(pairs)))

    def image(self, vector):
        vector = tuple(_q(x) for x in vector)
        if len(vector) != self.n:
            raise ValueError('vector dimension mismatch')
        return tuple(_dot(row, vector) for row in self.ports)


@dataclass(frozen=True)
class CommonPortReduction:
    """Rows of lift_basis form a basis of the common image subspace.

    At selected coordinates this basis is the identity. Dimension zero uses
    one identically zero port row in each block for nonempty-port APIs.
    The reduced projective normalization generally differs from the original
    normalization: objective signs, not normalized optimal values, agree.
    """

    original_blocks: tuple
    blocks: tuple
    lift_basis: tuple
    coordinates: tuple
    local_image_dimensions: tuple
    original_nullities: tuple
    restricted_nullities: tuple

    @property
    def dimension(self):
        return len(self.coordinates)

    def lift_port(self, port):
        z = tuple(_q(x) for x in port)
        if len(z) != max(1, self.dimension):
            raise ValueError('reduced port dimension mismatch')
        d = len(self.original_blocks[0].ports)
        if not self.dimension:
            if any(z):
                raise ValueError('zero-dimensional port must vanish')
            return (Q(0),)*d
        return tuple(sum((z[i]*self.lift_basis[i][j] for i in range(self.dimension)), Q(0))
                     for j in range(d))

    def reduce_master(self, objective):
        cost = tuple(_q(x) for x in objective)
        if len(cost) != len(self.original_blocks[0].ports):
            raise ValueError('master objective dimension mismatch')
        return tuple(_dot(row, cost) for row in self.lift_basis) or (Q(0),)


def compress_common_ports(blocks, *, check=lambda: None):
    """Restrict to W = intersection(P_i ker(A_i)) and select coordinates on W.

    Exact Gaussian elimination is polynomial in the binary matrix input size.
    No nonnegative feasibility or compatibility is discarded: every original
    synchronized tuple lies in W. Selected port rows remain nonnegative even
    when the full-port lifting basis has signed entries. Resource/cancellation
    exceptions from check propagate unchanged, including on empty input.
    """
    check()
    original = tuple(blocks)
    if (not original or any(not isinstance(b, PortBlock) for b in original)
            or len({len(b.ports) for b in original}) != 1):
        raise ValueError('nonempty PortBlocks with equal port dimensions required')
    d = len(original[0].ports)
    annihilators = []
    local_dims, nullities = [], []
    for b in original:
        check()
        kernel = _kernel(b.equations, b.n, check)
        nullities.append(len(kernel))
        images = tuple(b.image(v) for v in kernel)
        annihilator = _kernel(images, d, check)
        local_dims.append(d-len(annihilator))
        annihilators.extend(annihilator)
    # Sum of annihilators is the annihilator of the intersection.
    constraints, _ = _rref(annihilators, d, check)
    lift, coordinates = _rref(_kernel(constraints, d, check), d, check)
    reduced, restricted_nullities = [], []
    for b in original:
        added = []
        for row in constraints:
            check()
            added.append(tuple(sum((row[j]*b.ports[j][k] for j in range(d)), Q(0))
                               for k in range(b.n)))
        equations, pivots = _rref(b.equations+tuple(added), b.n, check)
        restricted_nullities.append(b.n-len(pivots))
        ports = tuple(b.ports[j] for j in coordinates) or ((Q(0),)*b.n,)
        reduced.append(PortBlock(b.n, equations, ports, b.conflicts))
    return CommonPortReduction(original, tuple(reduced), lift, coordinates,
                               tuple(local_dims), tuple(nullities), tuple(restricted_nullities))
