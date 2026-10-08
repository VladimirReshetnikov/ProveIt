"""Check a proposed graph quotient against an independently rebuilt closed PD.

This is a verifier, not an automatic producer of terminal partitions. It
costs O(N^2) matrix comparisons per query and does not establish that the
faster boundary-only extraction route is available for arbitrary frontiers.
"""
from .linalg import signed_laplacian, quotient_cofactor


def verify_quotient_geometry(laplacian, terminals, partition, diagram, permutation):
    """Return the raw (-i) phase if a supplied cofactor identification is valid.

    `permutation[i]` is the row/column of the actual Tait cofactor corresponding
    to row/column i of the proposed quotient cofactor. Grounded actual Tait
    vertex zero is fixed by the independent PD construction. The kernel's
    separate block-identity certificate must also be checked before trusting
    a result computed from an externally supplied kernel.
    """
    vertices, edges, phase = diagram.tait_data()
    actual = signed_laplacian(vertices, edges)
    actual = [row[1:] for row in actual[1:]]
    proposed = quotient_cofactor(laplacian, terminals, partition)
    d = len(proposed)
    if len(actual) != d or sorted(permutation) != list(range(d)):
        raise ValueError('invalid cofactor vertex identification')
    if any(proposed[i][j] != actual[permutation[i]][permutation[j]]
           for i in range(d) for j in range(d)):
        raise ValueError('proposed graph quotient does not match the actual Tait cofactor')
    return phase
