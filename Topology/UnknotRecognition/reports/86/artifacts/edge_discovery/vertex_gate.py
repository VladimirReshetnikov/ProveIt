"""Polynomial rank-and-boundary certificate for a primitive vertex disc.

Only the existing finite-manifold and normal-coordinate validators are
reused.  Rank selection, fraction-free determinant replay, and the boundary
cohomology quotient are implemented here.  No component-orbit or normal-disc
discovery routine is imported.  This is a supplementary research artifact,
not a change to the frozen edge-defect discovery module or its benchmarks.

Input JSON for the CLI contains 'triangulation' and 'coordinates'.  The
'produce' command adds 'certificate'; 'verify' independently replays it.
"""

import argparse
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
import json
from math import gcd
from pathlib import Path

from fastunknot.normal_surface_geometry import (
    _prepare, _coordinates, _edge, NormalOrbitError,
)


_FIELDS = {
    'schema', 'source_sha256', 'support', 'minor_rows', 'minor_columns',
    'minor_determinant', 'boundary_edges', 'boundary_parity',
    'coboundary_rank', 'augmented_rank', 'euler_characteristic', 'primitive_gcd',
}


def _binding(triangulation, rows):
    body = dict(triangulation=triangulation,
                coordinates=[[hex(value) for value in row] for row in rows])
    return sha256(json.dumps(body, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def _minor_determinant(matrix, check=lambda: None):
    """Bareiss elimination with row pivoting; det(empty)=1."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError('determinant requires a square matrix')
    if n == 0:
        return 1
    a = [row.copy() for row in matrix]
    previous, sign = 1, 1
    for column in range(n-1):
        check()
        pivot = next((r for r in range(column, n) if a[r][column]), None)
        if pivot is None:
            return 0
        if pivot != column:
            a[pivot], a[column] = a[column], a[pivot]
            sign = -sign
        value = a[column][column]
        for r in range(column+1, n):
            check()
            multiplier = a[r][column]
            for c in range(column+1, n):
                numerator = value*a[r][c]-multiplier*a[column][c]
                quotient, remainder = divmod(numerator, previous)
                if remainder:
                    raise ArithmeticError('fraction-free minor division was not exact')
                a[r][c] = quotient
            a[r][column] = 0
        previous = value
    return sign*a[-1][-1]


def _find_rank_minor(equations, support, check=lambda: None):
    """Select independent original rows/columns by sparse rational elimination."""
    present = set(support)
    pivots, selected_rows, selected_columns = {}, [], []
    for original, equation in enumerate(equations):
        check()
        row = {i: Fraction(value) for i, value in equation.items()
               if i in present and value}
        while row:
            check()
            column = min(row)
            if column not in pivots:
                value = row[column]
                pivots[column] = {i: x/value for i, x in row.items()}
                selected_rows.append(original)
                selected_columns.append(column)
                break
            multiplier = row[column]
            for i, value in pivots[column].items():
                changed = row.get(i, 0)-multiplier*value
                if changed:
                    row[i] = changed
                else:
                    row.pop(i, None)
        if len(selected_rows) == len(support)-1:
            return selected_rows, selected_columns
    return None


def _binary_rank(vectors, check=lambda: None):
    pivots = {}
    for vector in vectors:
        check()
        while vector:
            pivot = vector.bit_length()-1
            if pivot in pivots:
                vector ^= pivots[pivot]
            else:
                pivots[pivot] = vector
                break
    return len(pivots)


def _boundary_quotient(prepared, analysed, check=lambda: None):
    """Check a parity cocycle modulo all boundary-vertex coboundaries."""
    edges = sorted(prepared['boundary_incidence'])
    index = {edge: i for i, edge in enumerate(edges)}
    parity = [analysed['weights'][edge] & 1 for edge in edges]
    for tetrahedron, face in prepared['boundary_faces']:
        check()
        value = 0
        for a, b in combinations((v for v in range(4) if v != face), 2):
            value ^= parity[index[prepared['edge_roots'][_edge(tetrahedron, a, b)]]]
        if value:
            raise ArithmeticError('normal boundary edge parity is not a cocycle')
    coboundaries = {}
    for edge in edges:
        check()
        for vertex in prepared['endpoints'][edge]:
            coboundaries[vertex] = coboundaries.get(vertex, 0) ^ (1 << index[edge])
    vector = sum(value << i for i, value in enumerate(parity))
    columns = [coboundaries[vertex] for vertex in sorted(coboundaries)]
    rank = _binary_rank(columns, check)
    augmented = _binary_rank(columns+[vector], check)
    return edges, parity, rank, augmented


def produce_vertex_disc_certificate(triangulation, coordinates, *, check=lambda: None):
    """Return a rank-only disc certificate, or None when this gate does not certify."""
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    flat = [value for row in analysed['rows'] for value in row]
    support = [i for i, value in enumerate(flat) if value]
    common = 0
    for value in flat:
        common = gcd(common, value)
    if common != 1 or analysed['euler_characteristic'] != 1:
        return None
    edges, parity, rank, augmented = _boundary_quotient(prepared, analysed, check)
    if augmented != rank+1:
        return None
    if len(support) == 1:
        selected_rows, selected_columns = [], []
    else:
        minor = _find_rank_minor(prepared['matching'], support, check)
        if minor is None:
            return None
        selected_rows, selected_columns = minor
    determinant = _minor_determinant([
        [prepared['matching'][r].get(c, 0) for c in selected_columns]
        for r in selected_rows], check)
    if determinant == 0:
        raise ArithmeticError('selected rank minor was singular')
    return dict(schema='normal-vertex-disc-rank-v1',
        source_sha256=_binding(triangulation, analysed['rows']), support=support,
        minor_rows=selected_rows, minor_columns=selected_columns,
        minor_determinant=hex(determinant), boundary_edges=edges,
        boundary_parity=parity, coboundary_rank=rank, augmented_rank=augmented,
        euler_characteristic=1, primitive_gcd=1)


def _integer_list(value):
    return type(value) is list and all(type(x) is int for x in value)


def verify_vertex_disc_certificate(triangulation, coordinates, certificate,
                                   *, check=lambda: None):
    """Independently verify the minor, primitive vector, Euler count and H^1 class.

    No rank-selection producer, surface-component routine, or witness
    discovery is called.  A successful result certifies this entire supplied
    primitive surface as an essential disc in the supplied triangulation.
    """
    check()
    if (type(certificate) is not dict or set(certificate) != _FIELDS
            or certificate['schema'] != 'normal-vertex-disc-rank-v1'):
        return False
    callback_error = [None]

    def checked():
        try:
            check()
        except BaseException as exc:
            callback_error[0] = exc
            raise

    try:
        prepared = _prepare(triangulation, checked)
        analysed = _coordinates(prepared, coordinates, checked)
    except NormalOrbitError:
        if callback_error[0] is not None:
            raise
        return False
    if certificate['source_sha256'] != _binding(triangulation, analysed['rows']):
        return False
    flat = [value for row in analysed['rows'] for value in row]
    support = [i for i, value in enumerate(flat) if value]
    common = 0
    for value in flat:
        checked()
        common = gcd(common, value)
    if (common != 1 or not support or analysed['euler_characteristic'] != 1
            or type(certificate['primitive_gcd']) is not int
            or certificate['primitive_gcd'] != 1
            or type(certificate['euler_characteristic']) is not int
            or certificate['euler_characteristic'] != 1
            or not _integer_list(certificate['support'])
            or certificate['support'] != support):
        return False
    rows, columns = certificate['minor_rows'], certificate['minor_columns']
    size = len(support)-1
    if (not _integer_list(rows) or not _integer_list(columns)
            or len(rows) != size or len(columns) != size
            or len(set(rows)) != size or len(set(columns)) != size
            or any(not 0 <= r < len(prepared['matching']) for r in rows)
            or any(c not in support for c in columns)
            or type(certificate['minor_determinant']) is not str):
        return False
    # Reconstruct the minor from the source equations, ignoring all producer
    # elimination state.  The nonzero source vector already bounds rank above.
    determinant = _minor_determinant([
        [prepared['matching'][r].get(c, 0) for c in columns] for r in rows], checked)
    if not determinant or certificate['minor_determinant'] != hex(determinant):
        return False
    edges, parity, rank, augmented = _boundary_quotient(prepared, analysed, checked)
    if (not _integer_list(certificate['boundary_edges'])
            or certificate['boundary_edges'] != edges
            or not _integer_list(certificate['boundary_parity'])
            or certificate['boundary_parity'] != parity
            or type(certificate['coboundary_rank']) is not int
            or type(certificate['augmented_rank']) is not int
            or certificate['coboundary_rank'] != rank
            or certificate['augmented_rank'] != augmented
            or augmented != rank+1):
        return False
    checked()
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('produce', 'verify'))
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    source = json.loads(args.input.read_text())
    if args.mode == 'produce':
        proof = produce_vertex_disc_certificate(source['triangulation'], source['coordinates'])
        result = dict(triangulation=source['triangulation'], coordinates=source['coordinates'],
                      certificate=proof, certified=proof is not None)
        if proof is not None:
            assert verify_vertex_disc_certificate(source['triangulation'],
                                                  source['coordinates'], proof)
    else:
        result = dict(certified=verify_vertex_disc_certificate(source['triangulation'],
                         source['coordinates'], source.get('certificate')))
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'certified': result['certified']}))


if __name__ == '__main__':
    main()
