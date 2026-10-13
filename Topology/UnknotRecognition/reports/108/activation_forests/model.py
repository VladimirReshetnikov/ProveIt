"""Validated finite graph/occurrence model shared by producer and checker.

The decision model uses unsigned geometric counts, capped at two.  The digest
binds the uncapped input counts, in canonical hexadecimal encoding.
"""

from dataclasses import dataclass
from hashlib import sha256
import json


class InvalidProblem(ValueError):
    pass


def integer(x):
    return type(x) is int


@dataclass(frozen=True)
class Problem:
    vertices: int
    columns: int
    edges: tuple
    rows: tuple
    digest: str
    raw_parity: bool


def parse_problem(value):
    if type(value) is not dict or set(value) != {'vertices', 'columns', 'edges', 'rows'}:
        raise InvalidProblem('expected vertices, columns, edges, rows')
    vertices, columns = value['vertices'], value['columns']
    if not integer(vertices) or vertices < 1 or not integer(columns) or columns < 0:
        raise InvalidProblem('invalid graph or column namespace')
    edges, rows = value['edges'], value['rows']
    if not isinstance(edges, (list, tuple)) or not isinstance(rows, (list, tuple)):
        raise InvalidProblem('edges and rows must be finite sequences')
    if len(edges) != len(rows):
        raise InvalidProblem('one edge, or None, is required per row')
    parsed_edges, parsed_rows, exact_rows = [], [], []
    column_boundary = {}
    for edge, row in zip(edges, rows):
        if edge is None:
            parsed_edges.append(None)
        elif (isinstance(edge, (list, tuple)) and len(edge) == 2
              and all(integer(v) and 0 <= v < vertices for v in edge)):
            parsed_edges.append(tuple(edge))
        else:
            raise InvalidProblem('invalid row edge')
        if not isinstance(row, (list, tuple)):
            raise InvalidProblem('sparse row must be a sequence')
        counts = {}
        for entry in row:
            if not isinstance(entry, (list, tuple)) or len(entry) != 2:
                raise InvalidProblem('invalid incidence pair')
            column, count = entry
            if (not integer(column) or not 0 <= column < columns
                    or not integer(count) or count < 1 or column in counts):
                raise InvalidProblem('invalid or repeated sparse incidence')
            counts[column] = count
        ordered = sorted(counts.items())
        edge = parsed_edges[-1]
        if edge is not None:
            for column, count in ordered:
                if count % 2:
                    boundary = column_boundary.setdefault(column, set())
                    for endpoint in edge:
                        if endpoint in boundary:
                            boundary.remove(endpoint)
                        else:
                            boundary.add(endpoint)
        parsed_rows.append(tuple((c, min(2, a)) for c, a in ordered))
        exact_rows.append([[hex(c), hex(a)] for c, a in ordered])
    canonical = {'vertices': hex(vertices), 'columns': hex(columns),
                 'edges': [None if e is None else [hex(v) for v in e]
                           for e in parsed_edges], 'rows': exact_rows}
    digest = sha256(json.dumps(canonical, separators=(',', ':'),
                               sort_keys=True).encode('ascii')).hexdigest()
    return Problem(vertices, columns, tuple(parsed_edges), tuple(parsed_rows), digest,
                   not any(column_boundary.values()))


def from_dense(vertices, edges, rows, columns=None):
    width = (len(rows[0]) if rows else 0) if columns is None else columns
    if any(len(row) != width for row in rows):
        raise InvalidProblem('dense row widths differ')
    value = {'vertices': vertices, 'columns': width, 'edges': edges,
             'rows': [[[c, a] for c, a in enumerate(row) if a]
                      for row in rows]}
    parse_problem(value)
    return value
