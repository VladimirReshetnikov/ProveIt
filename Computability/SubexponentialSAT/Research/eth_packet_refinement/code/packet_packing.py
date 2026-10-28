"""Exact deterministic packet packing for a bipartite multigraph.

This is an algebraic/combinatorial prototype, not a SAT solver.  Parallel
edges are represented by repeated (row, column) pairs and remain distinct.

The row assignment greedily balances weighted vertex degrees.  The column
assignment minimizes exact conditional expectations of

    Phi = sum_{a,b} z**X[a,b],  z = 1 + 1/(Delta * lambda_).

All choices and potential traces use fractions.Fraction.  The routine never
needs floating-point logarithms or exponential functions.  The accompanying
report proves the analytic estimate; rational_load_bound() deliberately uses
the weaker rational majorant ln(Q**2) <= ceil(log2(Q**2)) so finite checks can
also avoid floating point.

The code is a direct implementation written for this refinement.  It does not
reuse an upstream implementation or claim to implement the full preprint.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations_with_replacement, product
from typing import Iterable


def _integer(name: str, value: int, minimum: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an integer")
    if value < minimum:
        raise ValueError(f"{name} must be at least {minimum}")
    return value


@dataclass(frozen=True)
class Labeling:
    """Immutable output, including every chosen conditional potential.

    delta is max(1, maximum vertex degree), so the empty graph is supported.
    potential_trace[0] is the expectation before any column is assigned;
    potential_trace[v+1] is the conditional expectation after column v.
    """

    n_rows: int
    n_columns: int
    edges: tuple[tuple[int, int], ...]
    q: int
    lambda_: int
    delta: int
    row_labels: tuple[int, ...]
    column_labels: tuple[int, ...]
    row_bin_weights: tuple[int, ...]
    loads: tuple[tuple[int, ...], ...]
    z: Fraction
    potential_trace: tuple[Fraction, ...]

    @property
    def edge_count(self) -> int:
        return len(self.edges)

    @property
    def max_load(self) -> int:
        return max((max(row) for row in self.loads), default=0)


def deterministic_labeling(
    n_rows: int,
    n_columns: int,
    edges: Iterable[tuple[int, int]],
    q: int,
    lambda_: int,
) -> Labeling:
    """Label a bipartite multigraph by q labels on each side.

    Row vertices and column vertices are processed in index order.  A tie
    always chooses the smallest label, making the result reproducible.
    Invalid endpoints and noninteger parameters are rejected explicitly.

    This straightforward exact implementation prioritizes a reviewable
    specification.  Its polynomial arithmetic cost is not an optimized
    implementation benchmark for the asymptotic theorem.
    """

    _integer("n_rows", n_rows)
    _integer("n_columns", n_columns)
    _integer("q", q, 1)
    _integer("lambda_", lambda_, 1)
    edge_list: list[tuple[int, int]] = []
    for index, edge in enumerate(edges):
        try:
            row, column = edge
        except (TypeError, ValueError) as exc:
            raise ValueError(f"edge {index} must contain two endpoints") from exc
        _integer(f"edge {index} row", row)
        _integer(f"edge {index} column", column)
        if row >= n_rows or column >= n_columns:
            raise ValueError(f"edge {index} has an out-of-range endpoint")
        edge_list.append((row, column))
    edge_tuple = tuple(edge_list)
    m = len(edge_tuple)

    row_degrees = [0] * n_rows
    column_degrees = [0] * n_columns
    for row, column in edge_tuple:
        row_degrees[row] += 1
        column_degrees[column] += 1
    delta = max([1, *row_degrees, *column_degrees])

    row_bin_weights = [0] * q
    row_labels: list[int] = []
    for degree in row_degrees:
        label = min(range(q), key=lambda a: (row_bin_weights[a], a))
        row_labels.append(label)
        row_bin_weights[label] += degree

    # w[a][v] is a bundled vertex contribution, not an independent edge.
    # This distinction is essential when the graph contains parallel edges.
    w = [[0] * n_columns for _ in range(q)]
    for row, column in edge_tuple:
        w[row_labels[row]][column] += 1

    z = Fraction(delta * lambda_ + 1, delta * lambda_)
    z_powers = [Fraction(1)]
    for _ in range(m):
        z_powers.append(z_powers[-1] * z)

    # suffix[a][v] is the exact moment-generating product of unassigned
    # column vertices v,...,n_columns-1 for one fixed ordered-label cell.
    suffix = [[Fraction(1)] * (n_columns + 1) for _ in range(q)]
    for a in range(q):
        for v in range(n_columns - 1, -1, -1):
            factor = (q - 1 + z_powers[w[a][v]]) / q
            suffix[a][v] = factor * suffix[a][v + 1]

    loads = [[0] * q for _ in range(q)]
    row_power_sums = [Fraction(q)] * q
    initial = sum((q * suffix[a][0] for a in range(q)), Fraction())
    trace = [initial]
    column_labels: list[int] = []

    for v in range(n_columns):
        candidates: list[Fraction] = []
        for b in range(q):
            candidate = Fraction()
            for a in range(q):
                old = loads[a][b]
                updated_sum = (
                    row_power_sums[a]
                    - z_powers[old]
                    + z_powers[old + w[a][v]]
                )
                candidate += updated_sum * suffix[a][v + 1]
            candidates.append(candidate)
        b = min(range(q), key=lambda label: (candidates[label], label))
        column_labels.append(b)
        for a in range(q):
            old = loads[a][b]
            new = old + w[a][v]
            row_power_sums[a] += z_powers[new] - z_powers[old]
            loads[a][b] = new
        trace.append(candidates[b])

    return Labeling(
        n_rows=n_rows,
        n_columns=n_columns,
        edges=edge_tuple,
        q=q,
        lambda_=lambda_,
        delta=delta,
        row_labels=tuple(row_labels),
        column_labels=tuple(column_labels),
        row_bin_weights=tuple(row_bin_weights),
        loads=tuple(tuple(row) for row in loads),
        z=z,
        potential_trace=tuple(trace),
    )


def rational_load_bound(labeling: Labeling) -> Fraction:
    """An exact conservative majorant of the proved maximum-load bound.

    For D=Q**2, ln(D)<=ceil(log2(D)).  The latter is computed by integer
    bit_length, including D=1 where both sides are zero.  Therefore this
    certificate is rational and never relies on rounded transcendental data.
    """

    d = labeling.q**2
    log_majorant = (d - 1).bit_length()
    scale = Fraction(labeling.lambda_ + 1, labeling.lambda_)
    return scale * (
        Fraction(labeling.edge_count, d) + Fraction(labeling.delta, labeling.q)
    ) + (labeling.delta * labeling.lambda_ + 1) * log_majorant


def rational_padding_bound(labeling: Labeling, slots: int) -> Fraction:
    """The load certificate plus the strict-rounding allowance slots."""

    _integer("slots", slots, 1)
    return rational_load_bound(labeling) + slots


def label_digits(label: int, r: int, a: int) -> tuple[int, ...]:
    """The a base-r coordinates, least significant coordinate first."""

    _integer("r", r, 2)
    _integer("a", a, 1)
    _integer("label", label)
    if label >= r**a:
        raise ValueError("label does not fit in a base-r coordinates")
    digits: list[int] = []
    for _ in range(a):
        digits.append(label % r)
        label //= r
    return tuple(digits)


def _encode_digits(digits: Iterable[int], r: int) -> int:
    label = 0
    place = 1
    for digit in digits:
        label += place * digit
        place *= r
    return label


@dataclass(frozen=True)
class Packet:
    """An oriented packet; a real slot stores its original edge index.

    A None slot is padding and has no real port on either side.  The same
    slot index is used for the two ends of each real edge.
    """

    coordinate_pairs: tuple[tuple[int, int], ...]
    slots: tuple[int | None, ...]


@dataclass(frozen=True)
class PacketPacking:
    labeling: Labeling
    r: int
    a: int
    slots_per_packet: int
    common_cell_padding: int
    packets: tuple[Packet, ...]


def build_oriented_packets(labeling: Labeling, r: int, a: int) -> PacketPacking:
    """Pad and orient the ordered label classes exactly as required.

    Requires Q=r**a and uses L=2**a slots.  In coordinate i with unequal
    symbols low<high, bit i of a slot selects row/column orientation:
    0 gives (low,high), 1 gives (high,low).  If the symbols are equal,
    the slot bit chooses a distinct copy of the same ordered label class.

    Full padded packets, including completely empty ones, are retained so
    the exact equality number_of_packets=H_pad*Q**2/L is inspectable.
    """

    _integer("r", r, 2)
    _integer("a", a, 1)
    if labeling.q != r**a:
        raise ValueError("the labeling must have q == r**a")
    q = labeling.q
    slots = 2**a
    h_pad = ((labeling.max_load + slots - 1) // slots) * slots
    classes: list[list[list[int]]] = [[[] for _ in range(q)] for _ in range(q)]
    for edge_id, (row, column) in enumerate(labeling.edges):
        classes[labeling.row_labels[row]][labeling.column_labels[column]].append(edge_id)

    symbol_pairs = tuple(combinations_with_replacement(range(r), 2))
    packets: list[Packet] = []
    for coordinate_pairs in product(symbol_pairs, repeat=a):
        equal_coordinates = [i for i, (lo, hi) in enumerate(coordinate_pairs) if lo == hi]
        copies_per_class = 2 ** len(equal_coordinates)
        for packet_index in range(h_pad // copies_per_class):
            packet_slots: list[int | None] = []
            for slot in range(slots):
                row_digits: list[int] = []
                column_digits: list[int] = []
                for i, (lo, hi) in enumerate(coordinate_pairs):
                    if (slot >> i) & 1:
                        row_digits.append(hi)
                        column_digits.append(lo)
                    else:
                        row_digits.append(lo)
                        column_digits.append(hi)
                row_label = _encode_digits(row_digits, r)
                column_label = _encode_digits(column_digits, r)
                copy = sum(((slot >> i) & 1) << j for j, i in enumerate(equal_coordinates))
                position = packet_index * copies_per_class + copy
                cell = classes[row_label][column_label]
                packet_slots.append(cell[position] if position < len(cell) else None)
            packets.append(Packet(tuple(coordinate_pairs), tuple(packet_slots)))
    return PacketPacking(labeling, r, a, slots, h_pad, tuple(packets))
