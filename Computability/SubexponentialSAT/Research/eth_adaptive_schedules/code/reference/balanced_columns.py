"""Exact prototype of balanced vertex labeling and packet embedding.

This is a finite kernel prototype, not a SAT solver.  Tiny examples normally
fail the report's asymptotic sufficient size gates; ``certified_threshold``
checks their initial potential directly instead.  All conditional expectations
are computed as exact fractions.  No assertions are used for correctness gates.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from heapq import heappop, heappush
from itertools import combinations_with_replacement, product
from typing import Optional, Sequence


@dataclass(frozen=True)
class Graph:
    left_vertices: int
    right_vertices: int
    edges: tuple[tuple[int, int], ...]

    def __post_init__(self) -> None:
        if self.left_vertices < 0 or self.right_vertices < 0:
            raise ValueError("Vertex counts must be nonnegative")
        for left, right in self.edges:
            if not 0 <= left < self.left_vertices:
                raise ValueError("Left endpoint is outside the graph")
            if not 0 <= right < self.right_vertices:
                raise ValueError("Right endpoint is outside the graph")

    @property
    def size(self) -> int:
        return len(self.edges)

    def degrees(self) -> tuple[tuple[int, ...], tuple[int, ...]]:
        left = [0] * self.left_vertices
        right = [0] * self.right_vertices
        for x, y in self.edges:
            left[x] += 1
            right[y] += 1
        return tuple(left), tuple(right)

    @property
    def max_degree(self) -> int:
        left, right = self.degrees()
        return max((*left, *right), default=0)


def greedy_row_labels(graph: Graph, groups: int) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Put each whole row vertex into a least-loaded group; break ties by id."""
    if groups < 1:
        raise ValueError("There must be at least one group")
    degrees, _ = graph.degrees()
    heap = [(0, group) for group in range(groups)]
    labels = []
    for degree in degrees:
        load, group = heappop(heap)
        labels.append(group)
        heappush(heap, (load + degree, group))
    loads = [0] * groups
    for load, group in heap:
        loads[group] = load
    return tuple(labels), tuple(loads)


def row_group_weights(graph: Graph, row_labels: Sequence[int], groups: int) -> tuple[tuple[int, ...], ...]:
    """w[g][v] counts edges from row group g to column vertex v."""
    if groups < 1 or len(row_labels) != graph.left_vertices:
        raise ValueError("Invalid row-label dimensions")
    if any(not 0 <= label < groups for label in row_labels):
        raise ValueError("Invalid row label")
    weights = [[0] * graph.right_vertices for _ in range(groups)]
    for x, y in graph.edges:
        weights[row_labels[x]][y] += 1
    return tuple(tuple(row) for row in weights)


def _validate_weights(weights: Sequence[Sequence[int]], groups: int) -> int:
    if groups < 1 or len(weights) != groups:
        raise ValueError("Invalid number of row groups")
    columns = len(weights[0])
    if any(len(row) != columns for row in weights):
        raise ValueError("Unequal weight-row lengths")
    if any(not isinstance(weight, int) or weight < 0 for row in weights for weight in row):
        raise ValueError("Weights must be nonnegative integers")
    return columns


def conditional_potential(
    weights: Sequence[Sequence[int]], groups: int, z: Fraction, threshold: int,
    column_labels: Optional[Sequence[Optional[int]]] = None,
) -> Fraction:
    """E[sum_(g,h) z^(X[g,h]-B)] given the specified column labels.

    Unassigned column vertices are independent and uniform among ``groups``.
    An assigned vertex always keeps its entire vector of incident edge weights.
    """
    columns = _validate_weights(weights, groups)
    z = Fraction(z)
    if z <= 1 or threshold < 0:
        raise ValueError("Require z>1 and threshold>=0")
    labels = (None,) * columns if column_labels is None else tuple(column_labels)
    if len(labels) != columns:
        raise ValueError("Invalid column-label dimensions")
    if any(label is not None and not 0 <= label < groups for label in labels):
        raise ValueError("Invalid column label")
    powers = {weight: z ** weight for row in weights for weight in row}
    total = Fraction(0)
    for row in weights:
        fixed_loads = [0] * groups
        unassigned_factor = Fraction(1)
        for weight, label in zip(row, labels):
            if label is None:
                unassigned_factor *= (groups - 1 + powers[weight]) / groups
            else:
                fixed_loads[label] += weight
        total += unassigned_factor * sum((z ** load for load in fixed_loads), Fraction(0))
    return total / z ** threshold


def certified_threshold(weights: Sequence[Sequence[int]], groups: int, z: Fraction) -> int:
    """Least nonnegative integer B whose exact initial potential is below 1.

    This finite-example certificate is distinct from the report's asymptotic
    sufficient threshold.  It is deliberately obtained without logarithms.
    """
    value = conditional_potential(weights, groups, z, 0)
    threshold = 0
    while value >= 1:
        value /= z
        threshold += 1
    return threshold


@dataclass(frozen=True)
class Step:
    vertex: int
    before: Fraction
    candidates: tuple[Fraction, ...]
    choice: int
    after: Fraction


@dataclass(frozen=True)
class LabelingResult:
    column_labels: tuple[int, ...]
    cell_loads: tuple[tuple[int, ...], ...]
    initial_potential: Fraction
    final_potential: Fraction
    threshold: int
    steps: tuple[Step, ...]

    @property
    def maximum_load(self) -> int:
        return max((load for row in self.cell_loads for load in row), default=0)


def derandomize_columns(
    weights: Sequence[Sequence[int]], groups: int, z: Fraction, threshold: int,
) -> LabelingResult:
    """Choose whole column labels by exact conditional expectation."""
    columns = _validate_weights(weights, groups)
    labels: list[Optional[int]] = [None] * columns
    initial = conditional_potential(weights, groups, z, threshold, labels)
    current = initial
    history = []
    for vertex in range(columns):
        choices = []
        for label in range(groups):
            labels[vertex] = label
            choices.append(conditional_potential(weights, groups, z, threshold, labels))
        if sum(choices, Fraction(0)) / groups != current:
            raise ArithmeticError("Conditional-expectation averaging identity failed")
        choice = min(range(groups), key=lambda label: (choices[label], label))
        labels[vertex] = choice
        following = choices[choice]
        if following > current:
            raise ArithmeticError("Conditional expectation increased")
        history.append(Step(vertex, current, tuple(choices), choice, following))
        current = following
    completed = tuple(int(label) for label in labels)
    cells = [[0] * groups for _ in range(groups)]
    for row_group, row in enumerate(weights):
        for weight, column_group in zip(row, completed):
            cells[row_group][column_group] += weight
    if initial < 1 and any(load >= threshold for row in cells for load in row):
        raise ArithmeticError("The strict potential certificate did not bound a cell")
    return LabelingResult(completed, tuple(tuple(row) for row in cells), initial,
                          current, threshold, tuple(history))


def asymptotic_parameters(size: int, max_degree: int, groups: int, log_scale: int) -> tuple[Fraction, int, bool]:
    """Return z, B, and whether the report's stated sufficient gates hold.

    The caller must additionally supply the global normalization M<=s<=2^lambda
    and the packet-rounding gate when applying the asymptotic theorem.
    """
    if size < 0 or max_degree < 1 or groups < 1 or log_scale < 1:
        raise ValueError("Invalid asymptotic parameters")
    cells = groups * groups
    z = Fraction(max_degree * log_scale * log_scale + 1,
                 max_degree * log_scale * log_scale)
    numerator = (log_scale + 2) * size
    denominator = log_scale * cells
    threshold = (numerator + denominator - 1) // denominator
    gates = (log_scale >= 4 and cells <= 2 ** log_scale
             and size >= 4 * cells * max_degree * log_scale ** 4)
    return z, threshold, gates


def label_digits(label: int, alphabet: int, coordinates: int) -> tuple[int, ...]:
    return tuple((label // (alphabet ** coordinate)) % alphabet
                 for coordinate in range(coordinates))


def digits_label(digits: Sequence[int], alphabet: int) -> int:
    return sum(digit * alphabet ** coordinate for coordinate, digit in enumerate(digits))


@dataclass(frozen=True)
class Packet:
    symbol_pairs: tuple[tuple[int, int], ...]
    slots: tuple[Optional[int], ...]


@dataclass(frozen=True)
class PacketEmbedding:
    padded_class_size: int
    packets: tuple[Packet, ...]


def make_packets(graph: Graph, row_labels: Sequence[int], column_labels: Sequence[int],
                 alphabet: int, coordinates: int) -> PacketEmbedding:
    """Embed edge ids in the source's orientation-preserving padded packets."""
    if alphabet < 1 or coordinates < 1:
        raise ValueError("Require a positive alphabet and at least one coordinate")
    groups = alphabet ** coordinates
    if len(row_labels) != graph.left_vertices or len(column_labels) != graph.right_vertices:
        raise ValueError("Invalid label dimensions")
    if any(not 0 <= label < groups for label in (*row_labels, *column_labels)):
        raise ValueError("Label is outside the alphabet power")
    classes = {(g, h): [] for g in range(groups) for h in range(groups)}
    for edge_id, (left, right) in enumerate(graph.edges):
        classes[row_labels[left], column_labels[right]].append(edge_id)
    length = 2 ** coordinates
    maximum = max((len(edges) for edges in classes.values()), default=0)
    padded = ((maximum + length - 1) // length) * length
    packets = []
    pairs = tuple(combinations_with_replacement(range(alphabet), 2))
    for symbol_pairs in product(pairs, repeat=coordinates):
        equal_coordinates = [i for i, (lo, hi) in enumerate(symbol_pairs) if lo == hi]
        copies = 2 ** len(equal_coordinates)
        for packet_id in range(padded // copies):
            slots = []
            for position in range(length):
                row_digits = []
                column_digits = []
                for coordinate, (lo, hi) in enumerate(symbol_pairs):
                    bit = (position >> coordinate) & 1
                    row_digits.append(hi if bit else lo)
                    column_digits.append(lo if bit else hi)
                row_label = digits_label(row_digits, alphabet)
                column_label = digits_label(column_digits, alphabet)
                copy = sum(((position >> coordinate) & 1) << index
                           for index, coordinate in enumerate(equal_coordinates))
                index = packet_id * copies + copy
                cell = classes[row_label, column_label]
                slots.append(cell[index] if index < len(cell) else None)
            packets.append(Packet(tuple(symbol_pairs), tuple(slots)))
    return PacketEmbedding(padded, tuple(packets))
