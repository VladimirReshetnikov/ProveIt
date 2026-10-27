"""Exact deterministic asymmetric pair-label balancing and packet construction.

The routines are research components, not a full tensor-contraction or SAT solver.
They use only Python's standard library. Edge multiplicities are permitted.
"""
from fractions import Fraction
from itertools import combinations_with_replacement, product


def _adjacency(adjacency):
    adj = [list(row) for row in adjacency]
    ncols = len(adj[0]) if adj else 0
    if any(len(row) != ncols for row in adj):
        raise ValueError("Ragged adjacency matrix")
    if any(type(value) is not int or value < 0 for row in adj for value in row):
        raise ValueError("Edge multiplicities must be nonnegative integers")
    return adj, ncols


def balance_pair_labels(adjacency, label_count, smoothness=8, keep_certificate=True):
    """Assign Q labels on each side of a bipartite multigraph.

    Rows are greedily balanced by incident degree. Columns minimize the exact
    conditional expectation of Phi=sum_(a,b) q**X[a,b], where
    q=1+1/(h*C), h=smoothness, and C is the actual maximum COLUMN degree.
    C=1 is used for the empty graph. The row bound R is tracked separately.

    All arithmetic choices and their averaging checks are exact. This explicit
    implementation favors auditability over polynomial-degree optimization.
    """
    if type(label_count) is not int or label_count < 1:
        raise ValueError("label_count must be a positive integer")
    if type(smoothness) is not int or smoothness < 2:
        raise ValueError("smoothness must be an integer at least two")
    adj, ncols = _adjacency(adjacency)
    nrows = len(adj)
    row_degrees = [sum(row) for row in adj]
    col_degrees = [sum(adj[i][j] for i in range(nrows)) for j in range(ncols)]
    M = sum(row_degrees)
    R = max(row_degrees, default=0)
    C = max(col_degrees, default=0)
    potential_C = max(1, C)
    Q = label_count
    q = Fraction(smoothness * potential_C + 1, smoothness * potential_C)
    powers = [Fraction(1)]
    for _ in range(M):
        powers.append(powers[-1] * q)

    row_loads = [0] * Q
    row_labels = []
    for degree in row_degrees:
        label = min(range(Q), key=lambda a: (row_loads[a], a))
        row_labels.append(label)
        row_loads[label] += degree

    weights = [[0] * ncols for _ in range(Q)]
    for i, row in enumerate(adj):
        for j, value in enumerate(row):
            weights[row_labels[i]][j] += value
    if any(value > C for row in weights for value in row):
        raise ArithmeticError("Column weight exceeded the column-degree bound")
    factors = [[Fraction(Q - 1, Q) + powers[value] / Q for value in row]
               for row in weights]
    future = []
    for row in factors:
        value = Fraction(1)
        for factor in row:
            value *= factor
        future.append(value)

    loads = [[0] * Q for _ in range(Q)]
    current = Q * sum(future, Fraction(0))
    initial = current
    column_labels = []
    certificates = []
    for j in range(ncols):
        next_future = [future[a] / factors[a][j] for a in range(Q)]
        scores = []
        for choice in range(Q):
            score = sum((next_future[a] * sum(
                (powers[loads[a][b] + (weights[a][j] if b == choice else 0)]
                 for b in range(Q)), Fraction(0))
                for a in range(Q)), Fraction(0))
            scores.append(score)
        if sum(scores, Fraction(0)) / Q != current:
            raise ArithmeticError("Conditional-expectation averaging identity failed")
        selected = min(range(Q), key=lambda b: (scores[b], b))
        if scores[selected] > current:
            raise ArithmeticError("Conditional expectation increased")
        if keep_certificate:
            certificates.append({
                "column": j, "selected_label": selected,
                "before": str(current), "after": str(scores[selected]),
                "candidate_scores": [str(score) for score in scores],
            })
        column_labels.append(selected)
        for a in range(Q):
            loads[a][selected] += weights[a][j]
        future = next_future
        current = scores[selected]

    final_potential = sum((powers[value] for row in loads for value in row), Fraction(0))
    if current != final_potential or current > initial:
        raise ArithmeticError("Final potential certificate failed")
    if any(Q * value > M + Q * R for value in row_loads):
        raise ArithmeticError("Greedy row bound failed")
    return {
        "row_labels": row_labels, "column_labels": column_labels,
        "row_loads": row_loads, "pair_loads": loads,
        "edges": M, "maximum_degree": max(R, C),
        "maximum_row_degree": R, "maximum_column_degree": C,
        "potential_column_bound": potential_C,
        "label_count": Q, "smoothness": smoothness,
        "potential_base": str(q), "initial_expected_potential": str(initial),
        "final_potential": str(final_potential),
        "max_pair_load": max((value for row in loads for value in row), default=0),
        "checked_assignment_steps": ncols, "steps": certificates,
    }


def _digits(label, base, width):
    result = []
    for _ in range(width):
        label, digit = divmod(label, base)
        result.append(digit)
    return result


def construct_packets(adjacency, row_labels, column_labels, group_count, coordinates):
    """Uniformly pad label pairs and embed edges in orientation packets.

    Q=group_count**coordinates; L=2**coordinates. The common load Hpad is
    the maximum real pair load rounded UP to a multiple of L. Every packet
    records separate row and column ports, including dummy slots, so the
    shared-slot and orientation identities can be independently inspected.

    This materializes polynomial-size packing data; it is not the depth-first
    contraction algorithm. Empty padded packets are deliberately retained.
    """
    if type(group_count) is not int or group_count < 2:
        raise ValueError("group_count must be an integer at least two")
    if type(coordinates) is not int or coordinates < 0:
        raise ValueError("coordinates must be a nonnegative integer")
    adj, ncols = _adjacency(adjacency)
    if len(row_labels) != len(adj) or len(column_labels) != ncols:
        raise ValueError("Vertex-label counts do not match the graph")
    Q = group_count ** coordinates
    L = 1 << coordinates
    if any(type(label) is not int or not 0 <= label < Q
           for label in list(row_labels) + list(column_labels)):
        raise ValueError("A vertex label lies outside the label set")
    buckets = {(a, b): [] for a in range(Q) for b in range(Q)}
    edges = []
    for row_vertex, row in enumerate(adj):
        for col_vertex, multiplicity in enumerate(row):
            for copy in range(multiplicity):
                edge_id = len(edges)
                edges.append((row_vertex, col_vertex, copy))
                buckets[row_labels[row_vertex], column_labels[col_vertex]].append(edge_id)
    maximum = max((len(bucket) for bucket in buckets.values()), default=0)
    Hpad = ((maximum + L - 1) // L) * L
    coordinate_pairs = tuple(combinations_with_replacement(range(group_count), 2))
    powers = [group_count ** i for i in range(coordinates)]
    packets = []
    for key in product(coordinate_pairs, repeat=coordinates):
        equal_coordinates = [i for i, pair in enumerate(key) if pair[0] == pair[1]]
        copies_per_pair = 1 << len(equal_coordinates)
        for packet_number in range(Hpad // copies_per_pair):
            row_slots, column_slots = [], []
            row_slot_labels, column_slot_labels = [], []
            for slot in range(L):
                row_label = column_label = 0
                for i, (low, high) in enumerate(key):
                    bit = (slot >> i) & 1
                    row_digit = high if bit else low
                    col_digit = low if bit else high
                    row_label += row_digit * powers[i]
                    column_label += col_digit * powers[i]
                copy_index = sum(((slot >> i) & 1) << j
                                 for j, i in enumerate(equal_coordinates))
                index = packet_number * copies_per_pair + copy_index
                bucket = buckets[row_label, column_label]
                edge_id = bucket[index] if index < len(bucket) else None
                if edge_id is None:
                    row_slots.append(None)
                    column_slots.append(None)
                else:
                    row_vertex, col_vertex, _ = edges[edge_id]
                    row_slots.append((edge_id, row_vertex))
                    column_slots.append((edge_id, col_vertex))
                row_slot_labels.append(row_label)
                column_slot_labels.append(column_label)
            packets.append({
                "symbol_pairs": [list(pair) for pair in key],
                "row_slots": row_slots, "column_slots": column_slots,
                "row_slot_labels": row_slot_labels,
                "column_slot_labels": column_slot_labels,
            })
    return {
        "group_count": group_count, "coordinates": coordinates,
        "label_count": Q, "packet_size": L, "common_padded_load": Hpad,
        "padded_ports_per_side": Hpad * Q * Q,
        "real_edges": edges, "packets": packets,
    }
