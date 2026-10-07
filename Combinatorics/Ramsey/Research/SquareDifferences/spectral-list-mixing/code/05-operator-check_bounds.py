#!/usr/bin/env python3
"""Deterministic numerical checks for the accompanying mathematical article.

Run from any directory: python verification/check_bounds.py
Only NumPy and the Python standard library are used. These finite checks are
sanity checks of the displayed analytic formulas, not a proof certificate.
No complete reflection-positive tuple law is constructed by this program.
"""

from itertools import combinations, permutations, product
import json
import math

import numpy as np


SEED = 20261007
TOLERANCE = 2e-11


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def op_norm(kernel, row_weights, column_weights):
    """L2 norm for the stated probability measures, including normalization."""
    matrix = np.sqrt(row_weights)[:, None] * kernel
    matrix = matrix * np.sqrt(column_weights)[None, :]
    return float(np.linalg.svd(matrix, compute_uv=False)[0])


def product_space(weights):
    indices = np.array(list(product(*(range(len(w)) for w in weights))), dtype=int)
    masses = np.ones(len(indices))
    for coordinate, weight in enumerate(weights):
        masses *= weight[indices[:, coordinate]]
    require(abs(float(masses.sum()) - 1.0) < TOLERANCE, "Product mass is not one")
    return indices, masses


def prefix_bound(order, deltas, constants):
    answer = 0.0
    prefix = 1.0
    for edge in order:
        answer += prefix * deltas[edge]
        prefix *= constants[edge]
    return answer


def sorted_order(deltas, constants):
    def key(edge):
        if constants[edge] == 1.0:
            return 0.0 if deltas[edge] == 0.0 else math.inf
        return deltas[edge] / (1.0 - constants[edge])
    return tuple(sorted(range(len(constants)), key=key))


def random_product_checks(rng):
    maximum_heterogeneous_residual = -math.inf
    maximum_homogeneous_residual = -math.inf
    maximum_ordering_residual = 0.0
    maximum_single_edge_residual = 0.0
    minimum_probability = 1.0
    permutation_count = 0
    for case in range(64):
        left_weights = []
        right_weights = []
        for collection in (left_weights, right_weights):
            for _ in range(3):
                size = int(rng.integers(2, 4))
                raw = rng.uniform(0.05, 1.0, size)
                weights = raw / raw.sum()
                collection.append(weights)
                minimum_probability = min(minimum_probability, float(weights.min()))
        left_indices, left_masses = product_space(left_weights)
        right_indices, right_masses = product_space(right_weights)
        edge_count = case % 8
        candidates = [(i, j) for i in range(3) for j in range(3)]
        picked = rng.choice(len(candidates), edge_count, replace=False)
        edges = [candidates[int(i)] for i in picked]
        constants = rng.uniform(0.2, 0.8, edge_count)
        kernels = []
        deltas = []
        for edge_number, (left, right) in enumerate(edges):
            shape = (len(left_weights[left]), len(right_weights[right]))
            if case % 2:
                u = rng.normal(size=shape[0])
                v = rng.normal(size=shape[1])
                u -= np.dot(left_weights[left], u)
                v -= np.dot(right_weights[right], v)
                u /= max(1.0, float(np.max(np.abs(u))))
                v /= max(1.0, float(np.max(np.abs(v))))
                amplitude = float(rng.uniform(0.005, 0.15))
                kernel = constants[edge_number] + amplitude * np.outer(u, v)
            else:
                kernel = rng.uniform(0.0, 1.0, shape)
            if case == 15 and edge_number == 0:
                constants[edge_number] = 1.0
            if case == 23 and edge_number == 0:
                constants[edge_number] = 1.0
                kernel = np.ones(shape)
            if case == 31 and edge_number == 0:
                constants[edge_number] = 0.0
            require(float(kernel.min()) >= 0 and float(kernel.max()) <= 1,
                    "An edge kernel left the interval [0,1]")
            kernels.append(kernel)
            deltas.append(op_norm(kernel - constants[edge_number],
                                  left_weights[left], right_weights[right]))

        full_kernel = np.ones((len(left_indices), len(right_indices)))
        for (left, right), kernel in zip(edges, kernels):
            full_kernel *= kernel[left_indices[:, left, None],
                                  right_indices[None, :, right]]
        actual = op_norm(full_kernel - float(np.prod(constants)), left_masses, right_masses)
        ordering = sorted_order(deltas, constants)
        certificate = prefix_bound(ordering, deltas, constants)
        residual = actual - certificate
        maximum_heterogeneous_residual = max(maximum_heterogeneous_residual, residual)
        require(residual <= TOLERANCE * (1.0 + certificate),
                "Heterogeneous product-kernel inequality failed")

        brute_minimum = math.inf
        for order in permutations(range(edge_count)):
            permutation_count += 1
            brute_minimum = min(brute_minimum, prefix_bound(order, deltas, constants))
        ordering_residual = abs(certificate - brute_minimum)
        maximum_ordering_residual = max(maximum_ordering_residual, ordering_residual)
        require(ordering_residual < TOLERANCE, "Sorted order was not a minimum")

        common_constant = 0.5
        common_delta = 0.0
        for (left, right), kernel in zip(edges, kernels):
            common_delta = max(common_delta,
                               op_norm(kernel - common_constant,
                                       left_weights[left], right_weights[right]))
        homogeneous_actual = op_norm(full_kernel - common_constant ** edge_count,
                                     left_masses, right_masses)
        homogeneous_certificate = common_delta * (1.0 - common_constant ** edge_count)
        homogeneous_certificate /= 1.0 - common_constant
        residual = homogeneous_actual - homogeneous_certificate
        maximum_homogeneous_residual = max(maximum_homogeneous_residual, residual)
        require(residual <= TOLERANCE * (1.0 + homogeneous_certificate),
                "Homogeneous product-kernel inequality failed")
        if edge_count == 1:
            maximum_single_edge_residual = max(maximum_single_edge_residual,
                                                abs(actual - deltas[0]))
    return {
        "cases": 64,
        "edge_counts": list(range(8)),
        "left_and_right_coordinate_counts": 3,
        "strictly_positive_nonuniform_vertex_measures": True,
        "smallest_vertex_atom": minimum_probability,
        "maximum_heterogeneous_actual_minus_bound": maximum_heterogeneous_residual,
        "maximum_homogeneous_actual_minus_bound": maximum_homogeneous_residual,
        "maximum_single_edge_equality_residual": maximum_single_edge_residual,
        "brute_force_orderings_checked": permutation_count,
        "maximum_sorted_minus_brute_absolute_residual": maximum_ordering_residual,
        "constant_endpoints_zero_and_one_checked": True,
    }


def star_checks():
    cases = []
    maximum_residual = 0.0
    for prime in (3, 7, 11):
        squares = {value * value % prime for value in range(1, prime)}
        q = (prime - 1) / (2.0 * prime)
        overlap = (prime - 3) / (4.0 * prime)
        for degree in (1, 2, 3):
            leaves = np.array(list(product(range(prime), repeat=degree)), dtype=int)
            kernel = np.ones((prime, len(leaves)))
            for center in range(prime):
                for coordinate in range(degree):
                    kernel[center] *= np.isin((leaves[:, coordinate] - center) % prime,
                                              tuple(squares))
            actual = op_norm(kernel - q ** degree,
                             np.full(prime, 1.0 / prime),
                             np.full(len(leaves), 1.0 / len(leaves)))
            exact_formula = math.sqrt((q ** degree - overlap ** degree) / prime)
            residual = abs(actual - exact_formula)
            maximum_residual = max(maximum_residual, residual)
            require(residual <= TOLERANCE, "Paley-star singular-value formula failed")
            cases.append({"prime": prime, "degree": degree,
                          "matrix_norm": actual, "formula_norm": exact_formula})
    asymptotics = []
    # These use the explicit scalar expression, not huge p-by-p^degree matrices.
    for degree in (1, 2, 3, 5):
        prime = 2147483647
        q = (prime - 1) / (2.0 * prime)
        overlap = (prime - 3) / (4.0 * prime)
        rescaled = math.sqrt(q ** degree - overlap ** degree)
        limiting = math.sqrt(2.0 ** (-degree) - 4.0 ** (-degree))
        require(abs(rescaled - limiting) < 2e-9, "Star rescaling check failed")
        asymptotics.append({"degree": degree, "sqrt_p_rescaled_formula": rescaled,
                            "limiting_constant": limiting})
    return {"cases": cases, "maximum_formula_residual": maximum_residual,
            "fixed_degree_asymptotic_checks": asymptotics,
            "meaning": "Checks sharp p^(-1/2) order, not optimality of the geometric prefactor."}


def small_address_graph_checks():
    h, depth, blocks = 3, 1, 3
    words = list(permutations(range(h)))
    word_index = {word: index for index, word in enumerate(words)}
    shift = np.array([word_index[word[1:] + word[:1]] for word in words])
    edge_counts = []
    reflection_checks = 0
    for marked_size in range(depth + 1):
        for marked in combinations(range(blocks), marked_size):
            clean = [block for block in range(blocks) if block not in marked]
            addresses = np.array(list(product(range(len(words)), repeat=len(clean))), dtype=int)
            address_index = {tuple(address): index for index, address in enumerate(addresses)}
            shifted = shift[addresses]
            matches = (shifted[:, None, :] == addresses[None, :, :]).sum(axis=2)
            graph = matches >= depth + 1
            require(not np.any(np.diag(graph)), "Address graph has a loop")
            require(not np.any(graph & graph.T), "Address graph has opposite directed edges")
            for coordinate in range(len(clean)):
                for a, b in combinations(range(h), 2):
                    swapped_words = []
                    for word in words:
                        changed = tuple(b if x == a else a if x == b else x for x in word)
                        swapped_words.append(word_index[changed])
                    reflected = addresses.copy()
                    reflected[:, coordinate] = np.array(swapped_words)[addresses[:, coordinate]]
                    reindex = [address_index[tuple(address)] for address in reflected]
                    require(np.array_equal(graph, graph[np.ix_(reindex, reindex)]),
                            "Address graph is not reflection-invariant")
                    reflection_checks += 1
            identity = word_index[tuple(range(h))]
            cycle_words = [identity]
            for _ in range(h - 1):
                cycle_words.append(int(shift[cycle_words[-1]]))
            cycle_vertices = [address_index[tuple([word] * len(clean))] for word in cycle_words]
            for j in range(h):
                require(bool(graph[cycle_vertices[j], cycle_vertices[(j + 1) % h]]),
                        "A designated cycle edge was lost")
            edge_counts.append({"marked_blocks": list(marked),
                                "addresses": len(addresses), "directed_edges": int(graph.sum())})
    return {"h": h, "depth": depth, "blocks": blocks, "graphs": edge_counts,
            "reflection_symmetries_checked": reflection_checks,
            "meaning": "Combinatorial address model only; no full tuple law or positivity matrix generated."}


def clean_floats(value):
    if isinstance(value, float):
        return float(format(value, ".12g"))
    if isinstance(value, dict):
        return {key: clean_floats(item) for key, item in value.items()}
    if isinstance(value, list):
        return [clean_floats(item) for item in value]
    return value


def main():
    rng = np.random.default_rng(SEED)
    result = {
        "status": "all finite numerical checks passed",
        "scope": "Numerical sanity checks; analytic all-parameter proofs are in the article.",
        "seed": SEED,
        "floating_point_tolerance": TOLERANCE,
        "product_kernel_checks": random_product_checks(rng),
        "star_checks": star_checks(),
        "small_address_graph_checks": small_address_graph_checks(),
    }
    print(json.dumps(clean_floats(result), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
