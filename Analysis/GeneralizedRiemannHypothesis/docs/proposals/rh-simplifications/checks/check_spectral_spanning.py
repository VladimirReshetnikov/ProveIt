"""Check the spectral spanning identities in two rational finite-dimensional models.

Requires Python 3 and SymPy. The proof in the paper applies in all dimensions.
The models exercise the trace identity, source restriction, a nontrivial
target projection, and rank growth for nonorthogonal ranges. A second exact
calculation checks the extremal examples without allocating large matrices.
"""
from itertools import product

from sympy import Matrix, Rational as Q, diag, eye, zeros


def uniform_mean(items):
    return sum(items, zeros(items[0].rows, items[0].cols)) / len(items)


def inner_square(matrix):
    return (matrix.T * matrix).trace()


def projection(columns):
    """Exact orthogonal projector onto the column span of a rational matrix."""
    basis = columns.columnspace()
    if not basis:
        return zeros(columns.rows)
    matrix = Matrix.hstack(*basis)
    return matrix * (matrix.T * matrix).inv() * matrix.T


def signed_cyclic_group(dimension):
    matrices = []
    for offset in range(dimension):
        for signs in product((-1, 1), repeat=dimension):
            matrix = zeros(dimension)
            for col, sign in enumerate(signs):
                matrix[(col + offset) % dimension, col] = sign
            matrices.append(matrix)
    return matrices


def check_model(ramified_dimension):
    dimension, source_dimension = 4, 3
    group = signed_cyclic_group(dimension)
    ambient_actions = [diag(action, eye(1)) for action in group]
    # The fifth coordinate is removed by the invariant target projection.
    target_basis = Matrix([
        [Q(3, 5), Q(4, 5), 0],
        [Q(4, 5), -Q(3, 5), 0],
        [0, 0, Q(3, 5)],
        [0, 0, Q(4, 5)],
    ])
    singular_values = [Q(501, 500), Q(499, 500), 1]
    source_map = (target_basis * diag(*singular_values)).col_join(
        Matrix([[Q(1, 50), 0, 0]])
    )
    ambient_covariance = uniform_mean(
        [u * source_map * source_map.T * u.T for u in ambient_actions]
    )
    overlap = sum(
        inner_square(source_map.T * u * source_map) for u in ambient_actions
    ) / len(group)
    assert (ambient_covariance**2).trace() == overlap

    alpha, beta = 5 * Q(1, 4**4), 9 * Q(1, 4**4)
    gamma = Q(source_dimension - ramified_dimension, source_dimension)
    assert dimension * overlap <= (1 + beta) * source_dimension**2
    below_one = sum(max(0, 1 - value**2) for value in singular_values)
    assert below_one <= alpha * source_dimension

    restricted_basis = target_basis[:, :ramified_dimension]
    values = singular_values[:ramified_dimension]
    full_target_maps = [action * source_map[:dimension, :] for action in group]
    translates = [u * restricted_basis * diag(*values) for u in group]
    nu = beta + 2 * alpha + 2 * gamma

    # Start with an oblique range to exercise the preimage/rank inequality.
    current = Matrix([[1], [2], [1], [-1]])
    while current.rank() < dimension:
        target_projection = projection(current)
        complement = eye(dimension) - target_projection
        old_rank = current.rank()
        gains, energies = [], []
        for restricted, full in zip(translates, full_target_maps):
            quotient = complement * restricted
            kernel_basis = quotient.nullspace()
            kernel = (
                Matrix.hstack(*kernel_basis) if kernel_basis
                else zeros(ramified_dimension, 0)
            )
            gain = current.row_join(restricted).rank() - old_rank
            assert gain == ramified_dimension - kernel.cols
            restricted_energy = inner_square(restricted * projection(kernel))
            energy = inner_square(target_projection * full)
            assert restricted_energy >= kernel.cols - alpha * source_dimension
            assert restricted_energy <= energy
            gains.append(gain)
            energies.append(energy)

        mean_energy = sum(energies) / len(group)
        target_covariance = ambient_covariance[:dimension, :dimension]
        assert mean_energy == (target_projection * target_covariance).trace()
        assert mean_energy**2 <= old_rank * overlap
        assert sum(gains) / len(group) >= Q(source_dimension, 2 * dimension) * (
            dimension - old_rank - nu * dimension
        )
        choice = gains.index(max(gains))
        assert gains[choice] > 0
        current = current.row_join(translates[choice])

    print(
        f"S_r dimension {ramified_dimension}, target dimension {dimension}, "
        f"{len(group)} translates: trace and rank checks passed."
    )


if __name__ == "__main__":
    check_model(3)
    # A conspicuous source restriction tests the general lemma with gamma=1/3.
    # The number-theoretic application has the smaller bound gamma=b^(-8).
    check_model(2)
    assert 1 + Q(1, 3) + Q(2, 3**4) < 2
    for b in [3, 4, 10, 100, 1000]:
        x = b**4
        dimension = x * (x + 9)
        orbit_size = (x - 5)**2
        squared_norm = 1 - Q(5, x)
        assert dimension * squared_norm**2 / orbit_size == 1 + Q(9, x)
        missing = 1 - Q(orbit_size, dimension)
        assert missing == 1 - squared_norm**2 / (1 + Q(9, x))
        assert missing == Q(19 * x - 25, x * (x + 9))
        assert x * missing == 19 - Q(196, x + 9)
    print("Exact extremal cyclic models and the universal b >= 3 allowance passed.")
