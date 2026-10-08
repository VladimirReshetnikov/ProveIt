"""Factor-free optimization of affine vectors modulo a binary integer.

This standalone arithmetic kernel does not assert that its input describes
an embedded normal surface or an unknot certificate.  It solves linear
congruences and minimizes gcd(m, h_1, ..., h_beta) in an affine image.

All algorithms use bounded residues, extended gcd, and integer arithmetic.
No integer factorization, matrix package, phase enumeration, or randomized
selection is used.  Generators are stored as a tuple of column vectors.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from typing import Callable, Sequence


Check = Callable[[], None] | None


def _poll(check: Check) -> None:
    if check is not None:
        check()


def _modulus(value: int) -> int:
    if type(value) is not int or value < 1:
        raise ValueError("modulus must be a positive integer")
    return value


def _integer_vector(values: Sequence[int], name: str) -> tuple[int, ...]:
    result = tuple(values)
    if any(type(value) is not int for value in result):
        raise ValueError(f"{name} must contain integers")
    return result


def _matrix(values: Sequence[Sequence[int]], columns: int, name: str):
    result = tuple(_integer_vector(row, name) for row in values)
    if any(len(row) != columns for row in result):
        raise ValueError(f"{name} has an inconsistent row length")
    return result


def _dot_mod(left, right, modulus: int) -> int:
    result = 0
    for a, b in zip(left, right):
        result = (result + a * b) % modulus
    return result


def _bezout(a: int, b: int, check: Check = None):
    """Return g,u,v with g=gcd(a,b)=u*a+v*b; a,b >= 0."""
    old_r, r, old_u, u, old_v, v = a, b, 1, 0, 0, 1
    while r:
        _poll(check)
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_u, u = u, old_u - quotient * u
        old_v, v = v, old_v - quotient * v
    return old_r, old_u, old_v


@dataclass(frozen=True)
class AffineSolution:
    modulus: int
    particular: tuple[int, ...]
    generators: tuple[tuple[int, ...], ...]
    solution_count: int


@dataclass(frozen=True)
class GCDMinimum:
    divisor: int
    vector: tuple[int, ...]
    coefficients: tuple[int, ...]
    saturation_gcd_calls: int


def solve_congruences(
    matrix: Sequence[Sequence[int]],
    rhs: Sequence[int],
    modulus: int,
    *,
    variable_count: int | None = None,
    check: Check = None,
) -> AffineSolution | None:
    """Return the entire solution coset of A z = b (mod m), or None.

    The parameterization need not be injective, but its image is exactly the
    solution set.  At most `variable_count` generators are retained.  The
    count is the number of distinct z, not the number of parameter tuples.
    Empty matrices require `variable_count` unless there are zero variables.
    """
    modulus = _modulus(modulus)
    rows = tuple(tuple(row) for row in matrix)
    if variable_count is None:
        variable_count = len(rows[0]) if rows else 0
    if type(variable_count) is not int or variable_count < 0:
        raise ValueError("variable_count must be a nonnegative integer")
    rows = _matrix(rows, variable_count, "matrix")
    rhs = _integer_vector(rhs, "rhs")
    if len(rows) != len(rhs):
        raise ValueError("matrix and rhs lengths differ")

    size = variable_count
    particular = [0] * size
    basis = [[int(row == column) % modulus for row in range(size)]
             for column in range(size)]
    count = modulus ** size

    for row, target in zip(rows, rhs):
        _poll(check)
        row = tuple(value % modulus for value in row)
        coefficients = [_dot_mod(row, column, modulus) for column in basis]
        residual = (target - _dot_mod(row, particular, modulus)) % modulus
        pivot = next((index for index, value in enumerate(coefficients)
                      if value), None)
        if pivot is None:
            if residual:
                return None
            continue
        basis[0], basis[pivot] = basis[pivot], basis[0]
        coefficients[0], coefficients[pivot] = coefficients[pivot], coefficients[0]
        divisor = coefficients[0]

        # The two-column matrix [[u,-a/g],[v,d/g]] has determinant one.
        # Applying it to the parameterization changes coordinates bijectively.
        for index in range(1, size):
            _poll(check)
            value = coefficients[index]
            if not value:
                continue
            common, u, v = _bezout(divisor, value, check)
            first, other = basis[0], basis[index]
            basis[0] = [(u * x + v * y) % modulus
                        for x, y in zip(first, other)]
            basis[index] = [(-(value // common) * x
                             + (divisor // common) * y) % modulus
                            for x, y in zip(first, other)]
            divisor = common

        common = gcd(modulus, divisor)
        if residual % common:
            return None
        quotient = modulus // common
        first_value = 0 if quotient == 1 else (
            (residual // common) * pow(divisor // common, -1, quotient)
        ) % quotient
        particular = [(x + first_value * y) % modulus
                      for x, y in zip(particular, basis[0])]
        basis[0] = [(quotient * value) % modulus for value in basis[0]]
        if count % quotient:
            raise ArithmeticError("internal solution-count divisibility failure")
        count //= quotient

    return AffineSolution(modulus, tuple(particular),
                          tuple(tuple(column) for column in basis), count)


def minimise_affine_gcd(
    modulus: int,
    offset: Sequence[int],
    generators: Sequence[Sequence[int]],
    *,
    check: Check = None,
) -> GCDMinimum:
    """Minimize gcd(m, vector entries) over offset + span(generators).

    Returns a coefficient vector attaining gcd(m, all entries of the offset
    and all generators).  This stronger divisibility minimum is attained
    simultaneously at every prime dividing m, without factoring m.
    """
    modulus = _modulus(modulus)
    offset = _integer_vector(offset, "offset")
    columns = _matrix(generators, len(offset), "generators")
    current = tuple(value % modulus for value in offset)
    coefficients = []
    saturation_calls = 0

    for column in columns:
        _poll(check)
        column = tuple(value % modulus for value in column)
        common = gcd(modulus, *current, *column)
        reduced_modulus = modulus // common
        bad = gcd(reduced_modulus, *(value // common for value in current))

        if bad == 1:
            coefficient = 0
        else:
            saturated = bad
            while True:
                _poll(check)
                next_saturated = gcd(reduced_modulus, saturated * saturated)
                saturation_calls += 1
                if next_saturated == saturated:
                    break
                saturated = next_saturated
            coefficient = reduced_modulus // saturated
        current = tuple((a + coefficient * b) % modulus
                        for a, b in zip(current, column))
        coefficients.append(coefficient)
        if gcd(modulus, *current) != common:
            raise ArithmeticError("internal gcd merge failure")

    return GCDMinimum(gcd(modulus, *current), current, tuple(coefficients),
                      saturation_calls)


def _prepare_family(modulus, constants, holonomy_matrix, seam_matrix, seam_rhs,
                    variable_count):
    modulus = _modulus(modulus)
    constants = _integer_vector(constants, "constants")
    holonomy_matrix = tuple(tuple(row) for row in holonomy_matrix)
    seam_matrix = tuple(tuple(row) for row in seam_matrix)
    if variable_count is None:
        if holonomy_matrix:
            variable_count = len(holonomy_matrix[0])
        elif seam_matrix:
            variable_count = len(seam_matrix[0])
        else:
            variable_count = 0
    if type(variable_count) is not int or variable_count < 0:
        raise ValueError("variable_count must be a nonnegative integer")
    holonomy_matrix = _matrix(holonomy_matrix, variable_count, "holonomy_matrix")
    seam_matrix = _matrix(seam_matrix, variable_count, "seam_matrix")
    seam_rhs = _integer_vector(seam_rhs, "seam_rhs")
    if len(constants) != len(holonomy_matrix):
        raise ValueError("constants and holonomy_matrix lengths differ")
    if len(seam_matrix) != len(seam_rhs):
        raise ValueError("seam_matrix and seam_rhs lengths differ")
    return (modulus, constants, holonomy_matrix, seam_matrix, seam_rhs,
            variable_count)


def optimise_cyclic_affine_family(
    modulus: int,
    constants: Sequence[int],
    holonomy_matrix: Sequence[Sequence[int]],
    seam_matrix: Sequence[Sequence[int]] = (),
    seam_rhs: Sequence[int] = (),
    *,
    variable_count: int | None = None,
    certificate: bool = True,
    check: Check = None,
) -> dict:
    """Solve seams and minimize the cyclic orbit count in the affine family.

    A feasible answer includes a concrete variable assignment and holonomy
    vector.  If requested, dual congruence rows independently certify global
    optimality; verify them with `verify_optimality_certificate`.
    """
    (modulus, constants, holonomy_matrix, seam_matrix, seam_rhs,
     variable_count) = _prepare_family(modulus, constants, holonomy_matrix,
                                      seam_matrix, seam_rhs, variable_count)
    solution = solve_congruences(seam_matrix, seam_rhs, modulus,
                                 variable_count=variable_count, check=check)
    if solution is None:
        result = {"feasible": False, "solution_count": 0}
        if certificate:
            transposed = tuple(tuple(row[index] for row in seam_matrix)
                               for index in range(variable_count))
            annihilator = solve_congruences(
                transposed, (0,) * variable_count, modulus,
                variable_count=len(seam_matrix), check=check,
            )
            if annihilator is None:
                raise ArithmeticError("homogeneous system unexpectedly infeasible")
            for multiplier in annihilator.generators:
                _poll(check)
                residue = _dot_mod(multiplier, seam_rhs, modulus)
                if residue:
                    result["obstruction"] = {
                        "multipliers": list(multiplier), "residue": residue,
                    }
                    break
            if "obstruction" not in result:
                raise ArithmeticError("internal infeasibility certificate failure")
        return result

    offset = tuple((constant + _dot_mod(row, solution.particular, modulus)) % modulus
                   for constant, row in zip(constants, holonomy_matrix))
    generators = tuple(tuple(_dot_mod(row, column, modulus)
                             for row in holonomy_matrix)
                       for column in solution.generators)
    minimum = minimise_affine_gcd(modulus, offset, generators, check=check)
    parameters = list(solution.particular)
    for coefficient, column in zip(minimum.coefficients, solution.generators):
        _poll(check)
        parameters = [(a + coefficient * b) % modulus
                      for a, b in zip(parameters, column)]

    result = {
        "feasible": True,
        "solution_count": solution.solution_count,
        "minimum_components": minimum.divisor,
        "connected_member_exists": minimum.divisor == 1,
        "parameters": parameters,
        "holonomies": list(minimum.vector),
        "saturation_gcd_calls": minimum.saturation_gcd_calls,
    }
    if certificate:
        scale = modulus // minimum.divisor
        transposed = tuple(tuple(row[index] for row in seam_matrix)
                           for index in range(variable_count))
        dual_rows = []
        for constant, row in zip(constants, holonomy_matrix):
            _poll(check)
            if minimum.divisor == 1:
                dual = (0,) * len(seam_matrix)
            else:
                dual_solution = solve_congruences(
                    transposed, tuple((scale * value) % modulus for value in row),
                    modulus, variable_count=len(seam_matrix), check=check,
                )
                if dual_solution is None:
                    raise ArithmeticError("internal annihilator certificate failure")
                dual = dual_solution.particular
            if (scale * constant + _dot_mod(dual, seam_rhs, modulus)) % modulus:
                raise ArithmeticError("internal affine certificate failure")
            dual_rows.append(list(dual))
        result["dual_rows"] = dual_rows
        if not verify_optimality_certificate(
            modulus, constants, holonomy_matrix, seam_matrix, seam_rhs,
            result, variable_count=variable_count, check=check,
        ):
            raise ArithmeticError("internal certificate verification failure")
    return result


def verify_optimality_certificate(
    modulus: int,
    constants: Sequence[int],
    holonomy_matrix: Sequence[Sequence[int]],
    seam_matrix: Sequence[Sequence[int]],
    seam_rhs: Sequence[int],
    proposed: dict,
    *,
    variable_count: int | None = None,
    check: Check = None,
) -> bool:
    """Verify exact minimum using only modular products and gcd.

    This verifier does not use the congruence solver or optimizer and does not
    verify `solution_count`.  False means malformed or invalid certificate.
    """
    try:
        if not isinstance(proposed, dict):
            return False
        (modulus, constants, holonomy_matrix, seam_matrix, seam_rhs,
         variable_count) = _prepare_family(modulus, constants, holonomy_matrix,
                                          seam_matrix, seam_rhs, variable_count)
        if proposed.get("feasible") is not True:
            return False
        minimum = proposed["minimum_components"]
        if type(minimum) is not int or minimum < 1 or modulus % minimum:
            return False
        parameters = _integer_vector(proposed["parameters"], "parameters")
        holonomies = _integer_vector(proposed["holonomies"], "holonomies")
        if len(parameters) != variable_count or len(holonomies) != len(constants):
            return False
        if any(value < 0 or value >= modulus for value in parameters + holonomies):
            return False
        for row, target in zip(seam_matrix, seam_rhs):
            _poll(check)
            if (_dot_mod(row, parameters, modulus) - target) % modulus:
                return False
        calculated = tuple((constant + _dot_mod(row, parameters, modulus)) % modulus
                           for constant, row in zip(constants, holonomy_matrix))
        if calculated != holonomies or gcd(modulus, *holonomies) != minimum:
            return False
        dual_rows = _matrix(proposed["dual_rows"], len(seam_matrix), "dual_rows")
        if len(dual_rows) != len(constants):
            return False
        scale = modulus // minimum
        for constant, row, dual in zip(constants, holonomy_matrix, dual_rows):
            _poll(check)
            for index in range(variable_count):
                column = tuple(seam[index] for seam in seam_matrix)
                if (_dot_mod(dual, column, modulus) - scale * row[index]) % modulus:
                    return False
            if (_dot_mod(dual, seam_rhs, modulus) + scale * constant) % modulus:
                return False
        claimed_connected = proposed.get("connected_member_exists", minimum == 1)
        return type(claimed_connected) is bool and claimed_connected == (minimum == 1)
    except (KeyError, TypeError, ValueError):
        return False


def verify_infeasibility_certificate(
    modulus: int,
    seam_matrix: Sequence[Sequence[int]],
    seam_rhs: Sequence[int],
    proposed: dict,
    *,
    variable_count: int | None = None,
    check: Check = None,
) -> bool:
    """Verify y*A=0 and y*b nonzero (mod m), a proof that seams conflict."""
    try:
        if not isinstance(proposed, dict) or proposed.get("feasible") is not False:
            return False
        (modulus, _, _, seam_matrix, seam_rhs,
         variable_count) = _prepare_family(modulus, (), (), seam_matrix,
                                          seam_rhs, variable_count)
        obstruction = proposed["obstruction"]
        multipliers = _integer_vector(obstruction["multipliers"], "multipliers")
        if len(multipliers) != len(seam_matrix):
            return False
        for index in range(variable_count):
            _poll(check)
            column = tuple(row[index] for row in seam_matrix)
            if _dot_mod(multipliers, column, modulus):
                return False
        residue = _dot_mod(multipliers, seam_rhs, modulus)
        return (residue != 0 and type(obstruction["residue"]) is int
                and residue == obstruction["residue"])
    except (KeyError, TypeError, ValueError):
        return False
