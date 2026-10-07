#!/usr/bin/env python3
"""Finite checks of Paley, reflected-matching, repair and mixture formulas.

Run from any working directory:
    python path/to/verification/check_spectra.py

Only NumPy and the Python standard library are required. All matrices are
normalized in orthonormal point-mass bases for their stated probability
measures. The JSON file is written beside this script unless --output is
provided. These checks support, but do not replace, the analytic proofs.
They do not construct the large arithmetic tuple laws.
"""

import argparse
from itertools import combinations, product
import json
import math
from pathlib import Path
import platform

import numpy as np


TOLERANCE = 3e-11
PALEY_PRIMES = (3, 5, 7, 13)
MIXTURE_PRIMES = (3, 5)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def close(actual, expected, message):
    residual = abs(float(actual) - float(expected))
    require(residual <= TOLERANCE * (1.0 + abs(float(expected))), message)
    return residual


def matrix_norm(matrix):
    return float(np.linalg.svd(matrix, compute_uv=False)[0])


def paley_indicator(prime):
    residues = {value * value % prime for value in range(1, prime)}
    coordinates = np.arange(prime)
    differences = (coordinates[None, :] - coordinates[:, None]) % prime
    return np.isin(differences, tuple(sorted(residues))).astype(float)


def predicted_nonconstant_singular_value(prime):
    if prime % 4 == 1:
        return (math.sqrt(prime) + 1.0) / (2.0 * prime)
    return math.sqrt(prime + 1.0) / (2.0 * prime)


def paley_and_reflected_matching(prime):
    indicator = paley_indicator(prime)
    density = (prime - 1.0) / (2.0 * prime)
    square_operator = indicator / prime
    constant_operator = np.ones((prime, prime)) / prime
    row_mean_error = float(np.max(np.abs(indicator.mean(axis=1) - density)))
    column_mean_error = float(np.max(np.abs(indicator.mean(axis=0) - density)))
    require(max(row_mean_error, column_mean_error) < TOLERANCE,
            "The strict-square matrix is not biregular")

    singular_values = np.linalg.svd(square_operator, compute_uv=False)
    nonconstant_actual = matrix_norm(square_operator - density * constant_operator)
    nonconstant_formula = predicted_nonconstant_singular_value(prime)
    singular_value_error = close(nonconstant_actual, nonconstant_formula,
                                 "Paley nonconstant singular-value formula failed")
    centered_half_actual = matrix_norm(square_operator - 0.5 * constant_operator)
    centered_half_bound = (math.sqrt(prime) + 1.0) / (2.0 * prime)
    require(centered_half_actual <= centered_half_bound + TOLERANCE,
            "The one-edge Gauss-sum upper bound failed")

    # Character vectors have norm one in the probability-space convention.
    coordinates = np.arange(prime)
    characters = np.exp(2j * np.pi * coordinates[:, None]
                        * coordinates[None, :] / prime)
    images = square_operator @ characters
    multipliers = np.sum(characters.conj() * images, axis=0) / prime
    fourier_residual = float(np.max(np.abs(images - characters * multipliers)))
    require(fourier_residual < TOLERANCE, "Character diagonalization failed")
    close(abs(multipliers[0]), density, "The constant Fourier multiplier is wrong")
    close(float(np.max(np.abs(multipliers[1:]))), nonconstant_formula,
          "The character and singular-value computations disagree")

    states = np.array(list(product(range(prime), repeat=2)), dtype=int)
    state_count = len(states)
    matching_kernel = (
        indicator[states[:, 0, None], states[None, :, 1]]
        * indicator[states[None, :, 0], states[:, 1, None]]
    )
    require(np.array_equal(matching_kernel, matching_kernel.T),
            "The reflected matching is not symmetric")
    matching_operator = matching_kernel / state_count
    matching_eigenvalues = np.linalg.eigvalsh(matching_operator)

    predicted_eigenvalues = [float(value * value) for value in singular_values]
    for first, second in combinations(singular_values, 2):
        predicted_eigenvalues.extend((float(first * second), float(-first * second)))
    predicted_eigenvalues.sort()
    full_spectrum_error = float(np.max(np.abs(
        matching_eigenvalues - np.array(predicted_eigenvalues))))
    require(full_spectrum_error < TOLERANCE,
            "The full reflected-matching spectrum is not the SVD product spectrum")
    negative_actual = max(0.0, float(-matching_eigenvalues[0]))
    negative_formula = density * nonconstant_formula
    negative_error = close(negative_actual, negative_formula,
                           "The exact reflected-matching negative defect failed")
    centered_matching = matching_operator - density ** 2 / state_count
    centered_matching_norm = float(np.max(np.abs(np.linalg.eigvalsh(centered_matching))))
    centered_matching_error = close(centered_matching_norm, negative_formula,
                                    "The centered matching norm formula failed")
    matching_mass_error = close(float(matching_kernel.mean()), density ** 2,
                                "The unnormalized matching mass is not q squared")

    # Use a genuine complex Fourier singular pair. This checks the phase
    # in the p == 3 mod 4 case, where the square matrix is not symmetric.
    maximizing_frequency = 1 + int(np.argmax(np.abs(multipliers[1:])))
    multiplier = multipliers[maximizing_frequency]
    phase = multiplier / abs(multiplier)
    singular_right = characters[:, maximizing_frequency]
    singular_left = phase * singular_right
    singular_pair_residual = max(
        float(np.max(np.abs(square_operator @ singular_right
                            - nonconstant_formula * singular_left))),
        float(np.max(np.abs(square_operator.conj().T @ singular_left
                            - nonconstant_formula * singular_right))),
    )
    require(singular_pair_residual < TOLERANCE,
            "The phase-corrected complex singular pair failed")
    negative_function = (singular_right[states[:, 1]]
                         - singular_left[states[:, 0]]) / math.sqrt(2.0)
    function_norm_squared = float(np.vdot(negative_function, negative_function).real
                                  / state_count)
    close(function_norm_squared, 1.0, "The negative eigenfunction is not normalized")
    negative_function_residual = float(np.linalg.norm(
        matching_operator @ negative_function + negative_formula * negative_function)
        / math.sqrt(state_count))
    require(negative_function_residual < TOLERANCE,
            "The complex negative eigenfunction has a wrong phase or tensor order")
    function_supremum = float(np.max(np.abs(negative_function)))
    require(function_supremum <= math.sqrt(2.0) + TOLERANCE,
            "The bounded negative eigenfunction estimate failed")
    rayleigh = np.vdot(negative_function, matching_operator @ negative_function)
    rayleigh /= state_count
    close(rayleigh.real, -negative_formula, "The negative Rayleigh value failed")
    require(abs(rayleigh.imag) < TOLERANCE, "The symmetric cut form was not real")

    # Uniform diagonal probability measure on the p^2-state row space has
    # cut operator I. The added mass equals the coefficient of this shift.
    repair_mass = negative_formula
    repaired_operator = matching_operator + repair_mass * np.eye(state_count)
    repaired_minimum = float(np.linalg.eigvalsh(repaired_operator)[0])
    require(repaired_minimum >= -TOLERANCE, "The diagonal repair was not PSD")
    require(abs(repaired_minimum) < TOLERANCE,
            "The claimed minimal uniform diagonal shift was not on the PSD boundary")
    half_shift_minimum = float(np.linalg.eigvalsh(
        matching_operator + 0.5 * repair_mass * np.eye(state_count))[0])
    close(half_shift_minimum, -0.5 * negative_formula,
          "The half-strength diagonal shift did not retain the predicted negative eigenvalue")

    return {
        "prime": prime,
        "prime_modulo_four": prime % 4,
        "density_q": density,
        "single_edge_normalized_matrix_size": [prime, prime],
        "row_and_column_mean_maximum_error": max(row_mean_error, column_mean_error),
        "nonconstant_singular_value_matrix": nonconstant_actual,
        "nonconstant_singular_value_formula": nonconstant_formula,
        "nonconstant_singular_value_error": singular_value_error,
        "centered_at_half_norm": centered_half_actual,
        "centered_at_half_Gauss_upper_bound": centered_half_bound,
        "Fourier_diagonalization_maximum_error": fourier_residual,
        "reflected_matching_normalized_matrix_size": [state_count, state_count],
        "reflected_matching_full_spectrum_maximum_error": full_spectrum_error,
        "matching_mass_error": matching_mass_error,
        "negative_part_matrix": negative_actual,
        "negative_part_formula": negative_formula,
        "negative_part_error": negative_error,
        "centered_matching_norm": centered_matching_norm,
        "centered_matching_norm_error": centered_matching_error,
        "complex_singular_frequency": maximizing_frequency,
        "complex_singular_phase": {"real": float(phase.real), "imag": float(phase.imag)},
        "complex_singular_pair_maximum_error": singular_pair_residual,
        "complex_negative_function_residual": negative_function_residual,
        "negative_function_supremum": function_supremum,
        "negative_function_Rayleigh_value": float(rayleigh.real),
        "unrestricted_repair_mass_necessary_bound": negative_formula / 2.0,
        "uniform_diagonal_repair_mass": repair_mass,
        "repaired_minimum_eigenvalue": repaired_minimum,
        "half_strength_diagonal_repair_minimum_eigenvalue": half_shift_minimum,
    }


def four_label_mixture(prime, mixture_mass):
    """Enumerate the joint law, not just its asserted scalar norm formula."""
    require(0.0 <= mixture_mass <= 1.0, "Mixture mass is not a probability")
    outputs = np.array(list(product(range(prime), repeat=3)), dtype=int)
    joint = np.full((prime, len(outputs)), (1.0 - mixture_mass) / prime ** 4)
    for output_index, output in enumerate(outputs):
        if output[0] == output[1] == output[2]:
            joint[output[0], output_index] += mixture_mass / prime
    close(float(joint.sum()), 1.0, "The four-label law does not have total mass one")
    input_marginal = joint.sum(axis=1)
    input_marginal_error = float(np.max(np.abs(input_marginal - 1.0 / prime)))
    require(input_marginal_error < TOLERANCE, "The X marginal is not uniform")
    output_marginal = joint.sum(axis=0)
    output_coordinate_error = 0.0
    for coordinate in range(3):
        masses = np.bincount(outputs[:, coordinate], weights=output_marginal,
                             minlength=prime)
        output_coordinate_error = max(output_coordinate_error,
                                      float(np.max(np.abs(masses - 1.0 / prime))))
    require(output_coordinate_error < TOLERANCE, "An output coordinate is not uniform")

    positive_outputs = output_marginal > 0.0
    matrix = joint[:, positive_outputs].T
    matrix = matrix / np.sqrt(output_marginal[positive_outputs])[:, None]
    matrix = matrix / np.sqrt(input_marginal)[None, :]
    constant_input = np.sqrt(input_marginal)
    mean_zero_projection = np.eye(prime) - np.outer(constant_input, constant_input)
    restricted_singular_values = np.linalg.svd(matrix @ mean_zero_projection,
                                               compute_uv=False)
    actual = float(restricted_singular_values[0])
    agreement_mass = mixture_mass + (1.0 - mixture_mass) / prime ** 2
    expected = mixture_mass / math.sqrt(agreement_mass)
    norm_error = close(actual, expected, "The exact four-label conditional norm failed")
    full_restricted_spectrum_error = max(
        float(np.max(np.abs(restricted_singular_values[:-1] - expected))),
        float(abs(restricted_singular_values[-1])),
    )
    require(full_restricted_spectrum_error < TOLERANCE,
            "The conditional operator is not scalar on all nonconstant singular directions")
    equal_outputs = np.all(outputs == outputs[:, :1], axis=1)
    close(float(output_marginal[equal_outputs].sum()), agreement_mass,
          "The enumerated agreement event has the wrong probability")

    full_array = joint.reshape((prime,) * 4)
    cut_checks = []
    for left in ((0, 1), (0, 2), (0, 3)):
        right = tuple(index for index in range(4) if index not in left)
        # A probability-mass cut matrix becomes a normalized operator
        # after multiplication by p^2, since each ambient half state has
        # base probability 1/p^2. Its PSD sign is unaffected by this scale.
        cut_operator = full_array.transpose(left + right).reshape(prime ** 2, prime ** 2)
        cut_operator = prime ** 2 * cut_operator
        symmetry_error = float(np.max(np.abs(cut_operator - cut_operator.T)))
        minimum = float(np.linalg.eigvalsh(cut_operator)[0])
        require(symmetry_error < TOLERANCE, "A balanced mixture cut was not symmetric")
        require(minimum >= -TOLERANCE, "A balanced mixture cut was not PSD")
        cut_checks.append({"left_coordinates_zero_based": list(left),
                           "minimum_eigenvalue": minimum,
                           "symmetry_error": symmetry_error})
    return {
        "prime": prime,
        "mixture_mass": mixture_mass,
        "enumerated_joint_states": prime ** 4,
        "positive_output_states": int(positive_outputs.sum()),
        "maximum_coordinate_marginal_error": max(input_marginal_error,
                                                  output_coordinate_error),
        "conditional_norm_matrix": actual,
        "conditional_norm_formula": expected,
        "conditional_norm_error": norm_error,
        "full_nonconstant_spectrum_error": full_restricted_spectrum_error,
        "output_agreement_probability": agreement_mass,
        "balanced_cut_checks": cut_checks,
    }


def round_floats(value):
    if isinstance(value, float):
        return float(format(value, ".15g"))
    if isinstance(value, dict):
        return {key: round_floats(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [round_floats(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=None,
                        help="Optional path for JSON; by default print JSON to stdout.")
    arguments = parser.parse_args()
    paley_cases = [paley_and_reflected_matching(prime) for prime in PALEY_PRIMES]
    mixture_cases = []
    for prime in MIXTURE_PRIMES:
        for mixture_mass in (0.0, 0.02, 0.5, prime ** -0.5, 1.0):
            mixture_cases.append(four_label_mixture(prime, mixture_mass))
    asymptotic_checks = []
    for prime in (3, 5, 7, 13, 101, 1009, 10007):
        mass = prime ** -0.5
        norm = mass / math.sqrt(mass + (1.0 - mass) / prime ** 2)
        asymptotic_checks.append({"prime": prime, "mixture_mass": mass,
                                  "formula_norm": norm,
                                  "p_to_one_quarter_times_norm": prime ** 0.25 * norm})
    output = {
        "status": "all finite spectral and mixture checks passed",
        "scope": ("Numerical verification of displayed finite formulas. Analytic proofs "
                  "remain primary; large arithmetic tuple laws are not generated."),
        "normalization": "orthonormal point-mass bases for stated probability measures",
        "dependencies": {"Python": platform.python_version(), "NumPy": np.__version__},
        "tolerance": TOLERANCE,
        "Paley_and_reflected_matching": paley_cases,
        "four_label_mixture_enumerations": mixture_cases,
        "mixture_asymptotic_formula_checks": asymptotic_checks,
        "maximum_Paley_formula_error": max(case["nonconstant_singular_value_error"]
                                            for case in paley_cases),
        "maximum_reflected_full_spectrum_error": max(
            case["reflected_matching_full_spectrum_maximum_error"] for case in paley_cases),
        "maximum_complex_eigenfunction_error": max(
            case["complex_negative_function_residual"] for case in paley_cases),
        "maximum_mixture_norm_error": max(case["conditional_norm_error"]
                                          for case in mixture_cases),
    }
    encoded = json.dumps(round_floats(output), indent=2) + "\n"
    if arguments.output is None:
        print(encoded, end="")
    else:
        arguments.output.parent.mkdir(parents=True, exist_ok=True)
        arguments.output.write_text(encoded, encoding="utf-8")
        print(f"All checks passed; wrote {arguments.output}")


if __name__ == "__main__":
    main()
