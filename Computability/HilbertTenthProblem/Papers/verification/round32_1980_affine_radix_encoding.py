#!/usr/bin/env python3
"""Finite sparse regressions for the 95-operation additive-radix code.

The universal argument is in AFFINE_RADIX_95_PROOF.md. This independently
compiles a sample logical circuit, checks its full physical coefficient
layout, and exercises complete sparse low-digit carries. No B**target or
universal fixed-index numeral is constructed.
"""
from __future__ import annotations

from collections import defaultdict
import json
from pathlib import Path

from round30_1980_linear_radix_encoding import (
    need, mono, polynomial, scaled, square_terms, sparse_digits,
    target_polynomial, next_power_two,
)

HERE = Path(__file__).resolve().parent
OUT = HERE / "round32_1980_affine_radix_encoding.json"


def split_bit_clear(value, forbidden_bit):
    need(value >= 0 and forbidden_bit >= 2 and forbidden_bit & (forbidden_bit-1) == 0,
         "nonnegative value and nonunit power-of-two forbidden bit")
    if value & forbidden_bit:
        result = (value-forbidden_bit, forbidden_bit//2, forbidden_bit//2)
    else:
        result = (value, 0, 0)
    need(sum(result) == value and all(0 <= item <= value for item in result),
         "three-way decomposition has the required sum and nonnegative pieces")
    need(all(item & forbidden_bit == 0 for item in result), "each piece clears the fixed bit")
    return result


def expand_logical(poly, groups):
    result = defaultdict(int)
    for (left, right), coefficient in poly.items():
        for physical_left in groups[left]:
            for physical_right in groups[right]:
                result[mono(physical_left, physical_right)] += coefficient
    return {key: value for key, value in result.items() if value}


def make_layout():
    logical_names = ["x", "delta", "X", "Y", "Z", "delta_copy", "u",
                     "v", "a", "z", "zero"]
    groups = {name: (name,) if name in ("x", "delta") else
              tuple(name+"_"+str(index) for index in range(3)) for name in logical_names}
    physical_names = [physical for name in logical_names for physical in groups[name]]
    weights = {"x": 0}
    weights.update({name: 6*3**index for index, name in enumerate(physical_names[1:])})
    logical_rows = [
        ("copy_X", polynomial((1, "X", "X"), (-1, "x", "x"))),
        ("copy_Y", polynomial((1, "Y", "Y"), (-1, "x", "x"))),
        ("copy_Z", polynomial((1, "Z", "Z"), (-1, "x", "x"))),
        ("copy_delta", polynomial((1, "delta_copy", "delta_copy"), (-1, "delta", "delta"))),
        ("guard", polynomial((2, "x", "X"), (-2, "delta", "delta_copy"), (-2, "u", "delta"))),
        ("multiply", polynomial((2, "x", "X"), (-2, "v", "delta"))),
        ("add_one", polynomial((2, "x", "delta"), (2, "delta", "delta_copy"), (-2, "a", "delta"))),
        ("add", polynomial((2, "v", "delta"), (2, "a", "delta"), (-2, "z", "delta"))),
        ("zero", polynomial((2, "zero", "delta"))),
    ]
    rows = []
    for name, logical in logical_rows:
        physical = expand_logical(logical, groups)
        rows.extend([(name+"+", physical), (name+"-", scaled(physical, -1))])
    rows.extend([(name, polynomial((1, "delta", "delta")))
                 for name in ("unit_plain", "unit_five", "unit_seven")])
    maximum = max(weights.values())
    spacing = 4*maximum+6
    targets = [(len(rows)+1)*spacing+2*maximum+index*spacing for index in range(len(rows))]
    complement = defaultdict(int)
    for target, (_, poly) in zip(targets, rows):
        for (left, right), coefficient in poly.items():
            multiplicity = 1 if left == right else 2
            need(coefficient % multiplicity == 0, "physical divided coefficient is integral")
            divided = coefficient//multiplicity
            need(divided in (-1, 1), "physical divided coefficient remains plus or minus one")
            complement[target-weights[left]-weights[right]] += divided
        complement[target-3] += 1
    for target, logical_copies in ((targets[-2], ("X", "Y")),
                                    (targets[-1], ("X", "Y", "Z"))):
        complement[target-1] += 1
        for logical in logical_copies:
            for physical in groups[logical]:
                complement[target-1-weights[physical]] += 1
    complement = {key: value for key, value in complement.items() if value}
    need(set(complement.values()) <= {-1, 1}, "fixed coefficient instructions never collide")
    for index, target in enumerate(targets):
        for offset in range(3):
            weights["dummy_%d_%d" % (index, offset)] = target+offset
    indicator = set(weights.values())-{0}
    need(len(indicator) == len(weights)-1, "all indicator positions are distinct")
    return {"weights": weights, "groups": groups, "logical_rows": logical_rows,
            "physical_names": physical_names, "rows": rows, "targets": targets,
            "last": targets[-1], "K": targets[-1]+3, "M": maximum,
            "spacing": spacing, "D": complement, "indicator": indicator}


def symbolic_checks(layout):
    weights, targets, last = layout["weights"], layout["targets"], layout["last"]
    terms = square_terms(weights)
    true_weights = {name: weights[name] for name in layout["physical_names"]}
    degrees = [degree for degree, _, _ in square_terms(true_weights)]
    need(len(degrees) == len(set(degrees)), "quadratic weights uniquely identify physical pairs")
    need(min(layout["D"])+min(targets) > last+2, "all dummy products are beyond the last tested digit")
    need(min(layout["D"]) > layout["M"], "all variable tests lie below the complementary polynomial")
    need(min(layout["D"]) > 0 and max(layout["D"]) < layout["K"], "short positive-degree support")
    x_square = polynomial((1, "x", "x"))
    pad_five = expand_logical(polynomial((1, "x", "x"), (2, "x", "X"), (2, "x", "Y")), layout["groups"])
    pad_seven = expand_logical(polynomial((1, "x", "x"), (2, "x", "X"), (2, "x", "Y"), (2, "x", "Z")), layout["groups"])
    records = []
    for index, (target, (name, expected)) in enumerate(zip(targets, layout["rows"])):
        need(target_polynomial(layout, target, terms) == expected, "exact physical target " + name)
        for offset in (-5, -4, -2, 1, 2):
            need(target_polynomial(layout, target+offset, terms) == {}, "empty reset/window position")
        need(target_polynomial(layout, target-3, terms) == x_square, "reset coefficient equals x squared exactly")
        expected_pad = pad_five if index == len(targets)-2 else pad_seven if index == len(targets)-1 else {}
        need(target_polynomial(layout, target-1, terms) == expected_pad, "exact isolated five/seven padding")
        records.append({"name": name, "target": target,
                        "physical_terms": [[value, *key] for key, value in sorted(expected.items())]})
    residue_pairs = 0
    for d_exponent in layout["D"]:
        for c_exponent, _, _ in terms:
            exponent = d_exponent+c_exponent
            if exponent <= last+2:
                need(exponent % 6 in (0, 3, 5), "only permitted low residue classes occur")
                residue_pairs += 1
    for position in true_weights.values():
        need(target_polynomial(layout, position, terms) == {}, "true variable target is untouched")
    need({1+value for value in layout["D"].values()} <= {0, 1, 2}, "baseline-one digits stay below four")
    return {"logical_coordinate_count": len(layout["groups"]),
            "true_physical_coordinate_count": len(true_weights),
            "all_coordinate_count_including_dummies": len(weights),
            "target_count": len(targets), "targets": records,
            "maximum_true_weight": layout["M"], "row_spacing": layout["spacing"],
            "last_target": last, "short_length_K": layout["K"],
            "coefficient_terms": len(layout["D"]),
            "sum_absolute_coefficients": sum(map(abs, layout["D"].values())),
            "checked_low_convolution_pairs": residue_pairs,
            "exact_x_square_resets": True, "exact_five_and_seven_padding": True,
            "dummy_exclusion_through_last_plus_two": True,
            "empty_low_residue_classes": [1, 2, 4]}


def physical_assignment(layout, logical, H0):
    result = {name: 0 for name in layout["weights"]}
    for name, group in layout["groups"].items():
        values = (logical.get(name, 0),) if len(group) == 1 else split_bit_clear(logical.get(name, 0), H0)
        for physical, value in zip(group, values):
            result[physical] = value
    return result


def numeric_raw_low(layout, values):
    maximum = layout["last"]+2
    degree_limit = maximum-min(layout["D"])
    code_square = defaultdict(int)
    for exponent, (left, right), multiplicity in square_terms(layout["weights"]):
        if exponent <= degree_limit:
            code_square[exponent] += multiplicity*values[left]*values[right]
    d_terms = sorted(layout["D"].items())
    result = defaultdict(int)
    for c_exponent, value in code_square.items():
        if value:
            for d_exponent, coefficient in d_terms:
                if c_exponent+d_exponent > maximum:
                    break
                result[c_exponent+d_exponent] += value*coefficient
    return {key: value for key, value in result.items() if value}


def positions_to_inspect(layout):
    return set(layout["indicator"]) | {
        target+offset for target in layout["targets"] for offset in range(-5, 3)}


def first_mask_check(layout, values, H0, B):
    H, b = H0+1, B-H0-1
    need(B & (B-1) == 0 and H0 & (H0-1) == 0 and B > H, "power-of-two radix and forbidden bit")
    need(0 < values["x"] < b and b < B, "positive queried input and input gap")
    need(B-1-b == H0, "first-mask coefficient is exactly the fixed bit")
    for name, value in values.items():
        need(0 <= value < B, "physical values fit their radix digit")
        if name != "x":
            need(value & H0 == 0, "every encoded digit passes the first mask")


def full_sparse_checks(layout, unit_examples):
    positions = positions_to_inspect(layout)
    valid_cases, wide_cases, rejected_cases = [], [], []
    mask_checks, events_total = 0, 0
    for H0 in (64, 256):
        inputs = (1, 2, 7, H0//2, H0-1, H0, H0+1, 2*H0-1, 2*H0, 2*H0+1)
        for x in inputs:
            logical = {"x": x, "delta": 1, "X": x, "Y": x, "Z": x,
                       "delta_copy": 1, "u": x*x-1, "v": x*x,
                       "a": x+1, "z": x*x+x+1, "zero": 0}
            values = physical_assignment(layout, logical, H0)
            total_square = sum(values.values())**2
            B = next_power_two(max(H0+2+x, 8*total_square+1, 32*x*x+1))
            first_mask_check(layout, values, H0, B)
            raw = numeric_raw_low(layout, values)
            need(max(map(abs, raw.values())) < B//4, "necessary raw coefficients are small")
            need(total_square < B**3//64, "full-code coefficient bound")
            digits, events, _ = sparse_digits(raw, positions, B)
            for index, target in enumerate(layout["targets"]):
                need(digits[target]["incoming"] == 0, "all necessary target carries vanish")
                expected = 1 if index >= len(layout["targets"])-3 else 0
                need([digits[target+offset]["digit"] for offset in range(3)] == [expected, 0, 0],
                     "exact necessary three-digit target")
            for position in layout["indicator"]:
                need(digits[position]["digit"] < 4, "every necessary mask digit passes")
                mask_checks += 1
            events_total += events
            valid_cases.append({"H0": H0, "x": x, "B": B, "b": B-H0-1,
                                "coordinate_sum_square": total_square})
    # Large arbitrary physical digits exercise genuinely three-digit raw
    # coefficients and high signed carries; rows need not be satisfied.
    for seed in range(8):
        H0, B = 64, 1 << 20
        values = {name: 0 for name in layout["weights"]}
        values["x"] = B-H0-2-seed
        for index, name in enumerate(layout["weights"]):
            if name != "x":
                values[name] = ((B//3 + (index+1)*(7919+seed*101)) % B) & ~H0
        first_mask_check(layout, values, H0, B)
        need(sum(values.values())**2 < B**3//64, "wide code obeys the full coefficient bound")
        raw = numeric_raw_low(layout, values)
        need(max(map(abs, raw.values())) > B*B, "wide code actually has more than two raw digits")
        digits, events, _ = sparse_digits(raw, positions, B)
        for target in layout["targets"][:-2]:
            need(digits[target]["incoming"] == 0, "resets work for wide signed coefficients")
        for target in layout["targets"]:
            need(raw[target-3] == values["x"]**2, "numerical reset equals input square")
        events_total += events
        wide_cases.append({"B": B, "H0": H0, "seed": seed,
                           "largest_absolute_raw_coefficient": max(map(abs, raw.values()))})
    # These assignments deliberately fail a circuit row; they isolate the
    # necessity of BOTH padding tests while retaining exact input copies.
    for B, delta, x in unit_examples:
        H0 = next_power_two(delta+1)
        logical = {"x": x, "delta": delta, "X": x, "Y": x, "Z": x,
                   "delta_copy": delta}
        values = physical_assignment(layout, logical, H0)
        if x >= B-H0-1 or sum(values.values())**2 >= B**3//64:
            continue
        first_mask_check(layout, values, H0, B)
        raw = numeric_raw_low(layout, values)
        digits, events, _ = sparse_digits(raw, positions, B)
        t0, t5, t7 = layout["targets"][-3:]
        need(digits[t0]["incoming"] == 0, "plain unit has reset carry zero")
        need(digits[t5]["incoming"] == 5*x*x//B, "exact five padding carry")
        need(digits[t7]["incoming"] == 7*x*x//B, "exact seven padding carry")
        windows = [[digits[target+offset]["digit"] for offset in range(3)] for target in (t0, t5, t7)]
        need(all(value < 4 for value in windows[0]+windows[1]), "plain and five tests admit this nonunit")
        need(any(value >= 4 for value in windows[2]), "seven test rejects this nonunit")
        events_total += events
        rejected_cases.append({"B": B, "H0": H0, "delta": delta, "x": x, "windows": windows})
    need(rejected_cases, "at least one complete code witnesses why seven padding is necessary")
    return {"valid_necessity_cases": valid_cases, "wide_signed_carry_cases": wide_cases,
            "nonunits_passing_five_but_failing_seven": rejected_cases,
            "third_mask_digit_checks": mask_checks, "sparse_events_processed": events_total,
            "no_B_to_target_integer_constructed": True}


def local_checks():
    decomposition_cases, paired_cases, reset_cases = 0, 0, 0
    for power in range(1, 13):
        H0 = 1 << power
        for value in range(8*H0+17):
            split_bit_clear(value, H0)
            decomposition_cases += 1
    def allowed(value, B):
        return all((value//(B**offset)) % B < 4 for offset in range(3))
    for B in (16, 32, 64):
        for value in range(-B**3//64+1, B**3//64):
            need((allowed(value, B) and allowed(-value, B)) == (value == 0),
                 "paired three-digit windows detect zero")
            paired_cases += 1
    for B in (16, 32, 64):
        for previous in range(-B*B//8+1, B*B//8):
            incoming = previous//(B*B)
            need(incoming in (-1, 0), "two empty positions reduce the carry")
            for x in range(1, B):
                reset = (x*x+incoming)//B
                need(0 <= reset < B and reset//B == 0, "reset plus empty slot erases the carry")
                reset_cases += 1
    first_pairs, both_pairs, examples = 0, 0, []
    for B in (64, 128, 256, 512, 1024, 2048, 4096, 8192):
        for delta in range(1, B):
            square = delta*delta
            if not allowed(square, B):
                continue
            for x in range(delta, B):
                first_pairs += 1
                h5, h7 = 5*x*x//B, 7*x*x//B
                need(-7 < 7*h5-5*h7 < 5, "exact coupled-floor estimate")
                five, seven = allowed(square+h5, B), allowed(square+h7, B)
                if delta > 1 and five:
                    examples.append((B, delta, x))
                if five and seven:
                    both_pairs += 1
                    need(delta == 1, "all three unit tests force unit one")
    return ({"bit_decomposition_cases": decomposition_cases,
             "paired_three_digit_cases": paired_cases, "reset_cases": reset_cases,
             "first_unit_test_pairs": first_pairs, "all_unit_tests_pass_pairs": both_pairs,
             "nonunit_pairs_passing_five_only": len(examples),
             "unit_radices": [64, 128, 256, 512, 1024, 2048, 4096, 8192]}, examples)


def verify():
    layout = make_layout()
    symbolic = symbolic_checks(layout)
    local, examples = local_checks()
    return {"status": "PASS",
            "scope": "finite exact physical compiler/support, sparse carries and local unit regressions; not a universality or full Pell-witness proof",
            "proof": "../1980/AFFINE_RADIX_95_PROOF.md",
            "symbolic_layout": symbolic,
            "local_exhaustive_families": local,
            "full_sparse_codes": full_sparse_checks(layout, examples),
            "admissibility_boundary": "Toy H0 choices exercise explicit coefficient and bit-mask bounds; they do not instantiate the enormous universal fixed-index H0. No giant fixed index or B**target is constructed."}


if __name__ == "__main__":
    receipt = verify()
    OUT.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(receipt["status"], receipt["scope"])
    print(json.dumps(receipt["local_exhaustive_families"], sort_keys=True))
    print("Full sparse valid/wide/rejected:", len(receipt["full_sparse_codes"]["valid_necessity_cases"]),
          len(receipt["full_sparse_codes"]["wide_signed_carry_cases"]),
          len(receipt["full_sparse_codes"]["nonunits_passing_five_but_failing_seven"]))
