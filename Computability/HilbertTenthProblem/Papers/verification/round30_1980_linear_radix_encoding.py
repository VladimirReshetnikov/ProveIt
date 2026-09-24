#!/usr/bin/env python3
"""Finite sparse regressions for the proposed linear-radix encoding.

This is not a universality proof or the arithmetic certificate. It checks
one explicit compiled circuit layout, exact symbolic target coefficients,
selected complete sparse code evaluations, and exhaustive small local
carry/unit families. It never constructs B**target or the fixed H index.
"""
from __future__ import annotations

from collections import defaultdict
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / "round30_1980_linear_radix_encoding.json"


def need(condition, message):
    if not condition:
        raise AssertionError(message)


def mono(left, right):
    return tuple(sorted((left, right)))


def polynomial(*terms):
    result = defaultdict(int)
    for coefficient, left, right in terms:
        result[mono(left, right)] += coefficient
    return {key: value for key, value in result.items() if value}


def scaled(poly, factor):
    return {key: value * factor for key, value in poly.items()}


def make_layout():
    names = ["x", "delta", "X", "Y", "delta_copy", "u",
             "v", "a", "z", "zero"]
    weights = {"x": 0}
    weights.update({name: 4 * 3**index for index, name in enumerate(names[1:])})
    base_rows = [
        ("copy_X", polynomial((1, "X", "X"), (-1, "x", "x"))),
        ("copy_Y", polynomial((1, "Y", "Y"), (-1, "x", "x"))),
        ("copy_delta", polynomial((1, "delta_copy", "delta_copy"),
                                  (-1, "delta", "delta"))),
        ("guard", polynomial((2, "x", "X"), (-2, "delta", "delta_copy"),
                             (-2, "u", "delta"))),
        ("multiply", polynomial((2, "x", "X"), (-2, "v", "delta"))),
        ("add_one", polynomial((2, "x", "delta"), (2, "delta", "delta_copy"),
                               (-2, "a", "delta"))),
        ("add", polynomial((2, "v", "delta"), (2, "a", "delta"),
                           (-2, "z", "delta"))),
        ("zero", polynomial((2, "zero", "delta"))),
    ]
    rows = []
    for name, poly in base_rows:
        rows.extend([(name + "+", poly), (name + "-", scaled(poly, -1))])
    rows.extend([("unit_unpadded", polynomial((1, "delta", "delta"))),
                 ("unit_padded", polynomial((1, "delta", "delta")))])
    maximum = max(weights.values())
    spacing = 4 * maximum + 4
    targets = [(len(rows)+1)*spacing + 2*maximum + index*spacing
               for index in range(len(rows))]
    last = targets[-1]
    complement = defaultdict(int)
    for target, (_, poly) in zip(targets, rows):
        for (left, right), coefficient in poly.items():
            multiplicity = 1 if left == right else 2
            need(coefficient % multiplicity == 0, "integral divided coefficient")
            divided = coefficient // multiplicity
            need(divided in (-1, 1), "divided coefficient is plus or minus one")
            complement[target-weights[left]-weights[right]] += divided
        complement[target-2] += 1
    for offset in (0, weights["X"], weights["Y"]):
        complement[last-1-offset] += 1
    complement = {key: value for key, value in complement.items() if value}
    need(set(complement.values()) <= {-1, 1}, "no coefficient accumulation")
    for index, target in enumerate(targets):
        weights["dummy_%d_0" % index] = target
        weights["dummy_%d_1" % index] = target+1
    indicator = set(weights.values()) - {0}
    need(len(indicator) == len(weights)-1, "distinct indicator positions")
    return {
        "weights": weights, "original_names": names, "rows": rows,
        "targets": targets, "last": last, "K": last+2,
        "M": maximum, "spacing": spacing, "D": complement,
        "indicator": indicator,
    }


def square_terms(weights):
    items = list(weights.items())
    result = []
    for index, (left, left_weight) in enumerate(items):
        for right, right_weight in items[index:]:
            result.append((left_weight+right_weight, mono(left, right),
                           1 if left == right else 2))
    return result


def target_polynomial(layout, exponent, terms):
    result = defaultdict(int)
    for weight, monomial, multiplicity in terms:
        coefficient = layout["D"].get(exponent-weight, 0)
        if coefficient:
            result[monomial] += coefficient * multiplicity
    return {key: value for key, value in result.items() if value}


def symbolic_layout_checks(layout):
    weights, last = layout["weights"], layout["last"]
    terms = square_terms(weights)
    original = {name: weights[name] for name in layout["original_names"]}
    original_degrees = [degree for degree, _, _ in square_terms(original)]
    need(len(original_degrees) == len(set(original_degrees)),
         "all original quadratic monomial weights are distinct")
    need(min(layout["D"])+min(layout["targets"]) > last+1,
         "dummy coordinates affect no tested coefficient or reset slot")
    x_square = polynomial((1, "x", "x"))
    special_pad = polynomial((1, "x", "x"), (2, "x", "X"), (2, "x", "Y"))
    records = []
    for index, (target, (name, expected)) in enumerate(zip(layout["targets"], layout["rows"])):
        need(target_polynomial(layout, target, terms) == expected, "exact target: " + name)
        need(target_polynomial(layout, target+1, terms) == {}, "empty second target digit")
        need(target_polynomial(layout, target-3, terms) == {}, "empty pre-reset slot")
        need(target_polynomial(layout, target-2, terms) == x_square, "exact x-square reset")
        expected_pad = special_pad if index == len(layout["rows"])-1 else {}
        need(target_polynomial(layout, target-1, terms) == expected_pad,
             "exact post-reset coefficient")
        records.append({"name": name, "target": target,
                        "polynomial": [[coefficient, *monomial]
                                       for monomial, coefficient in sorted(expected.items())]})
    residue_checks = 0
    for d_exponent in layout["D"]:
        for c_exponent, _, _ in terms:
            exponent = d_exponent+c_exponent
            if exponent <= last+1:
                need(exponent % 4 != 1, "residue-one coefficient is empty")
                residue_checks += 1
    need(min(layout["D"]) > layout["M"]+1, "variable and adjacent low slots are untouched")
    for position in original.values():
        need(target_polynomial(layout, position, terms) == {}, "low variable target is zero")
    need(min(layout["D"]) > 0 and max(layout["D"]) < layout["K"],
         "finite coefficient polynomial has positive degree and short support")
    need({1+value for value in layout["D"].values()} <= {0, 1, 2},
         "all baseline-one coefficient digits are in zero through two")
    return {
        "compiled_target_count": len(records), "targets": records,
        "coefficient_terms": len(layout["D"]),
        "sum_absolute_coefficients": sum(abs(value) for value in layout["D"].values()),
        "original_coordinate_count": len(original),
        "all_coordinate_count_including_dummies": len(weights),
        "maximum_variable_weight": layout["M"], "row_spacing": layout["spacing"],
        "last_target": last, "short_length_K": layout["K"],
        "checked_low_convolution_pairs": residue_checks,
        "dummy_separation": True, "residue_one_empty_through_last_plus_one": True,
    }


def numeric_raw(layout, values):
    code_square = defaultdict(int)
    for exponent, (left, right), multiplicity in square_terms(layout["weights"]):
        code_square[exponent] += multiplicity*values[left]*values[right]
    result = defaultdict(int)
    for d_exponent, coefficient in layout["D"].items():
        for c_exponent, square_coefficient in code_square.items():
            if square_coefficient:
                result[d_exponent+c_exponent] += coefficient*square_coefficient
    return {key: value for key, value in result.items() if value}


def sparse_digits(raw, positions, base):
    """Normalize exactly at requested positions; skip arbitrarily large gaps."""
    maximum = max(positions)
    events = sorted(set(positions) | {key for key in raw if key <= maximum})
    carry, previous = 0, -1
    result, collapsed_steps = {}, 0
    for position in events:
        gap = position-previous-1
        while gap and carry not in (-1, 0):
            carry //= base
            gap -= 1
            collapsed_steps += 1
        incoming = carry
        value = raw.get(position, 0)+incoming
        carry, digit = divmod(value, base)
        if position in positions:
            result[position] = {"digit": digit, "incoming": incoming, "outgoing": carry}
        previous = position
    return result, len(events), collapsed_steps


def next_power_two(value):
    return 1 << (value-1).bit_length()


def full_code_checks(layout):
    cases, digit_checks, event_count = [], 0, 0
    positions = {target+offset for target in layout["targets"] for offset in (-3, -2, -1, 0, 1)}
    positions |= set(layout["indicator"])
    for H in (8, 16):
        for x in range(1, 17):
            values = {name: 0 for name in layout["weights"]}
            values.update(x=x, delta=1, X=x, Y=x, delta_copy=1,
                          u=x*x-1, v=x*x, a=x+1, z=x*x+x+1)
            total = sum(values.values())
            b = next_power_two(max(max(values.values())+1, (9*total)//H+1))
            B = H*b
            need(total*total < B*B//64, "complete code satisfies the proof's coefficient bound")
            raw = numeric_raw(layout, values)
            need(max(map(abs, raw.values())) < B*B//64, "actual full raw coefficient bound")
            digits, events, _ = sparse_digits(raw, positions, B)
            for index, target in enumerate(layout["targets"]):
                need(digits[target]["incoming"] == 0, "zero incoming carry in necessity")
                need(digits[target]["digit"] == (1 if index >= len(layout["rows"])-2 else 0),
                     "exact necessary target digit")
                need(digits[target+1]["digit"] == 0, "necessary high target digit is zero")
            for position in layout["indicator"]:
                need(digits[position]["digit"] < 4, "every third-mask target passes")
                digit_checks += 1
            event_count += events
            cases.append({"H": H, "x": x, "b": b, "B": B,
                          "coordinate_sum_square": total*total})
    # Include arbitrary dummy values and a failed unit assignment. These can
    # change high coefficients but must not change any low polynomial identity.
    for seed in range(8):
        values = {name: 0 for name in layout["weights"]}
        values.update(x=2+seed, delta=1, X=2+seed, Y=2+seed, delta_copy=1)
        for index, name in enumerate(layout["weights"]):
            if name.startswith("dummy_"):
                values[name] = (index+seed) % 4
        B = 1 << 16
        raw = numeric_raw(layout, values)
        need(sum(values.values())**2 < B*B//64, "dummy-case coefficient bound")
        digits, events, _ = sparse_digits(raw, positions, B)
        for target in layout["targets"][:-1]:
            need(digits[target]["incoming"] == 0, "reset despite signed rows and dummy digits")
        event_count += events
    rejected_units = []
    for B in (4096, 16384, 65536):
        delta = 1 << ((B.bit_length()-1)//2)
        need(delta*delta == B, "exact square-root test radix")
        for H in (8, 16):
            b = B//H
            values = {name: 0 for name in layout["weights"]}
            values.update(x=delta, delta=delta, X=delta, Y=delta, delta_copy=delta)
            need(max(values.values()) < b, "rejected unit still obeys coordinate bounds")
            need(sum(values.values())**2 < B*B//64, "rejected-unit coefficient bound")
            raw = numeric_raw(layout, values)
            digits, events, _ = sparse_digits(raw, positions, B)
            first, second = layout["targets"][-2:]
            need(digits[first]["incoming"] == 0, "first unit reset is exact")
            need(digits[first]["digit"] == 0 and digits[first+1]["digit"] == 1,
                 "nonunit square would pass the first two-digit test")
            need(digits[second]["incoming"] == 5 and digits[second]["digit"] == 5,
                 "last reset and padding reject the nonunit square")
            event_count += events
            rejected_units.append({"B": B, "H": H, "b": b, "delta": delta,
                                   "first_digits": [0, 1], "last_low_digit": 5})
    return {"valid_necessity_cases": len(cases), "cases": cases,
            "dummy_cases": 8, "mask_digit_checks": digit_checks,
            "complete_code_rejected_unit_cases": rejected_units,
            "sparse_events_processed": event_count,
            "no_integer_B_to_target_constructed": True}


def local_carry_checks():
    paired_count, reset_count, unit_count = 0, 0, 0
    for B in (64, 128, 256):
        def accepted(value):
            return value % B < 4 and (value//B) % B < 4
        for value in range(-B*B//4+1, B*B//4):
            need((accepted(value) and accepted(-value)) == (value == 0),
                 "two adjacent digits of paired signed rows detect exactly zero")
            paired_count += 1
        for H in (8, 16):
            b = B//H
            for x in range(1, b):
                for previous_carry in range(-B//2+1, B//2):
                    epsilon = previous_carry//B
                    reset_carry = (x*x+epsilon)//B
                    need(reset_carry >= 0 and reset_carry < B, "reset carry is nonnegative and small")
                    need(reset_carry//B == 0, "empty post-reset slot erases carry")
                    reset_count += 1
    for B in (64, 128, 256, 512, 1024):
        for H in (8, 16):
            b = B//H
            for delta in range(1, b):
                if delta*delta % B >= 4:
                    continue
                residue = delta*delta % B
                need(residue in (0, 1), "square residues modulo four")
                if residue == 1:
                    need(delta == 1, "small root of one modulo a power of two")
                for x in range(delta, b):
                    for epsilon in (-1, 0):
                        padding_carry = (5*x*x+epsilon)//B
                        need(0 <= padding_carry < B, "special padding carry is below radix")
                        if residue == 0:
                            need(delta*delta >= B and padding_carry >= 4,
                                 "zero-residue square forces rejecting padding")
                            need((delta*delta+padding_carry) % B >= 4,
                                 "second unit test rejects the zero residue")
                        if delta == 1 and x*x <= b:
                            need((delta*delta+padding_carry) % B == 1,
                                 "valid unit and bounded guard witness pass")
                        unit_count += 1
    return {"paired_integer_cases": paired_count,
            "reset_carry_cases": reset_count, "unit_modular_cases": unit_count,
            "radices_for_pairs_and_resets": [64, 128, 256],
            "radices_for_units": [64, 128, 256, 512, 1024],
            "toy_H_values": [8, 16]}


def verify():
    layout = make_layout()
    return {
        "status": "PASS",
        "scope": "finite sparse coefficient/carry regressions only; not universality, full Pell witnesses, or a certificate-size proof",
        "proof": "../1980/LINEAR_RADIX_96_PROOF.md",
        "symbolic_layout": symbolic_layout_checks(layout),
        "full_sparse_codes": full_code_checks(layout),
        "local_exhaustive_families": local_carry_checks(),
        "admissibility_boundary": "Toy H=8,16 cases check their explicit coefficient bounds; they do not instantiate the much larger H required by the universal fixed-index theorem.",
    }


if __name__ == "__main__":
    receipt = verify()
    OUT.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(receipt["status"], receipt["scope"])
    print(json.dumps(receipt["local_exhaustive_families"], sort_keys=True))
