#!/usr/bin/env python3
"""Isolated complete finite h=8 label-shift probe, with an h=9 counterexample."""
import argparse
import hashlib
import importlib.util
import json
from math import gcd, lcm
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / "research/one-anchor-independent/certify.py"
PARENT_SHA = "9e48fa6e071e279c271d4facc87aec2a7026369a2ab3b3056a68e33c41ae479d"
RHO, M, L = 1 << 47, 1 << 44, 7253


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def parent_model():
    require(sha(PARENT.read_bytes()) == PARENT_SHA, "Frozen complete one-anchor7309 verifier")
    spec = importlib.util.spec_from_file_location("frozen_shift_probe_parent", PARENT)
    require(spec is not None and spec.loader is not None, "Parent import specification")
    parent = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parent)
    # This authenticates the entire decoder, source page and ordinary proof.
    _, seed, actions, tiles, original, _ = parent.model()
    return parent, seed, actions, tiles, original


def model(original, shift):
    c = [0] * len(original)
    c[:943] = original[:943]
    for e in range(943, 2079):
        if original[e]:
            require(e - shift > 942 and not c[e - shift], "Shifted label/selector disjointness")
            c[e - shift] = original[e]
    anchor = 2079 - 2 * shift
    require(not c[anchor], "New weighted anchor disjointness")
    c[anchor] = 3 * M
    support = {e for e, value in enumerate(c) if value} | {1063 - shift, 1064 - shift}
    require(len(support) == 980 and sum(bool(v) for v in c) == 978 and sum(c) == sum(original),
            "Complete shifted support and preserved coefficients")
    arrays = []
    for t in (1, 2):
        a = [0] * len(c)
        for j in range(8):
            a[1023 - shift + j] += t ** j
            a[1003 - shift + j] += t ** (17 + j)
        for j in range(9):
            a[1013 - shift + j] += t ** (8 + j)
            a[983 - shift + j] += t ** (25 + j)
        a[anchor] += t ** 34 * (2 * t - 1)
        arrays.append(a)
    require(sum(arrays[0]) == 35 and all(v in (0, 1) for v in arrays[0]), "Complete shifted Psi-one")
    require([1024 * v for v in arrays[1][943:]] == c[943:], "Complete shifted Psi-two")
    return c, support, anchor


def dc_coefficients(c, anchor, centers):
    dc = {}
    for center in centers:
        for e, value in enumerate(c):
            if value:
                require(center - e not in dc, "Reflected residues disjoint")
                dc[center - e] = value
    for e in [30, 62] + list(range(anchor - 942, anchor + 1)):
        require(e not in dc, "Unit and reflected residues disjoint")
        dc[e] = 1
    return dc


def geometry(c, support, anchor, centers, shift, padding_start):
    dc = dc_coefficients(c, anchor, centers)
    checks = {}

    def check(name, actual, expected):
        checks[name] = {"pass": actual == expected, "actual": actual, "expected": expected}

    def hits(target):
        return sorted((e, dc[target - e]) for e in support if target - e in dc)

    start = 1014 - shift
    gap = centers[1] - centers[0]
    difference = anchor - start
    pairs = lambda d: sorted((a, b) for a in support for b in support if a - b == d)
    check("unique_phase_difference", pairs(difference), [(anchor, start)])
    check("clause_gap_absent", pairs(gap), [])
    check("gap_minus_one_PRESENT", pairs(gap - 1), [(anchor, 1013 - shift)])
    check("gap_plus_one_absent", pairs(gap + 1), [])
    check("Start_phase_target", hits(start), [(984 - shift, 1)])
    check("selector_count_target", hits(anchor), [(e, 1) for e in range(943)])
    check("Start_spatial_absent", start - 42 in support, False)
    check("anchor_bare_and_spatial_absent", [e for e in (anchor - 30, anchor - 62, anchor - 42) if e in support], [])
    for j in range(9):
        target = 1013 - shift + j
        check("temporal_copy_" + str(j), hits(target), [(983 - shift + j, 1)])
        check("temporal_no_spatial_" + str(j), target - 42 in support, False)
    for j in range(8):
        target = 1065 - shift + j
        check("spatial_copy_" + str(j), hits(target), [(1003 - shift + j, 1)])
        check("spatial_source_" + str(j), target - 42 in support, True)
        check("spatial_no_temporal_" + str(j), target in support, False)
    clause = sorted((e, c[e]) for e in support if c[e])
    adjacent = sorted((e, c[e + 1]) for e in support if c[e + 1])
    lower_extra = [(anchor, 1)] if centers[0] - 1 == 2 * anchor else []
    for center in centers:
        check("whole_clause_" + str(center), hits(center), clause)
        check("no_clause_or_predecessor_spatial_" + str(center),
              [e for e in (center - 42, center - 43) if e in support], [])
    check("complete_lower_predecessor", hits(centers[0] - 1), sorted(adjacent + lower_extra))
    check("complete_upper_predecessor", hits(centers[1] - 1), sorted(adjacent + [(anchor, 1 << 18)]))
    check("padding_predecessor", hits(padding_start - 1), [(anchor, 1 << 35)])
    zero_end = centers[1] + anchor - 943
    check("entire_padding_zero_band", [(e, hits(e)) for e in range(padding_start, zero_end + 1) if hits(e)], [])
    check("padding_spatial_absent", [e for e in range(padding_start, zero_end + 1) if e - 42 in support], [])
    max_product = max(dc) + max(support)
    check("maximum_product_field", max_product, centers[1] + anchor)
    check("last_nonzero_field", hits(max_product), [(anchor, c[0])])
    check("all_remaining_top_fields_zero", [(e, hits(e)) for e in range(max_product + 1, L) if hits(e)], [])
    first_reflection = centers[0] - anchor
    check("reflection_after_anchor", first_reflection > anchor, True)
    check("dummy_unit_then_reflection_disjoint", anchor + 1063 - shift < first_reflection + 1063 - shift, True)
    check("copies_before_unit_kernel", 1072 - shift < anchor - 942, True)
    check("no_cell_product_wrap", max_product < L, True)
    check("phase_reset_numerical", 952 + 3 * RHO // 4 + 29 < RHO, True)
    adjacent_max = max(c[e + 1] for e in support if e < 943 and c[e + 1])
    adjacent_other = sum(c[e + 1] for e in support if e >= 943 and c[e + 1])
    check("one_tile_adjacent_bound", adjacent_max + adjacent_other <= 2 * M - 1024, True)
    check("lower_predecessor_reset", 2 * M - 1024 + bool(lower_extra) + 29 < RHO, True)
    check("upper_predecessor_reset", 2 * M - 1024 + (1 << 18) + 29 < RHO, True)
    check("final_digit_reset", 7 * (M + 30) < RHO, True)
    dummy = 1063 - shift
    delta_exponents = [max(dc) + dummy, 42 + dummy, dummy]
    check("whole_safe_dummy_numerical_slack", all(L - (e + 1) >= 3 for e in delta_exponents) and RHO > 3, True)
    envelope = [0] * (max_product + 1)
    for e in support:
        for k, value in dc.items():
            envelope[e + k] += value
    extra = envelope.copy()
    for k, value in dc.items():
        extra[dummy + k] += 2 * value
    maximum, extra_maximum = max(envelope), max(extra)
    check("global29_numerical_given_temporal_bound", extra_maximum + 3 + 3 * RHO // 4 + 29 < 30 * RHO, True)
    return {"checks": checks, "failed_checks": [name for name, value in checks.items() if not value["pass"]],
            "first_reflected_exponent": first_reflection, "phase_difference": difference, "clause_gap": gap,
            "padding_zero_band": [padding_start, zero_end], "delta_exponents": delta_exponents,
            "boolean_convolution_maximum": maximum,
            "boolean_maximum_fields": [e for e, value in enumerate(envelope) if value == maximum],
            "extra_dummy_convolution_maximum": extra_maximum,
            "extra_dummy_maximum_fields": [e for e, value in enumerate(extra) if value == extra_maximum],
            "one_tile_adjacent_bound": adjacent_max + adjacent_other,
            "lower_predecessor_extra": lower_extra}


def constants(c, support, anchor, centers, shift, padding_start):
    power = lambda e: 1 << (47 * e)
    B, beta = power(L), power(L) - 1
    dc = sum(value * power(e) for e, value in dc_coefficients(c, anchor, centers).items())
    K = dc + B * power(42)
    MC = beta - sum(power(e) for e in support if e != 1) - 2 * power(1063 - shift)
    core = sum(power(e - shift) for e in range(1013, 1022))
    core += sum(power(e - shift) for e in range(1065, 1073)) + power(anchor)
    padding = (1 << 25) * power(padding_start + 18) - power(padding_start)
    expanded_padding = (RHO - 1) * sum(power(e) for e in range(padding_start, padding_start + 18))
    expanded_padding += ((1 << 25) - 1) * power(padding_start + 18)
    require(padding == expanded_padding and padding.bit_count() == 871, "Whole871-bit padding")
    native = 4 + ((1 << 46) - 2) * sum(power(e) for e in centers) + core + padding
    require(0 < dc < B and 0 < MC < beta and 0 < native < beta, "Whole shifted scalar boxes")
    require(native.bit_count() == 980 and MC.bit_count() == 47 * L - 980, "Whole shifted mask populations")
    require(MC % 4 == 2 and native % 8 == 4, "Whole shifted origin residues")
    return {"beta": beta, "K": K, "MC": MC, "MF_source": native + beta}


def modular(p, c, tiles, anchor, centers, shift, whole):
    power = lambda e: pow(2, 47 * e, p)
    inverse = pow(power(1), -1, p)
    phi = 0
    for value in reversed(c):
        phi = (phi * inverse + value) % p
    kernel = sum(power(e) for e in range(anchor - 942, anchor + 1))
    dense = (power(30) + power(62) + kernel + power(L + 42)
             + sum(power(center) for center in centers) * phi) % p
    direct = power(30) + power(62) + kernel + power(L + 42)
    for center in centers:
        for j, (w, n, east, south) in enumerate(tiles):
            direct += (1 + 1024 * (1 + w + 256 * n + 131072 * east + 33554432 * south)) * power(center - j)
        for start, bits, count in ((1023, 10, 8), (1003, 27, 8), (1013, 18, 9), (983, 35, 9)):
            direct += sum((1 << (bits + j)) * power(center - start + shift - j) for j in range(count))
        direct += 3 * M * power(center - anchor)
    require(dense == direct % p == whole["K"] % p, "Three complete shifted K routes")
    B = power(L)
    return {"p": p, "B": B, "K": dense, "B_squared": B * B % p,
            "H": (1 + B * dense + B * B) % p}


def controller(parent, c, tiles, anchor, centers, shift, whole):
    minimum = centers[1] + anchor + 1
    length_trials = [{"length": n, "least_factor": parent.least_factor(n)} for n in range(minimum, L + 1)]
    require(length_trials[-1]["least_factor"] is None
            and all(row["least_factor"] is not None for row in length_trials[:-1]), "Smallest eligible prime cell length")
    fixed = []
    for p in (47, L):
        row = modular(p, c, tiles, anchor, centers, shift, whole)
        row["base2_order"] = parent.order(2, p)
        row["B_order"] = parent.order(row["B"], p)
        require(row["B_squared"] != 1 and row["H"] != 0, "Shifted fixed controller units")
        require(gcd(47 * L, row["B_order"]["order"]) == 1, "Shifted exact order coprime to d")
        fixed.append(row)
    spacing = lcm(*(row["B_order"]["order"] for row in fixed))
    require(gcd(47 * L, spacing) == 1, "Shifted controller spacing")
    trials = []
    for j in range((47 * L - 1) // spacing + 1, (47 * L - 1) // spacing + 502):
        p = spacing * j + 1
        divisor = parent.least_factor(p)
        row = {"candidate": p, "multiplier": j, "least_factor": divisor}
        trials.append(row)
        if divisor is not None:
            continue
        row.update(modular(p, c, tiles, anchor, centers, shift, whole))
        lift = pow(2, 47 * L * (p - 1), p * p)
        require(lift % p == 1, "Shifted controller Fermat lift")
        row["lift_residue"], row["lift_quotient"] = lift, (lift - 1) // p
        if row["B_squared"] != 1 and row["H"] != 0 and row["lift_quotient"]:
            require(p > 47 * L and p % 2 == 1, "Auxiliary prime odd and above d")
            return {"length_trials": length_trials, "fixed": fixed, "spacing": spacing,
                    "auxiliary_trials": trials, "selected_lambda": p}
    raise ValueError("No auxiliary prime in501 bounded shifted-controller trials")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    parent, seed, actions, tiles, original = parent_model()
    shift = 8
    c, support, anchor = model(original, shift)
    variants = {}
    for name, centers, padding_start in (("plus3", (4129, 5188), 6277), ("plus1", (4127, 5186), 6275)):
        geometric = geometry(c, support, anchor, centers, shift, padding_start)
        require(not geometric["failed_checks"], "Shift8 geometry failed: " + repr(geometric["failed_checks"]))
        whole = constants(c, support, anchor, centers, shift, padding_start)
        controllers = controller(parent, c, tiles, anchor, centers, shift, whole)
        ports = {}
        for port, value in whole.items():
            raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
            ports[port] = {"bits": value.bit_length(), "bytes": len(raw), "sha256": sha(raw)}
        variants[name] = {"centers": centers, "padding_start": padding_start, "geometry": geometric,
                          "controller": controllers, "constant_ports": ports,
                          "raw_bytes": sum(row["bytes"] for row in ports.values())}
    c9, support9, anchor9 = model(original, 9)
    dc9 = dc_coefficients(c9, anchor9, (2 * anchor9 + 3, 2 * anchor9 + 3 + 1058))
    bad_target = 1013 - 9
    bad_hits = sorted((e, dc9[bad_target - e]) for e in support9 if bad_target - e in dc9)
    require(bad_hits == [(942, 1), (974, 1)], "Explicit first temporal-copy collision at h9")
    data = {"schema": "one_anchor_shift8_exploration_v1", "script_sha256": sha(Path(__file__).read_bytes()),
            "parent_verifier_sha256": PARENT_SHA,
            "inherited_source_page_sha256": parent.PAGE_SHA, "inherited_decoder_sha256": parent.DECODER_SHA,
            "inherited_proof_sha256": parent.PROOF_SHA,
            "seed_sha256": sha(seed.encode()), "actions_sha256": sha(encoded(actions)),
            "tiles_sha256": sha(encoded(tiles)), "all3297_coefficients_sha256": sha(encoded(c)),
            "shift": shift, "anchor": anchor, "L": L, "d": 47 * L, "physical_support": len(support),
            "coefficient_count": sum(bool(v) for v in c), "coefficient_sum": sum(c),
            "variants": variants,
            "h9_negative_control": {"target": bad_target, "actual_hits": bad_hits,
                                     "intended_hits": [(974, 1)], "extra_selector": 942},
            "scope": "Isolated finite model and proof lead only. No complete shifted ordinary proof, accepted source change, formal replay, or promotion is claimed."}
    for name, raw in (("RESULTS.json", encoded(data)), ("COEFFICIENTS.json", encoded(c))):
        if args.write:
            (HERE / name).write_bytes(raw)
        else:
            require((HERE / name).read_bytes() == raw, "Deterministic artifact differs: " + name)
    print(json.dumps({"status": "PASS", "L": L, "variants": {
        name: {"raw_bytes": item["raw_bytes"], "lambda": item["controller"]["selected_lambda"],
               "H": [row["H"] for row in item["controller"]["fixed"]]
                    + [item["controller"]["auxiliary_trials"][-1]["H"]]}
        for name, item in variants.items()}, "h9_counterexample": bad_hits,
        "results_sha256": sha(encoded(data))}, sort_keys=True))


if __name__ == "__main__":
    main()
