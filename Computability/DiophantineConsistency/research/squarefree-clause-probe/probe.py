#!/usr/bin/env python3
"""Complete finite probe with squarefree composite length and complete parity-clause geometry."""
import argparse
import hashlib
import importlib.util
import json
from math import gcd, lcm, prod
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / "research/one-anchor-independent/certify.py"
PARENT_SHA = "9e48fa6e071e279c271d4facc87aec2a7026369a2ab3b3056a68e33c41ae479d"
RHO, M = 1 << 47, 1 << 44
SPECS = {
    "squarefree_clause": {"south": 942, "west": 969, "north": 960, "east": 978,
                      "dummy": 977, "anchor": 1005, "temporal": 18, "west_copy": 18,
                      "spatial": 9, "centers": [1956], "padding": 2962, "zero_end": 2981},
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def parent_model():
    require(sha(PARENT.read_bytes()) == PARENT_SHA, "Exact frozen complete one-anchor7309 verifier")
    spec = importlib.util.spec_from_file_location("zero_flag_frozen_parent", PARENT)
    require(spec is not None and spec.loader is not None, "Parent import specification")
    parent = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parent)
    _, seed, actions, tiles, original, _ = parent.model()
    require(len(tiles) == 943 and list(tiles[1]) == [5, 0, 0, 0] and original[1] == 6145, "Exact complete old forbidden selector")
    mapping = [0] + list(range(2, 943))
    require(len(mapping) == 942 and set(mapping) == set(range(943)) - {1},
            "Full bijection onto exactly the old admissible selectors")
    selected = [tiles[j] for j in mapping]
    require(len(set(tuple(t) for t in selected)) == 942, "All admissible decoded tile identities remain distinct")
    return parent, seed, actions, selected, original


def model(original, spec):
    c = [0] * len(original)
    c[:942] = original[:1] + original[2:943]
    for name, bits, count in (("south", 35, 9), ("west", 27, 8), ("north", 18, 9), ("east", 10, 8)):
        for j in range(count):
            e = spec[name] + j
            require(e > 941 and not c[e], "Every weighted label disjoint from all selectors and labels")
            c[e] = 1 << (bits + j)
    anchor, dummy = spec["anchor"], spec["dummy"]
    require(c[anchor] == c[dummy] == 0 and c[dummy + 1] == 1024, "Zero flag/dummy; spill lands on weighted east bit zero")
    support = {e for e, value in enumerate(c) if value} | {dummy, anchor}
    require(len(c) == 3297 and len(support) == 978 and sum(bool(v) for v in c) == 976,
            "Full coefficient length,978 physical positions and976 weighted positions")
    require(sum(c) == sum(original) - 3 * M - original[1] and sum(c[942:]) == M - 1024 and max(c) < M,
            "Complete zero-flag coefficient sum and bound")
    arrays = []
    for t in (1, 2):
        a = [0] * len(c)
        for j in range(8):
            a[spec["east"] + j] += t ** j
            a[spec["west"] + j] += t ** (17 + j)
        for j in range(9):
            a[spec["north"] + j] += t ** (8 + j)
            a[spec["south"] + j] += t ** (25 + j)
        a[anchor] += t ** 34 * (2 - t)
        arrays.append(a)
    require(sum(arrays[0]) == 35 and all(v in (0, 1) for v in arrays[0]), "Psi-one includes35 controls, including zero-weight flag")
    require([1024 * v for v in arrays[1][942:]] == c[942:], "Psi-two omits flag and matches every weighted label")
    require(arrays[0][anchor] == 1 and arrays[1][anchor] == 0, "Physical flag explicitly retained despite coefficient zero")
    return c, support


def dc_coefficients(c, spec):
    dc = {}
    for center in spec["centers"]:
        for e, value in enumerate(c):
            if value:
                require(center - e not in dc, "All reflected coefficient residues disjoint")
                dc[center - e] = value
    for e in sorted({spec["temporal"], spec["west_copy"], spec["anchor"]}):
        require(e not in dc, "Unit and reflected residues disjoint")
        dc[e] = 1
    return dc


def geometry(c, support, spec, length, tiles):
    dc = dc_coefficients(c, spec)
    center = spec["centers"][0]
    require(len(spec["centers"]) == 1, "Exactly one complete clause")
    anchor, dummy, spatial = spec["anchor"], spec["dummy"], spec["spatial"]
    start = spec["north"] + 1
    checks = {}

    def check(name, actual, expected):
        def summarized(value):
            if isinstance(value, (list, tuple)) and len(value) > 8:
                return {"count": len(value), "sha256": sha(encoded(value))}
            return value
        checks[name] = {"pass": actual == expected, "actual": summarized(actual), "expected": summarized(expected)}

    def hits(target):
        return sorted((e, dc[target - e]) for e in support if target - e in dc)

    def parity_hits(target):
        return sorted((e, value % 2) for e, value in hits(target) if value % 2)

    south_targets = tuple(range(spec["north"] + 1, spec["north"] + 9))
    phase_targets = south_targets + (anchor,)
    phase_offsets = sorted({(anchor - e) % length for e in support
                            if all((target - ((anchor - e) % length)) % length in support
                                   for target in phase_targets)})
    multiple_selectors, calibrated_exclusions, unresolved = [], [], []
    last_tile_south = 511 - tiles[941][3]
    for r in phase_offsets:
        if r == 0:
            continue
        preimages = [target - r for target in south_targets]
        selectors = [e for e in preimages if 0 <= e <= 941]
        if len(selectors) >= 2 and all(0 <= e < length for e in preimages):
            multiple_selectors.append((r, selectors))
        elif (r == spec["temporal"] + 2 and selectors == [941] and 942 in preimages
              and last_tile_south & 1 == 0):
            calibrated_exclusions.append({"offset": r, "forced_selector": 941,
                                          "required_south_bit0": 1, "actual_south_bit0": 0,
                                          "south_preimages": preimages,
                                          "marker_preimage": anchor - r})
        else:
            unresolved.append((r, preimages))
    check("zero_phase_is_a_support_candidate", 0 in phase_offsets, True)
    check("all_nonzero_offsets_excluded", unresolved, [])
    check("exact_calibrated_tile941_south", last_tile_south, 74)
    check("unique_calibrated_exception_offset", [row["offset"] for row in calibrated_exclusions], [spec["temporal"] + 2])
    check("all_support_offsets_within_no_wrap_bounds", all(0 <= r <= start for r in phase_offsets), True)
    check("every_nonzero_offset_at_least_anchor_minus_lowmax", all(r >= anchor - max(support - {anchor}) for r in phase_offsets if r), True)
    check("all_offsets_classified", len(phase_offsets), 1 + len(multiple_selectors) + len(calibrated_exclusions))
    # This entire coarse argument precedes any one-hot/clause decoding.
    # The even low reflection and Boolean temporal digits force phase zero.
    low_reflections = []
    for target in range(anchor + 1):
        terms = [(e, center - target + e, c[center - target + e]) for e in support
                 if 0 <= center - target + e < len(c) and c[center - target + e]]
        require(all(index > 941 and value % 2 == 0 for _, index, value in terms),
                "Every low reflected coefficient is an even label weight")
        require(sum(value for _, _, value in terms) <= M - 1024,
                "Entire low reflected envelope bounded before any count decoding")
        low_reflections.append((target, terms))
    check("all_low_reflections_even_and_label_only", len(low_reflections), anchor + 1)
    marker_offsets = sorted(anchor - e for e in support)
    check("marker_offsets_without_onehot", all(0 <= r <= anchor for r in marker_offsets), True)
    clause_temporal_sources = [(r, center - r) for r in marker_offsets if center - r in support]
    check("sole_clause_temporal_sources_are_boolean", all(source in support and 0 <= source < length
          for _, source in clause_temporal_sources), True)
    check("clause_temporal_no_wrap", all(0 <= center - r < length for r in marker_offsets), True)
    check("Start_phase_target", parity_hits(start), [(spec["south"] + 1, 1)])
    check("second_Start_phase_target", parity_hits(spec["north"] + 8), [(spec["south"] + 8, 1)])
    check("physical_marker_target_copies_selector0", parity_hits(anchor), [(0, 1)])
    check("both_Start_targets_no_spatial", [e for e in (start - spatial, spec["north"] + 8 - spatial) if e in support], [])
    check("flag_no_bare_or_spatial", [e for e in (anchor - spec["temporal"], anchor - spec["west_copy"], anchor - spatial) if e in support], [])
    for j in range(9):
        target = spec["north"] + j
        check("temporal_copy_" + str(j), parity_hits(target), [(spec["south"] + j, 1)])
        check("temporal_no_spatial_" + str(j), target - spatial in support, False)
    for j in range(8):
        target = spec["west"] + spec["west_copy"] + j
        check("spatial_copy_" + str(j), parity_hits(target), [(spec["west"] + j, 1)])
        check("spatial_source_" + str(j), target - spatial, spec["east"] + j)
        check("spatial_no_temporal_" + str(j), target in support, False)
    clause = sorted((e, c[e]) for e in support if c[e])
    adjacent = sorted((e, c[e + 1]) for e in support if c[e + 1])
    check("complete_zero_flag_clause", hits(center), clause)
    check("clause_and_predecessor_no_spatial", [e for e in (center - spatial, center - spatial - 1) if e in support], [])
    check("complete_sole_predecessor_with_south_bit8", hits(center - 1), sorted(adjacent + [(950, 1)]))
    first_reflected = min(center - e for e, value in enumerate(c) if value)
    check("first_reflection_is_even_label_band", first_reflected, 971)
    low_max = max(support - {anchor})
    check("sole_clause_bare_marker_source_absent", center - anchor in support, False)
    check("sole_predecessor_bare_marker_source", center - 1 - anchor, 950)
    check("unit_marker_product_above_clause", 2 * anchor > center, True)
    check("flag_coefficient_zero", c[anchor], 0)
    check("flag_physical_support_retained", anchor in support, True)
    padding = spec["padding"]
    predecessor_index = center + anchor - (padding - 1)
    check("complete_padding_predecessor", hits(padding - 1), [(anchor, c[predecessor_index])])
    check("padding_predecessor_coefficient_index", predecessor_index, 0)
    check("padding_predecessor_coefficient", c[predecessor_index], c[0])
    check("entire_zero_padding_band", [(e, hits(e)) for e in range(padding, spec["zero_end"] + 1) if hits(e)], [])
    check("padding_band_no_spatial", [e for e in range(padding, spec["zero_end"] + 1) if e - spatial in support], [])
    check("padding_all20_fields_covered", padding + 19 <= spec["zero_end"], True)
    maximum_product = max(dc) + max(support)
    check("complete_maximum_product", maximum_product, center + anchor)
    check("last_product_field", hits(maximum_product), [(anchor, c[0])])
    check("all_later_top_fields_zero", [(e, hits(e)) for e in range(maximum_product + 1, length) if hits(e)], [])
    check("at_least_one_zero_top_field", maximum_product + 1 < length, True)
    check("phase_reset_numerical", M + 3 + RHO // 2 + 29 < RHO, True)
    adjacent_selector = max(c[e + 1] for e in support if e < 942 and c[e + 1])
    adjacent_controls = sum(c[e + 1] for e in support if e >= 942 and c[e + 1])
    check("one_tile_adjacent_bound", adjacent_selector + adjacent_controls <= 2 * M - 1024, True)
    check("dummy_successor_label_weight", c[dummy + 1], 1024)
    check("all47_boolean_phases_stay_inside_one_field", all((1 << phase) < RHO for phase in range(47)), True)
    check("all46_nonzero_phases_even_before_clause_decode", all((1 << phase) % 2 == 0 for phase in range(1, 47)), True)
    check("sole_predecessor_reset", 2 * M + 30 < RHO, True)
    check("exact_sole_predecessor_reset", adjacent_selector + adjacent_controls + 1 + 29 < RHO, True)
    check("final_digit_reset", 7 * (M + 30) < RHO, True)
    delta_exponents = [max(dc) + dummy, spatial + dummy, dummy]
    check("three_safe_dummy_slack", all(length - (e + 1) >= 3 for e in delta_exponents) and RHO > 3, True)
    envelope = [0] * (maximum_product + 1)
    for e in support:
        for k, value in dc.items():
            envelope[e + k] += value
    max_boolean = max(envelope)
    check("global29_given_temporal_bound", max_boolean + 1 + RHO // 2 + 29 < 30 * RHO, True)
    return {"checks": checks, "failed_checks": [name for name, row in checks.items() if not row["pass"]],
            "first_reflected_exponent": first_reflected, "low_support_maximum": low_max,
            "unit_kernel_exponent": anchor, "unit_low_product_maximum": anchor + low_max,
            "unit_marker_product": 2 * anchor,
            "low_reflected_geometry": {"count": len(low_reflections), "sha256": sha(encoded(low_reflections)),
                                        "maximum": max(sum(term[2] for term in terms) for _, terms in low_reflections)},
            "clause_temporal_sources": clause_temporal_sources,
            "phase_targets": phase_targets,
            "phase_support_offsets": {"count": len(phase_offsets), "sha256": sha(encoded(phase_offsets))},
            "multiple_selector_exclusions": {"count": len(multiple_selectors),
                                             "sha256": sha(encoded(multiple_selectors)),
                                             "first": multiple_selectors[0], "last": multiple_selectors[-1]},
            "calibrated_tile941_exclusions": calibrated_exclusions,
            "phase_difference": anchor - start, "clause_center": center,
            "predecode_marker_offsets": {"count": len(marker_offsets), "sha256": sha(encoded(marker_offsets)), "first": marker_offsets[0], "last": marker_offsets[-1]}, "last_product_exponent": maximum_product,
            "padding_predecessor_coefficient_index": predecessor_index, "delta_exponents": delta_exponents,
            "one_tile_adjacent_bound": adjacent_selector + adjacent_controls,
            "boolean_convolution_maximum": max_boolean,
            "boolean_maximum_fields": [e for e, value in enumerate(envelope) if value == max_boolean]}


def constants(c, support, spec, length):
    power = lambda e: 1 << (47 * e)
    B, beta = power(length), power(length) - 1
    dc = sum(value * power(e) for e, value in dc_coefficients(c, spec).items())
    K = dc + B * power(spec["spatial"])
    MC = beta - sum(power(e) for e in support)
    core = sum(power(spec["north"] + j) for j in range(9))
    core += sum(power(spec["west"] + spec["west_copy"] + j) for j in range(8)) + power(spec["anchor"])
    p = spec["padding"]
    padding = (1 << 23) * power(p + 19) - power(p)
    positive_padding = (RHO - 1) * sum(power(e) for e in range(p, p + 19))
    positive_padding += ((1 << 23) - 1) * power(p + 19)
    require(padding == positive_padding and padding.bit_count() == 916, "Whole916-bit padding identity")
    native_core = 4 + (M - 2) * sum(power(e) for e in spec["centers"]) + core
    require(native_core.bit_count() == 62, "One43-bit clause plus19 core tests")
    native = native_core + padding
    require(0 < dc < B and 0 < MC < beta and 0 < native < beta, "Complete zero-flag scalar boxes")
    require(native.bit_count() == 978 and MC.bit_count() == 47 * length - 978, "Whole complementary populations")
    require(MC % 4 == 2 and native % 8 == 4, "Whole origin residues")
    return {"beta": beta, "K": K, "MC": MC, "MF_source": native + beta}


def modular(p, c, tiles, spec, length, whole):
    power = lambda e: pow(2, 47 * e, p)
    inverse = pow(power(1), -1, p)
    phi = 0
    for value in reversed(c):
        phi = (phi * inverse + value) % p
    kernel = power(spec["anchor"])
    bare = sum(power(e) for e in {spec["temporal"], spec["west_copy"]}) + kernel + power(length + spec["spatial"])
    dense = (bare + sum(power(center) for center in spec["centers"]) * phi) % p
    direct = bare
    for center in spec["centers"]:
        for j, (w, n, east, south) in enumerate(tiles):
            direct += (1 + 1024 * (1 + w + 256 * n + 131072 * east + 33554432 * south)) * power(center - j)
        for name, bits, count in (("south", 35, 9), ("west", 27, 8), ("north", 18, 9), ("east", 10, 8)):
            direct += sum((1 << (bits + j)) * power(center - spec[name] - j) for j in range(count))
        # No anchor term: its coefficient is zero although it stays physical.
    require(dense == direct % p == whole["K"] % p, "Three complete zero-flag K routes")
    B = power(length)
    return {"p": p, "B": B, "K": dense, "B_squared": B * B % p,
            "H": (1 + B * dense + B * B) % p}


def controller(parent, c, support, tiles, spec):
    minimum = max(max(spec["centers"]) + spec["anchor"] + 1, spec["padding"] + 20)
    length_trials = []
    for length in range(minimum, minimum + 201):
        primes = parent.factors(length)
        trial = {"length": length, "distinct_prime_factors": primes}
        length_trials.append(trial)
        require(all(parent.least_factor(p) is None for p in primes), "Exact elementary factorization")
        if length % 2 == 0 or 47 in primes or prod(primes) != length:
            trial["rejected_reason"] = "Length must be odd squarefree and coprime to47"
            continue
        whole = constants(c, support, spec, length)
        fixed = []
        for p in [47] + primes:
            row = modular(p, c, tiles, spec, length, whole)
            row["base2_order"], row["B_order"] = parent.order(2, p), parent.order(row["B"], p)
            fixed.append(row)
        trial["fixed"] = fixed
        d = 47 * length
        if any(row["H"] == 0 or row["B_squared"] == 1 or gcd(d, row["B_order"]["order"]) != 1 for row in fixed):
            trial["rejected_reason"] = "Fixed controller condition fails"
            continue
        spacing = lcm(*(row["B_order"]["order"] for row in fixed))
        require(gcd(spacing, d) == 1, "Whole new spacing coprime to d")
        auxiliary_trials = []
        for j in range((d - 1) // spacing + 1, (d - 1) // spacing + 502):
            p = spacing * j + 1
            divisor = parent.least_factor(p)
            row = {"candidate": p, "multiplier": j, "least_factor": divisor}
            auxiliary_trials.append(row)
            if divisor is not None:
                continue
            row.update(modular(p, c, tiles, spec, length, whole))
            lift = pow(2, d * (p - 1), p * p)
            require(lift % p == 1, "Fermat lift")
            row["lift_residue"], row["lift_quotient"] = lift, (lift - 1) // p
            if row["B_squared"] != 1 and row["H"] != 0 and row["lift_quotient"]:
                require(p > d and p % 2 == 1, "Odd auxiliary prime above d")
                return {"L": length, "d": d, "length_trials": length_trials, "fixed": fixed,
                        "spacing": spacing, "auxiliary_trials": auxiliary_trials, "selected_lambda": p}, whole
        trial["rejected_reason"] = "No auxiliary prime in501 specified progression candidates"
    raise ValueError("No complete controller in201 specified field lengths")



def actual_mask_rank_checks(whole, spec, length):
    """Finite whole-word controls for the changed dummy/origin populations."""
    B = 1 << (47 * length)
    beta = B - 1
    MC, native = whole["MC"], whole["MF_source"] - beta
    dummy = 1 << (47 * spec["dummy"])
    acceptance = [(value * dummy & (MC + 1)) == 0 for value in range(4)]
    require(acceptance == [True, True, False, False], "Actual mask accepts exactly Boolean dummy digits")
    require((1 << 47) & (MC + 1) == 0, "New selector1 is allowed; it represents old selector2")
    require((MC >> (47 * spec["dummy"])) & (RHO - 1) == RHO - 2,
            "Dummy field clears exactly its low bit")
    rows = []
    for cells in (1, 2, 3):
        q, t = B ** cells, 47 * length * cells
        J = (q - 1) // beta
        low, high = MC * J + 1, native * J - 1
        require(low.bit_count() == (47 * length - 978) * cells + 1
                and high.bit_count() == 978 * cells + 1,
                "Actual shifted-origin mask populations")
        for toggle_all in (False, True):
            C = 1 + (dummy * J if toggle_all else 0)
            F = 8
            require(0 < C and 0 < F and C + F < q
                    and (C - 1) & low == 0 and F & high == 0,
                    "Whole actual mask-compatible rank sample")
            S = (C - 1) + q * F
            T = low + q * high
            big = q * q
            R = (q * (q - F) - C) * (q * q - 1) + (MC + q * whole["MF_source"]) * J
            require(T.bit_count() == t + 2 and S & T == 0
                    and R == (big - S) * (big - 1) + T
                    and R == (big - 1 - S) * big + (S + T)
                    and R.bit_count() == 3 * t + 2 and R % 4 == 3,
                    "Actual whole-word rank identities and populations")
            rows.append({"cells": cells, "all_dummy_bits_on": toggle_all,
                         "low_population": low.bit_count(), "high_population": high.bit_count(),
                         "mask_population": T.bit_count(), "rank_population": R.bit_count(), "rank_mod4": R % 4})
    return {"dummy0to3_accepted": acceptance, "samples": rows,
            "scope": "Whole-word finite checks of the new masks and universal rank algebra, not canonical tilings."}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    parent, seed, actions, tiles, original = parent_model()
    start_complemented = [255 - tiles[0][0], 511 - tiles[0][1], 255 - tiles[0][2], 511 - tiles[0][3]]
    require(start_complemented == [253, 76, 252, 510], "Exact retained Start selector0 calibration")
    require(all((start_complemented[3] >> j) & 1 for j in range(1, 9)), "All eight calibrated Start south bits are one")
    require(list(tiles[941]) == [4, 437, 2, 437], "Entire calibrated oldtile942/newtile941")
    # Marker1004 admits a local offset19 pattern; this is not a full native witness.
    tile4 = [255 - tiles[3][0], 511 - tiles[3][1], 255 - tiles[3][2], 511 - tiles[3][3]]
    require(tile4 == [255, 507, 247, 511], "Full oldtile4/newtile3 local-negative calibration")
    negative_signature = [int(941 == 3)] + [(tile4[3] >> j) & 1 for j in range(8)] + [(tile4[2] >> 7) & 1]
    expected_signature = [(start_complemented[3] >> j) & 1 for j in range(9)] + [1]
    require(negative_signature == expected_signature, "Marker1004 offset19 matches all local Start tests")
    variants, coefficients = {}, {}
    for name, spec in SPECS.items():
        c, support = model(original, spec)
        require(c[:942] == [1 + 1024 * (1 + w + 256 * n + 131072 * east + 33554432 * south)
                            for w, n, east, south in tiles],
                "Every one of942 new coefficients equals its exact admissible decoded tile")
        require(spec["temporal"] == spec["west_copy"] == 18, "One shared copy exponent")
        require(sorted(e for e, value in dc_coefficients(c, spec).items() if value == 1) == [18, 1005],
                "Exactly two bare unit monomials, not a double-weight shared term")
        controllers, whole = controller(parent, c, support, tiles, spec)
        geometric = geometry(c, support, spec, controllers["L"], tiles)
        require(not geometric["failed_checks"], name + " geometry failed: " + repr(geometric["failed_checks"]))
        require(controllers["L"] == 2983 and controllers["d"] == 140201
                and controllers["spacing"] == 10764 and controllers["selected_lambda"] == 150697,
                "Exact complete squarefree-clause controller")
        require([row["base2_order"]["order"] for row in controllers["fixed"]] == [23, 18, 52]
                and [row["B_order"]["order"] for row in controllers["fixed"]] == [23, 18, 52],
                "Exact base2 and B orders")
        require(geometric["predecode_marker_offsets"]["count"] == 978
                and geometric["predecode_marker_offsets"]["first"] == 0
                and geometric["predecode_marker_offsets"]["last"] == 1005,
                "All physical coarse offsets certified before one-hot decoding")
        require(geometric["phase_support_offsets"]["count"] == 934
                and geometric["multiple_selector_exclusions"]["count"] == 932
                and len(geometric["calibrated_tile941_exclusions"]) == 1,
                "Complete934-offset phase partition")
        # Enumerate every selector count and incoming carry with Boolean temporal tau.
        count_survivors = [(n, k, tau) for n in range(943) for k in range(30) for tau in (0, 1)
                           if (n + k + tau) & 1022 == 0]
        require(count_survivors == [(0, 0, 0), (0, 0, 1), (0, 1, 0), (1, 0, 0)]
                and 942 + 29 + 1 < 1024,
                "All n/k/tau low-count survivors; occupied cases force both incoming quantities zero")
        premature = {**spec, "centers": [1955]}
        premature_dc = {1955 - e: value for e, value in enumerate(c) if value}
        for exponent in (18, 1005):
            premature_dc[exponent] = premature_dc.get(exponent, 0) + 1
        premature_hits = sorted((e, premature_dc[1955 - e]) for e in support if 1955 - e in premature_dc)
        required_clause = {e: c[e] for e in support if c[e]}
        required_clause[950] += 1
        require(premature_hits == sorted(required_clause.items())
                and (start_complemented[3] >> 8) & 1 == 1
                and (M + 2) & (M - 2) != 0,
                "Center1955 adds the forced Start south-bit8 and violates its actual clause mask")
        mask_rank = actual_mask_rank_checks(whole, spec, controllers["L"])
        ports = {}
        for port, value in whole.items():
            raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
            ports[port] = {"bits": value.bit_length(), "bytes": len(raw), "sha256": sha(raw)}
        variants[name] = {"specification": spec, "geometry": geometric, "controller": controllers, "actual_mask_rank_checks": mask_rank,
                          "physical_positions": len(support), "nonzero_coefficients": sum(bool(v) for v in c),
                          "coefficient_sum": sum(c), "coefficient_maximum": max(c), "native_core_population": 62,
                          "padding_population": 916, "native_population": 978,
                          "all3297_coefficients_sha256": sha(encoded(c)), "constant_ports": ports,
                          "raw_bytes": sum(row["bytes"] for row in ports.values())}
        require(variants[name]["raw_bytes"] == 70157, "Exact whole four-port raw cost")
        variants[name]["boolean_tau_count"] = {"tested_triples": 943 * 30 * 2, "survivors": count_survivors}
        variants[name]["center1955_negative_control"] = {
            "extra_local_term": [950, 1], "Start_south_bit8": 1,
            "occupied_clause_value": M + 2, "forbidden_mask_intersection": (M + 2) & (M - 2),
            "scope": "Exact canonical forced-Start clause obstruction at center1955, not a global impossibility result."}
        coefficients[name] = c
    data = {"schema": "squarefree_clause_exploration_v1", "script_sha256": sha(Path(__file__).read_bytes()),
            "parent_verifier_sha256": PARENT_SHA, "inherited_source_page_sha256": parent.PAGE_SHA,
            "inherited_decoder_sha256": parent.DECODER_SHA, "inherited_proof_sha256": parent.PROOF_SHA,
            "seed_sha256": sha(seed.encode()), "actions_sha256": sha(encoded(actions)),
            "tiles_sha256": sha(encoded(tiles)), "admissible_old_indices": [0] + list(range(2, 943)), "Start_complemented": start_complemented, "variants": variants,
            "marker1004_negative_control": {
                "offset": 19, "selected_tile": 3, "complemented_tile": tile4,
                "test_targets": list(range(960, 969)) + [1004],
                "temporal_preimages": list(range(941, 950)) + [985],
                "actual_signature": negative_signature, "required_Start_signature": expected_signature,
                "scope": "Exact compatible local phase-test pattern; no complete native witness or polynomial zero is claimed."},
            "scope": "Isolated complete finite squarefree-length parity-clause admissible942 model and proof lead; every prime divisor47,19,157 of d has a complete controller certificate; low reflected contributions are even and the sole temporal Boolean digit is absorbed by the count lemma. All eight Start south-one tests exclude nonzero phases by multiple selectors or the complete decoded oldtile942/newtile941 calibration. No complete ordinary proof, accepted-source change, formal replay or promotion is claimed."}
    for filename, raw in (("RESULTS.json", encoded(data)), ("COEFFICIENTS.json", encoded(coefficients))):
        if args.write:
            (HERE / filename).write_bytes(raw)
        else:
            require((HERE / filename).read_bytes() == raw, "Deterministic artifact differs: " + filename)
    print(json.dumps({"status": "PASS", "variants": {name: {
        "L": item["controller"]["L"], "lambda": item["controller"]["selected_lambda"],
        "raw_bytes": item["raw_bytes"], "H": [row["H"] for row in item["controller"]["fixed"]]
                + [item["controller"]["auxiliary_trials"][-1]["H"]]}
        for name, item in variants.items()}, "script_sha256": data["script_sha256"],
        "results_sha256": sha(encoded(data))}, sort_keys=True))


if __name__ == "__main__":
    main()
