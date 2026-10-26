#!/usr/bin/env python3
"""Complete finite reversed-selector probe with doubled clauses and bit3 padding."""
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
BASE_PHI_SHA = "626c3a671efc045c6127991a2e636c7db64a9afb146a3402c6e6322e1fa9854f"
RHO, M, BASE_M = 1 << 47, 1 << 45, 1 << 44
SPECS = {
    "local1005": {"south": 942, "west": 969, "north": 960, "east": 978,
                  "dummy": 977, "anchor": 1005, "temporal": 18, "west_copy": 18,
                  "spatial": 9, "centers": [1516], "padding": 1, "padding_last": 916, "zero_tail": 2522},
    "global1004": {"south": 942, "west": 969, "north": 960, "east": 978,
                  "dummy": 977, "anchor": 1004, "temporal": 18, "west_copy": 18,
                  "spatial": 9, "centers": [1515], "padding": 1, "padding_last": 916, "zero_tail": 2520},
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
    mapping = [0] + list(range(942, 1, -1))
    require(len(mapping) == 942 and set(mapping) == set(range(943)) - {1},
            "Full bijection onto exactly the old admissible selectors")
    selected = [tiles[j] for j in mapping]
    require(len(set(tuple(t) for t in selected)) == 942, "All admissible decoded tile identities remain distinct")
    require(list(selected[14]) == [3, 436, 4, 4], "Reversed physical initializer14")
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
    require(sum(c) == sum(original) - 3 * BASE_M - original[1] and sum(c[942:]) == BASE_M - 1024 and max(c) < BASE_M,
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
    require(sha(encoded(c)) == BASE_PHI_SHA,
            "Entire basePhi equals the frozen2963 coefficient array before scaling")
    c[1:942] = reversed(c[1:942])
    scaled = [2 * value for value in c]
    require(all(value % 2 == 0 for value in scaled) and max(scaled) < M
            and sum(scaled[942:]) == M - 2048,
            "Every complete clause coefficient doubled, with the same physical support")
    return scaled, support


def dc_coefficients(c, spec):
    dc = {}
    for center in spec["centers"]:
        for e, value in enumerate(c):
            if value:
                require(center - e not in dc, "All reflected coefficient residues disjoint")
                dc[center - e] = value
    for e in sorted({spec["temporal"], spec["west_copy"], spec["anchor"]}):
        dc[e] = dc.get(e, 0) + 1
    require(all(value < RHO for value in dc.values()), "Every actual kernel coefficient including collisions is belowrho")
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
    multiple_selectors, calibrated_exclusions, global_exclusions, unresolved = [], [], [], []
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
        elif r == 19:
            require([target - r for target in range(spec["north"], spec["north"] + 9)]
                    == [941] + list(range(942, 950)), "Exact whole9-bit global offset19 preimages")
            global_exclusions.append({"offset": r, "method": "Complete512-state South-label ranking"})
        else:
            unresolved.append((r, preimages))
    check("zero_phase_is_a_support_candidate", 0 in phase_offsets, True)
    check("all_nonzero_offsets_excluded", unresolved, [])
    check("exact_calibrated_tile941_south", last_tile_south, 510)
    check("unique_calibrated_exception_offset", [row["offset"] for row in calibrated_exclusions], [spec["temporal"] + 2])
    check("all_support_offsets_within_no_wrap_bounds", all(0 <= r <= start for r in phase_offsets), True)
    check("every_nonzero_offset_at_least_anchor_minus_lowmax", all(r >= anchor - max(support - {anchor}) for r in phase_offsets if r), True)
    check("all_offsets_classified", len(phase_offsets), 1 + len(multiple_selectors) + len(calibrated_exclusions) + len(global_exclusions))
    # This entire coarse argument precedes any one-hot/clause decoding.
    # The even low reflection and Boolean temporal digits force phase zero.
    low_reflections = []
    for target in range(anchor):
        terms = [(e, center - target + e, c[center - target + e]) for e in support
                 if 0 <= center - target + e < len(c) and c[center - target + e]]
        require(all(index >= 512 and value % 2 == 0 for _, index, value in terms),
                "Every reset-band reflected coefficient is even and in the entire reversed tail512..985")
        require(sum(value for _, _, value in terms) <= sum(c[512:]),
                "Entire low reflected envelope bounded before any count decoding")
        low_reflections.append((target, terms))
    check("all_reset_band_reflections_even_and_tail_only", len(low_reflections), anchor)
    check("low_reset_unconditional_bound", sum(c[512:]) + 3 + RHO // 2 + 57 < RHO, True)
    check("marker_reflected_coefficients_even", all(value % 2 == 0
          for e, value in hits(anchor) if e != 0), True)
    check("actual_marker_coefficient_collision", dc[anchor], c[center - anchor] + 1)
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
    clause = {e: c[e] for e in support if c[e]}
    bare_clause_source = center - anchor
    clause[bare_clause_source] = clause.get(bare_clause_source, 0) + 1
    adjacent = {e: c[e + 1] for e in support if c[e + 1]}
    bare_predecessor_source = center - 1 - anchor
    adjacent[bare_predecessor_source] = adjacent.get(bare_predecessor_source, 0) + 1
    check("complete_scaled_clause_with_boolean_extra", hits(center), sorted(clause.items()))
    check("clause_and_predecessor_no_spatial", [e for e in (center - spatial, center - spatial - 1) if e in support], [])
    check("complete_predecessor_with_boolean_extra", hits(center - 1), sorted(adjacent.items()))
    check("exact_extra_clause_source", bare_clause_source, 511)
    check("exact_extra_predecessor_source", bare_predecessor_source, 510)
    first_reflected = min(center - e for e, value in enumerate(c) if value)
    check("first_reflection_is_even_label_band", first_reflected, center - 985)
    low_max = max(support - {anchor})
    check("unit_marker_product_above_clause", 2 * anchor > center, True)
    check("flag_coefficient_zero", c[anchor], 0)
    check("flag_physical_support_retained", anchor in support, True)
    padding_rows = []
    for target in range(spec["padding"], spec["padding_last"] + 1):
        local = hits(target)
        reflected = [(e, c[center - target + e]) for e in support
                     if 0 <= center - target + e < len(c) and c[center - target + e]]
        units = [(target - 18, 1)] if target - 18 in support else []
        require(local == sorted(reflected + units), "Every complete low-padding local coefficient array: " + str(target))
        require(all(0 <= e < 942 and value % 2048 in (0, 2) for e, value in reflected),
                "Every padding reflection has selector input and residue0 or2")
        spatial_source = target - spatial in support
        temporal_source = target in support
        maximum = max((value % 2048 for _, value in reflected), default=0) + len(units) + int(spatial_source) + int(temporal_source)
        require(maximum <= 5 and all((value & 8) == 0 for value in range(maximum + 1)),
                "With at most one selector, every aligned padding low residue avoids tested bit3")
        padding_rows.append((target, reflected, units, spatial_source, temporal_source, maximum))
    check("whole916_uniform_padding_fields", len(padding_rows), 916)
    check("padding_band_below_copy_tests", spec["padding_last"] < spec["north"], True)
    maximum_product = max(dc) + max(support)
    check("complete_maximum_product", maximum_product, center + anchor)
    check("exact_zero_tail_start", spec["zero_tail"], maximum_product + 1)
    check("all_safe_dummy_outputs_above_padding", min(min(dc) + dummy, spatial + dummy, dummy) > spec["padding_last"], True)
    check("last_product_field", hits(maximum_product), [(anchor, c[0])])
    check("all_later_top_fields_zero", [(e, hits(e)) for e in range(maximum_product + 1, length) if hits(e)], [])
    check("at_least_one_zero_top_field", maximum_product + 1 < length, True)
    check("phase_reset_numerical", sum(c[512:]) + 3 + RHO // 2 + 57 < RHO, True)
    adjacent_selector = max(c[e + 1] for e in support if e < 942 and c[e + 1])
    adjacent_controls = sum(c[e + 1] for e in support if e >= 942 and c[e + 1])
    check("one_tile_adjacent_bound", adjacent_selector + adjacent_controls <= 2 * M - 2048, True)
    check("dummy_successor_label_weight", c[dummy + 1], 2048)
    check("all47_boolean_phases_stay_inside_one_field", all((1 << phase) < RHO for phase in range(47)), True)
    check("all46_nonzero_phases_even_before_clause_decode", all((1 << phase) % 2 == 0 for phase in range(1, 47)), True)
    check("sole_predecessor_reset", 2 * M + 58 < RHO, True)
    check("exact_sole_predecessor_reset", adjacent_selector + adjacent_controls + 1 + 57 < RHO, True)
    check("final_digit_reset", M + 57 < RHO, True)
    delta_exponents = [max(dc) + dummy, spatial + dummy, dummy]
    check("three_safe_dummy_slack", all(length - (e + 1) >= 3 for e in delta_exponents) and RHO > 3, True)
    envelope = [0] * (maximum_product + 1)
    for e in support:
        for k, value in dc.items():
            envelope[e + k] += value
    max_boolean = max(envelope)
    check("global57_given_temporal_bound", max_boolean + 1 + RHO // 2 + 57 < 58 * RHO, True)
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
            "global_offset19_exclusions": global_exclusions,
            "phase_difference": anchor - start, "clause_center": center,
            "predecode_marker_offsets": {"count": len(marker_offsets), "sha256": sha(encoded(marker_offsets)), "first": marker_offsets[0], "last": marker_offsets[-1]}, "last_product_exponent": maximum_product,
            "low_padding_geometry": {"count": len(padding_rows), "sha256": sha(encoded(padding_rows)),
                                     "minimum": min(row[-1] for row in padding_rows),
                                     "maximum": max(row[-1] for row in padding_rows)},
            "delta_exponents": delta_exponents,
            "one_tile_adjacent_bound": adjacent_selector + adjacent_controls,
            "boolean_convolution_maximum": max_boolean,
            "boolean_maximum_fields": [e for e, value in enumerate(envelope) if value == max_boolean]}


def constants(c, support, spec, length):
    power = lambda e: 1 << (47 * e)
    B, beta = power(length), power(length) - 1
    dc = sum(value * power(e) for e, value in dc_coefficients(c, spec).items())
    base_reflection = sum((value // 2) * power(center - e)
                          for center in spec["centers"] for e, value in enumerate(c) if value)
    require(dc == power(18) + power(spec["anchor"]) + 2 * base_reflection,
            "Whole DC equals printed factor2 times the unscaled Phi reciprocal recipe")
    K = dc + B * power(spec["spatial"])
    MC = beta - sum(power(e) for e in support)
    require(MC == beta - sum(power(e) for e in range(951))
            - power(960) * sum(power(e) for e in range(26)) - power(spec["anchor"]),
            "Whole printed block-MC recipe independently preserves physical support")
    core = sum(power(spec["north"] + j) for j in range(9))
    core += sum(power(spec["west"] + spec["west_copy"] + j) for j in range(8)) + power(spec["anchor"])
    p = spec["padding"]
    padding = 8 * sum(power(e) for e in range(p, spec["padding_last"] + 1))
    require(p == 1 and spec["padding_last"] == 916 and padding.bit_count() == 916
            and (4 + padding).bit_count() == 917 and padding % RHO == 0
            and 4 + padding == 8 * sum(power(e) for e in range(917)) - 4,
            "Whole916-bit bit3 padding and exact merged origin8G917-4")
    native_core = 4 + (M - 4) * sum(power(e) for e in spec["centers"]) + core
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
    base_phi = 0
    for value in reversed(c):
        require(value % 2 == 0, "Every scaled coefficient has an integral basePhi half")
        base_phi = (base_phi * inverse + value // 2) % p
    printed = (bare + 2 * sum(power(center) for center in spec["centers"]) * base_phi) % p
    require(dense == printed, "Printed single-factor2 basePhi route agrees with scaled dense polynomial")
    direct = bare
    for center in spec["centers"]:
        for j, (w, n, east, south) in enumerate(tiles):
            direct += (2 + 2048 * (1 + w + 256 * n + 131072 * east + 33554432 * south)) * power(center - j)
        for name, bits, count in (("south", 35, 9), ("west", 27, 8), ("north", 18, 9), ("east", 10, 8)):
            direct += sum((1 << (bits + j + 1)) * power(center - spec[name] - j) for j in range(count))
        # No anchor term: its coefficient is zero although it stays physical.
    require(dense == direct % p == whole["K"] % p, "Printed basePhi, scaled dense, direct decoded and whole-integer K routes")
    B = power(length)
    return {"p": p, "B": B, "K": dense, "B_squared": B * B % p,
            "H": (1 + B * dense + B * B) % p}


def controller(parent, c, support, tiles, spec):
    minimum = max(spec["centers"]) + spec["anchor"] + 2
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


def global_phase_graph(tiles):
    """Recompute the whole offset19 South transition graph from all942 tiles."""
    require(list(tiles[941]) == [0, 2, 7, 1] and 511 - tiles[0][3] == 510,
            "Exact exceptional tile and forced Start calibration")
    preimages = [target - 19 for target in range(960, 969)]
    require(preimages == [941] + list(range(942, 950)), "All nine same-cell offset19 preimages")
    cases = []
    graph = {south: {2 * south % 512} for south in range(512)}
    graph[510].add(509)
    for south in range(512):
        for epsilon in ((0, 1) if south == 510 else (0,)):
            bits = [epsilon] + [(south >> j) & 1 for j in range(8)]
            current = sum(bit << j for j, bit in enumerate(bits))
            require(current == (2 * south + epsilon) % 512 and current in graph[south],
                    "Complete9-bit transition formula")
            cases.append((south, epsilon, current))
    ranks, active = {0: 0}, set()

    def rank(south):
        if south in ranks:
            return ranks[south]
        require(south not in active, "No directed cycle outside zero")
        active.add(south)
        ranks[south] = 1 + max(rank(target) for target in graph[south])
        active.remove(south)
        return ranks[south]

    for south in range(512):
        rank(south)
    require(len(cases) == 513 and len(ranks) == 512 and max(ranks.values()) == 11
            and graph[0] == {0}, "Entire calibrated graph and bounded ranking")
    require(all(ranks[target] < ranks[south] for south in range(1, 512) for target in graph[south]),
            "Every nonzero edge strictly decreases the recorded rank")
    transitions = [(None, 0, 0, 0)]
    for j, tile in enumerate(tiles):
        south, epsilon = 511 - tile[3], int(j == 941)
        current = (2 * south + epsilon) % 512
        require(current in graph[south] and (epsilon == 0 or south == 510),
                "Every942 decoded tile transition belongs to the graph")
        transitions.append((j, south, epsilon, current))
    require(len(transitions) == 943, "Full admissible tile language and empty state")
    require(any(511 - tile[3] == 511 for tile in tiles) and 2 * 511 % 512 == 510,
            "A compatible local Start pattern exists but lies on no finite nonzero cycle")
    require((2 * 511 + 1) % 512 == 511 and 511 != 510,
            "Removing exact exceptional-tile calibration would permit a nonzero cycle")
    return {"offset": 19, "preimages": preimages,
            "formula": "S_current=(2*S_temporal+I(tile_temporal=941)) mod512",
            "bit_cases": {"count": len(cases), "sha256": sha(encoded(cases))},
            "native_transitions": {"count": len(transitions), "sha256": sha(encoded(transitions))},
            "graph": [{"south": south, "successors": sorted(graph[south]), "rank": ranks[south]}
                      for south in range(512)],
            "largest_rank": 11, "only_directed_cycle": [0], "forced_Start_south": 510,
            "calibration_deletion_negative": {"false_exception_south": 511, "false_self_loop": 511},
            "consequence": "Every cell of a finite temporal permutation lies on a closed walk. Strict rank descent outside0 forces all South labels0, contradicting Start510."}



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    parent, seed, actions, tiles, original = parent_model()
    require([255 - tiles[0][0], 511 - tiles[0][1], 255 - tiles[0][2], 511 - tiles[0][3]]
            == [253, 76, 252, 510], "Whole unchanged Start0 calibration")
    require(list(tiles[941]) == [0, 2, 7, 1] and list(tiles[14]) == [3, 436, 4, 4],
            "Reversed exact terminal selector and initializer")
    graph = global_phase_graph(tiles)
    variants, arrays = {}, {}
    expected = {
        "local1005": {"L": 2531, "d": 118957, "orders": [23, 2530],
                      "order_factors": [[23], [2, 5, 11, 23]], "spacing": 2530,
                      "lambda": 121441, "lift": 54285, "raw_bytes": 59533,
                      "fine_offsets": 934, "global_offsets": []},
        "global1004": {"L": 2521, "d": 118487, "orders": [23, 1260],
                       "order_factors": [[23], [2, 3, 5, 7]], "spacing": 28980,
                       "lambda": 231841, "lift": 83367, "raw_bytes": 59297,
                       "fine_offsets": 935, "global_offsets": [19]},
    }
    for name, spec in SPECS.items():
        exp = expected[name]
        c, support = model(original, spec)
        require(c[:942] == [2 + 2048 * (1 + w + 256 * n + 131072 * east + 33554432 * south)
                            for w, n, east, south in tiles], "Every doubled reordered decoded coefficient")
        require(support == set(range(951)) | set(range(960, 986)) | {spec["anchor"]},
                "Full physical support independent of tile reindexing")
        require(sum(c[512:]) == 57463969448796 and sum(c[511:]) + RHO // 2 >= RHO,
                "Exact successful high-tail envelope and adjacent-center failure of the same bound")
        dc = dc_coefficients(c, spec)
        require(sorted(e for e, value in dc.items() if value == 1) == [18]
                and dc[spec["anchor"]] == c[511] + 1,
                "Exact marker/selector511 kernel collision")
        ctl, whole = controller(parent, c, support, tiles, spec)
        length, d, fixed = ctl["L"], ctl["d"], ctl["fixed"]
        require(length == exp["L"] and d == exp["d"] == 47 * length
                and parent.least_factor(length) is None and length != 47,
                "Exact new prime length and complete squarefree d")
        require([row["p"] for row in fixed] == [47, length]
                and [row["base2_order"]["order"] for row in fixed] == exp["orders"]
                and [row["B_order"]["order"] for row in fixed] == exp["orders"]
                and [row["base2_order"]["prime_factors"] for row in fixed] == exp["order_factors"]
                and all(parent.least_factor(p) is None for factors in exp["order_factors"] for p in factors),
                "All exact fixed orders, proper-order tests and factor primalities")
        require(all(gcd(d, row["B_order"]["order"]) == 1 and row["H"] != 0
                    and row["B_squared"] != 1 for row in fixed)
                and ctl["spacing"] == exp["spacing"] and gcd(d, ctl["spacing"]) == 1,
                "Complete fixed controller units and spacing")
        auxiliary = ctl["auxiliary_trials"][-1]
        require(ctl["selected_lambda"] == auxiliary["p"] == exp["lambda"] > d
                and parent.least_factor(auxiliary["p"]) is None
                and (auxiliary["p"] - 1) % exp["spacing"] == 0
                and auxiliary["B_squared"] != 1 and auxiliary["H"] != 0
                and 0 < auxiliary["lift_quotient"] == exp["lift"] < auxiliary["p"],
                "Whole auxiliary prime, H unit and exact valuation1")
        geo = geometry(c, support, spec, length, tiles)
        require(not geo["failed_checks"], name + " geometry failed: " + repr(geo["failed_checks"]))
        require(geo["phase_support_offsets"]["count"] == exp["fine_offsets"]
                and geo["multiple_selector_exclusions"]["count"] == 932
                and [row["offset"] for row in geo["calibrated_tile941_exclusions"]] == [20]
                and [row["offset"] for row in geo["global_offset19_exclusions"]] == exp["global_offsets"],
                "Complete fine phase partition, using the recalibrated graph when needed")
        require(geo["predecode_marker_offsets"]["count"] == 978
                and geo["predecode_marker_offsets"]["first"] == 0
                and geo["predecode_marker_offsets"]["last"] == spec["anchor"]
                and geo["low_reflected_geometry"]["count"] == spec["anchor"]
                and geo["low_reflected_geometry"]["maximum"] == sum(c[512:]),
                "All coarse offsets and every unconditional low-reset coefficient array")
        require(geo["low_padding_geometry"]["count"] == 916
                and geo["low_padding_geometry"]["maximum"] == 5
                and len(geo["clause_temporal_sources"]) == 467,
                "Complete overlapping bit3 padding and all Boolean clause temporal sources")
        count_survivors = [(n, k, tau, bare) for n in range(943) for k in range(58)
                           for tau in (0, 1) for bare in (0, 1)
                           if (2 * n + k + tau + bare) & 2044 == 0]
        require(len(count_survivors) == 16 and max(row[0] for row in count_survivors) == 1
                and all(2 * n + k + tau + bare <= 3 for n, k, tau, bare in count_survivors)
                and 2 * 942 + 57 + 1 + 1 < 2048, "Complete doubled count lemma")
        require(all((M + 2 + bare) & (M - 4) == 0 for bare in (0, 1)),
                "Both occupied canonical clause values pass")
        rank = actual_mask_rank_checks(whole, spec, length)
        ports = {}
        for port, value in whole.items():
            raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
            ports[port] = {"bits": value.bit_length(), "bytes": len(raw), "sha256": sha(raw)}
        raw_bytes = sum(row["bytes"] for row in ports.values())
        require(raw_bytes == exp["raw_bytes"], "Exact whole four-port byte cost")
        premature_dc = dc_coefficients(c, {**spec, "centers": [spec["centers"][0] - 1]})
        premature_raw = sum(value for exponent, value in premature_dc.items()
                           if spec["anchor"] - 1 - exponent in support)
        require(premature_raw + 1 + RHO // 2 + 57 >= RHO,
                "One smaller center fails this unconditional reset bound")
        require(4 <= 5 and 4 & 4 and not 4 & 8,
                "Retaining bit2 padding is not justified by the complete local residue envelope")
        variants[name] = {"specification": spec, "geometry": geo, "controller": ctl,
                          "constant_ports": ports, "raw_bytes": raw_bytes,
                          "scaled_coefficients_sha256": sha(encoded(c)),
                          "base_Phi_coefficients_sha256": sha(encoded([v // 2 for v in c])),
                          "actual_mask_rank_checks": rank,
                          "count_lemma": {"tested_quadruples": 943 * 58 * 2 * 2, "survivors": count_survivors},
                          "native_population": 978, "physical_population": 978,
                          "native_core_population": 62, "padding_population": 916,
                          "native_origin_padding_identity": "4+8*rho*G916(rho)=8*G917(rho)-4",
                          "reset_bound_negative": {"center": spec["centers"][0] - 1,
                              "field": spec["anchor"] - 1, "raw": premature_raw,
                              "scope": "Failure of the same unconditional local envelope, not a complete native counterexample or minimality claim."},
                          "bit2_padding_negative": {"allowed_residue": 4, "bit2_overlap": 4, "bit3_overlap": 0,
                              "scope": "Failure of a uniform local residue-envelope argument for bit2, not a complete native counterexample."}}
        arrays[name] = c
    require(arrays["local1005"] == arrays["global1004"], "Both variants use the same entire reversed Phi")
    data = {"schema": "reversed_admissible_selectors_finite_probe_v1",
            "script_sha256": sha(Path(__file__).read_bytes()), "parent_verifier_sha256": PARENT_SHA,
            "source_page_sha256": parent.PAGE_SHA, "decoder_sha256": parent.DECODER_SHA,
            "parent_proof_sha256": parent.PROOF_SHA, "unreversed_base_Phi_sha256": BASE_PHI_SHA,
            "seed_sha256": sha(seed.encode()), "actions_sha256": sha(encoded(actions)),
            "tiles_sha256": sha(encoded(tiles)), "old_indices": [0] + list(range(942, 1, -1)),
            "reindexing": "New physical0=old0; newphysicalj=old(943-j),1<=j<=941; precisely old1 omitted.",
            "initializer_physical_index": 14, "terminal_physical941": tiles[941],
            "global_offset19_graph": graph, "variants": variants,
            "scope": "Complete finite two-variant probe, with all physical/coefficient arrays, full carry envelopes, overlapping bit3 padding, recalibrated phase exclusions and full controllers. A new complete ordinary native/Pell proof and accepted-source promotion remain separate obligations."}
    for filename, raw in (("RESULTS.json", encoded(data)), ("COEFFICIENTS.json", encoded(arrays["local1005"]))):
        if args.write:
            (HERE / filename).write_bytes(raw)
        else:
            require((HERE / filename).read_bytes() == raw, "Deterministic artifact differs: " + filename)
    print(json.dumps({"status": "PASS", "script_sha256": data["script_sha256"],
                      "results_sha256": sha(encoded(data)), "variants": {name: {
                          "L": row["controller"]["L"], "raw_bytes": row["raw_bytes"],
                          "lambda": row["controller"]["selected_lambda"],
                          "H": [x["H"] for x in row["controller"]["fixed"]]
                               + [row["controller"]["auxiliary_trials"][-1]["H"]]}
                          for name, row in variants.items()}}, sort_keys=True))


if __name__ == "__main__":
    main()
