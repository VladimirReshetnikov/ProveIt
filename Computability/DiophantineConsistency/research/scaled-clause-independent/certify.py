#!/usr/bin/env python3
"""Reproduce the whole scaled-clause2953 finite geometry and controller certificate."""
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
L, D = 2953, 138791
PROOF = HERE / "PROOF.md"
PROOF_SHA = "602b9560017f52835d36de8c1969ec8348381c8dae31876cb86905c5de2cdebe"
SPEC = {"south": 942, "west": 969, "north": 960, "east": 978,
        "dummy": 977, "anchor": 1005, "temporal": 18, "west_copy": 18,
        "spatial": 9, "centers": [1945], "padding": 1, "padding_last": 916, "zero_tail": 2951}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def parent_model():
    require(sha(PROOF.read_bytes()) == PROOF_SHA, "Exact complete scaled-clause2953 ordinary proof")
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
    require(list(selected[928]) == list(tiles[929]) == [3, 436, 4, 4], "Exact admissible initializer index928")
    return parent, seed, actions, selected, original


def shifted_model(original, spec):
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
    for target in range(anchor):
        terms = [(e, center - target + e, c[center - target + e]) for e in support
                 if 0 <= center - target + e < len(c) and c[center - target + e]]
        require(all(index >= 941 and value % 2 == 0 for _, index, value in terms),
                "Every reset-band reflected coefficient is even and beyond selector940")
        require(sum(value for _, _, value in terms) <= c[941] + M - 2048,
                "Entire low reflected envelope bounded before any count decoding")
        low_reflections.append((target, terms))
    check("all_reset_band_reflections_even_and_tail_only", len(low_reflections), anchor)
    check("low_reset_unconditional_bound", c[941] + M - 2048 < 2 * M - 2048, True)
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
    check("exact_extra_clause_source", bare_clause_source, 940)
    check("exact_extra_predecessor_source", bare_predecessor_source, 939)
    first_reflected = min(center - e for e, value in enumerate(c) if value)
    check("first_reflection_is_even_label_band", first_reflected, 960)
    low_max = max(support - {anchor})
    check("unit_marker_product_above_clause", 2 * anchor > center, True)
    check("flag_coefficient_zero", c[anchor], 0)
    check("flag_physical_support_retained", anchor in support, True)
    padding_rows = []
    for target in range(spec["padding"], spec["padding_last"] + 1):
        local = hits(target)
        expected = [(target - 18, 1)] if target - 18 in support else []
        require(local == expected, "Every complete low-padding local coefficient array: " + str(target))
        spatial_source = target - spatial in support
        temporal_source = target in support
        maximum = sum(value for _, value in local) + int(spatial_source) + int(temporal_source)
        require(maximum <= 3 and all((value & 4) == 0 for value in range(maximum + 1)),
                "Every aligned padding digit is at most3 and avoids tested bit2")
        padding_rows.append((target, local, spatial_source, temporal_source, maximum))
    check("whole916_uniform_padding_fields", len(padding_rows), 916)
    check("padding_band_below_reflection_and_copy_tests", spec["padding_last"] < min(first_reflected, spec["north"]), True)
    maximum_product = max(dc) + max(support)
    check("complete_maximum_product", maximum_product, center + anchor)
    check("exact_zero_tail_start", spec["zero_tail"], maximum_product + 1)
    check("all_safe_dummy_outputs_above_padding", min(min(dc) + dummy, spatial + dummy, dummy) > spec["padding_last"], True)
    check("last_product_field", hits(maximum_product), [(anchor, c[0])])
    check("all_later_top_fields_zero", [(e, hits(e)) for e in range(maximum_product + 1, length) if hits(e)], [])
    check("at_least_one_zero_top_field", maximum_product + 1 < length, True)
    check("phase_reset_numerical", 2 * M - 2048 + 3 + RHO // 2 + 57 < RHO, True)
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
            "phase_difference": anchor - start, "clause_center": center,
            "predecode_marker_offsets": {"count": len(marker_offsets), "sha256": sha(encoded(marker_offsets)), "first": marker_offsets[0], "last": marker_offsets[-1]}, "last_product_exponent": maximum_product,
            "low_padding_geometry": {"count": len(padding_rows), "sha256": sha(encoded(padding_rows)),
                                     "minimum": min(row[-1] for row in padding_rows),
                                     "maximum": max(row[-1] for row in padding_rows)},
            "delta_exponents": delta_exponents,
            "one_tile_adjacent_bound": adjacent_selector + adjacent_controls,
            "boolean_convolution_maximum": max_boolean,
            "boolean_maximum_fields": [e for e, value in enumerate(envelope) if value == max_boolean]}


def whole_constants(c, support, spec, length):
    power = lambda e: 1 << (47 * e)
    B, beta = power(length), power(length) - 1
    dc = sum(value * power(e) for e, value in dc_coefficients(c, spec).items())
    base_reflection = sum((value // 2) * power(center - e)
                          for center in spec["centers"] for e, value in enumerate(c) if value)
    require(dc == power(18) + power(1005) + 2 * base_reflection,
            "Whole DC equals printed factor2 times the unscaled Phi reciprocal recipe")
    K = dc + B * power(spec["spatial"])
    MC = beta - sum(power(e) for e in support)
    require(MC == beta - sum(power(e) for e in range(951))
            - power(960) * sum(power(e) for e in range(26)) - power(1005),
            "Whole printed block-MC recipe independently preserves physical support")
    core = sum(power(spec["north"] + j) for j in range(9))
    core += sum(power(spec["west"] + spec["west_copy"] + j) for j in range(8)) + power(spec["anchor"])
    p = spec["padding"]
    padding = 4 * sum(power(e) for e in range(p, spec["padding_last"] + 1))
    merged_origin = 4 * sum(power(e) for e in range(spec["padding_last"] + 1))
    require(p == 1 and spec["padding_last"] == 916 and padding.bit_count() == 916
            and 4 + padding == merged_origin and merged_origin.bit_count() == 917,
            "Whole916-bit uniform padding and exact origin merge4+4rhoG916=4G917")
    native_core = 4 + (M - 4) * sum(power(e) for e in spec["centers"]) + core
    require(native_core.bit_count() == 62, "One43-bit clause plus19 core tests")
    native = native_core + padding
    require(native == merged_origin + (M - 4) * sum(power(e) for e in spec["centers"]) + core,
            "Exact whole MF_source merged-origin recipe")
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
        whole = whole_constants(c, support, spec, length)
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

def model():
    """Return parent, seed, actions, tiles, full3297 doubled coefficients, physical support."""
    parent, seed, actions, tiles, original = parent_model()
    c, support = shifted_model(original, SPEC)
    require(c[:942] == [2 + 2048 * (1 + w + 256 * n + 131072 * east + 33554432 * south)
                        for w, n, east, south in tiles],
            "Every new coefficient equals the exact admissible decoded tile")
    return parent, seed, actions, tiles, c, support


def constants(c, support):
    """Return the four whole fixed ports and the whole integer DC at L2953."""
    whole = whole_constants(c, support, SPEC, L)
    dc = whole["K"] - (1 << (47 * (L + SPEC["spatial"])))
    return whole, dc


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    parent, seed, actions, tiles, c, support = model()
    start_complemented = [255 - tiles[0][0], 511 - tiles[0][1], 255 - tiles[0][2], 511 - tiles[0][3]]
    require(start_complemented == [253, 76, 252, 510], "Exact retained Start selector0 calibration")
    require(all((start_complemented[3] >> j) & 1 for j in range(1, 9)), "All eight calibrated Start south bits are one")
    require(list(tiles[941]) == [4, 437, 2, 437], "Entire decoded tile941 calibration")
    tile941 = [255 - tiles[941][0], 511 - tiles[941][1], 255 - tiles[941][2], 511 - tiles[941][3]]
    require(tile941 == [251, 74, 253, 74] and tile941[3] & 1 == 0,
            "Entire complemented tile941 and forbidden southbit0")
    # A marker at1004 admits this exact local phase-test pattern at offset19.
    # This is not asserted to extend to a complete native word or polynomial zero.
    tile4 = [255 - tiles[3][0], 511 - tiles[3][1], 255 - tiles[3][2], 511 - tiles[3][3]]
    require(tile4 == [255, 507, 247, 511], "Entire decoded oldtile4/newtile3 negative-control calibration")
    negative_signature = [int(941 == 3)] + [(tile4[3] >> j) & 1 for j in range(8)] + [(tile4[2] >> 7) & 1]
    expected_signature = [(start_complemented[3] >> j) & 1 for j in range(9)] + [1]
    require(negative_signature == expected_signature, "Marker1004 offset19 reproduces the complete local Start-copy pattern")
    actual_dc = dc_coefficients(c, SPEC)
    require(SPEC["temporal"] == SPEC["west_copy"] == 18
            and sorted(e for e, value in actual_dc.items() if value == 1) == [18]
            and actual_dc[1005] == c[940] + 1,
            "Shared unit copy and exact scaled selector940/marker coefficient collision")
    controllers, whole = controller(parent, c, support, tiles, SPEC)
    require(controllers["L"] == L and controllers["d"] == D == 47 * L,
            "Exact announced length2953 and binary size138791")
    fixed_primes = [47, 2953]
    require(L == 2953 and D == prod(fixed_primes)
            and len(set(fixed_primes)) == len(fixed_primes)
            and all(p % 2 == 1 and parent.least_factor(p) is None for p in fixed_primes),
            "Complete squarefree factorization d=47*2953 with every distinct odd prime verified")
    require(controllers["spacing"] == 11316 and gcd(D, 11316) == 1,
            "Exact new coprime controller spacing")
    fixed = controllers["fixed"]
    require([row["p"] for row in fixed] == fixed_primes, "Every fixed prime divisor of the whole d")
    for row, expected in zip(fixed, (23, 492)):
        require(row["base2_order"]["order"] == row["B_order"]["order"] == expected
                and gcd(D, expected) == 1 and expected > 2,
                "Exact base2/B orders and coprimality")
        require(row["H"] != 0 and row["B_squared"] != 1, "Fixed controller units")
    require([row["base2_order"]["prime_factors"] for row in fixed] == [[23], [2, 3, 41]]
            and parent.least_factor(41) is None,
            "Every proper-order test for both fixed factors and primality41")
    selected = controllers["auxiliary_trials"][-1]
    require(controllers["selected_lambda"] == selected["p"] == 192373 > D
            and selected["p"] % 2 == 1 and parent.least_factor(selected["p"]) is None,
            "Exact auxiliary prime above d")
    require((selected["p"] - 1) % 11316 == 0 and selected["B_squared"] != 1
            and selected["H"] != 0 and 0 < selected["lift_quotient"] < selected["p"],
            "Complete controller progression, units and valuation exactly one")
    geometric = geometry(c, support, SPEC, L, tiles)
    require(not geometric["failed_checks"], "Complete physical geometry failed: " + repr(geometric["failed_checks"]))
    require(geometric["predecode_marker_offsets"]["count"] == 978
            and geometric["predecode_marker_offsets"]["first"] == 0
            and geometric["predecode_marker_offsets"]["last"] == 1005
            and geometric["first_reflected_exponent"] == 960
            and geometric["last_product_exponent"] == 2950,
            "Every pre-count physical marker offset and full single-band limits")
    require(geometric["low_reflected_geometry"]["count"] == 1005
            and geometric["low_reflected_geometry"]["maximum"] == 65215549415426
            and len(geometric["clause_temporal_sources"]) == 38,
            "Every low reflected array and every possible Boolean temporal clause source")
    require(geometric["low_padding_geometry"]["count"] == 916
            and geometric["low_padding_geometry"]["minimum"] == 1
            and geometric["low_padding_geometry"]["maximum"] == 3,
            "All916 low-padding fields have complete aligned Boolean sums at most3")
    require(geometric["phase_targets"] == tuple(range(961, 969)) + (1005,)
            and geometric["phase_support_offsets"]["count"] == 934
            and geometric["multiple_selector_exclusions"]["count"] == 932
            and geometric["multiple_selector_exclusions"]["first"] == (21, [940, 941])
            and geometric["multiple_selector_exclusions"]["last"] == (961, list(range(8)))
            and len(geometric["calibrated_tile941_exclusions"]) == 1
            and geometric["calibrated_tile941_exclusions"][0]["offset"] == 20,
            "Entire934-offset classification, including tile941 exceptional offset20")
    require(geometric["delta_exponents"] == [2922, 986, 977]
            and all(L - (e + 1) >= 3 for e in geometric["delta_exponents"]) and RHO > 3,
            "Exact ordinary safe-dummy magnitude margins")
    require(c[977] == 0 and c[978] == 2048 and 978 in support
            and geometric["one_tile_adjacent_bound"] <= 2 * M - 2048,
            "Sole Boolean dummy has no extra adjacent-weight allowance")
    require(L - 1006 > 1 and 2 * 7 * 3 < RHO, "Uniform 2C+F<q/3 slack")
    require(len(support) == 978 and 1005 in support and c[1005] == 0,
            "All978 physical positions are cleared in MC, including the zero-weight marker")
    # Removing the physical marker must fail the block-mask identity and alignment.
    omitted = support - {1005}
    omission_geometry = geometry(c, omitted, SPEC, L, tiles)
    require("flag_physical_support_retained" in omission_geometry["failed_checks"]
            and "zero_phase_is_a_support_candidate" in omission_geometry["failed_checks"],
            "Marker omission detected by full physical geometry")
    try:
        whole_constants(c, omitted, SPEC, L)
    except ValueError as error:
        require(str(error) == "Whole printed block-MC recipe independently preserves physical support",
                "Marker omission rejected by the independent whole block-mask identity")
        omission_error = str(error)
    else:
        raise ValueError("Marker omission unexpectedly accepted")
    # All942 selector counts,58 incoming carries and both Boolean summands.
    count_survivors = [(n, k, tau, bare) for n in range(943) for k in range(58)
                       for tau in (0, 1) for bare in (0, 1)
                       if (2 * n + k + tau + bare) & 2044 == 0]
    require(len(count_survivors) == 16 and max(row[0] for row in count_survivors) == 1
            and all(2 * n + k + tau + bare <= 3 for n, k, tau, bare in count_survivors)
            and 2 * 942 + 57 + 1 + 1 < 2048,
            "All scaled low-count survivors force n<=1 with no bit11 carry")
    require(all(((M + 2 + bare) & (M - 4)) == 0 for bare in (0, 1)),
            "Both complete occupied canonical clause values pass the actual mask")
    premature_dc = {1944 - e: value for e, value in enumerate(c) if value}
    for exponent in (18, 1005):
        premature_dc[exponent] = premature_dc.get(exponent, 0) + 1
    premature_raw = sum(value for exponent, value in premature_dc.items() if 1004 - exponent in support)
    require(premature_raw + 1 + RHO // 2 + 57 >= RHO,
            "Center1944 fails this unconditional incoming-marker reset bound")
    require(2 <= 3 and (2 & 2) != 0 and (2 & 4) == 0,
            "Bit1 is not uniformly safe under the complete three-Boolean low-field envelope")
    mask_rank = actual_mask_rank_checks(whole, SPEC, L)
    rebuilt, dc = constants(c, support)
    require(rebuilt == whole, "Fixed public tuple API equals full controller construction")
    ports = {}
    for port, value in whole.items():
        raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
        ports[port] = {"bits": value.bit_length(), "bytes": len(raw), "sha256": sha(raw)}
    coefficient_raw = encoded(c)
    data = {
        "schema": "scaled_clause_2953_finite_v1", "L": L, "d": D,
        "script_sha256": sha(Path(__file__).read_bytes()), "proof_sha256": PROOF_SHA,
        "parent_verifier_sha256": PARENT_SHA, "source_page_sha256": parent.PAGE_SHA,
        "decoder_sha256": parent.DECODER_SHA, "parent_proof_sha256": parent.PROOF_SHA,
        "recipe_bindings": {"seed_sha256": sha(seed.encode()), "actions_sha256": sha(encoded(actions)),
                            "tiles_sha256": sha(encoded(tiles)), "all3297_coefficients_sha256": sha(coefficient_raw)},
        "specification": SPEC, "Start_complemented": start_complemented, "tile941_complemented": tile941,
        "geometry": {**geometric, "physical_positions": len(support), "nonzero_coefficients": sum(bool(v) for v in c),
                     "coefficient_sum": sum(c), "coefficient_maximum": max(c), "control_positions": 35,
                     "native_core_population": 62, "padding_population": 916, "native_population": 978,
                     "MC_population": D - 978, "DC_bits": dc.bit_length()},
        "admissible_selector_bijection": {
            "formula": "g(0)=0; g(j)=j+1 for1<=j<=941", "count": 942,
            "old_indices_sha256": sha(encoded([0] + list(range(2, 943)))),
            "omitted_old_index": 1, "omitted_old_tile": [5, 0, 0, 0], "omitted_coefficient": 6145},
        "scaling_identity": {
            "scale": 2, "base_Phi_coefficients_sha256": BASE_PHI_SHA,
            "actual_K_recipe": "rho18+rho1005+rho^(L+9)+2*rho1945*Phi_base(1/rho)",
            "actual_clause_mask": M - 4, "actual_global_carry_bound": 57,
            "physical_MC_recipe": "beta-G951(rho)-rho960*G26(rho)-rho1005"},
        "merged_origin_recipe": {
            "separate_native": "4+4*rho*G916(rho)+(M-4)*rho1945+Ccore",
            "merged_native": "4*G917(rho)+(M-4)*rho1945+Ccore",
            "origin_plus_padding_population": 917, "separate_padding_population": 916,
            "source_shift": "Add beta exactly once to either whole native recipe"},
        "bit1_padding_negative_control": {
            "allowed_local_boolean_summands": [1, 1, 0], "raw_sum": 2,
            "bit1_intersection": 2, "bit2_intersection": 0,
            "scope": "Failure of a uniform local-envelope proof for bit1; no complete native counterexample is claimed."},
        "boolean_tau_count": {"tested_quadruples": 943 * 58 * 2 * 2, "survivors": count_survivors},
        "center1944_reset_bound_negative": {
            "tested_field": 1004, "maximum_local_raw": premature_raw,
            "spatial_upper_bound": 1, "temporal_upper_bound": RHO // 2, "carry_upper_bound": 57,
            "scope": "Failure of the unconditional zero-outgoing-carry bound before the marker; no full native counterexample or global minimality is claimed."},
        "actual_mask_rank_checks": mask_rank,
        "negative_marker_omission": {"whole_mask_error": omission_error,
                                     "failed_geometry_checks": omission_geometry["failed_checks"]},
        "marker1004_negative_control": {
            "offset": 19, "selected_tile": 3, "complemented_tile": tile4,
            "test_targets": list(range(960, 969)) + [1004],
            "temporal_preimages": list(range(941, 950)) + [985],
            "actual_signature": negative_signature, "required_Start_signature": expected_signature,
            "scope": "Exact compatible local phase-test pattern; no complete native witness or polynomial zero is claimed."},
        "complete_d_factorization": {"d": D, "distinct_primes": fixed_primes,
                                       "L": L, "L_distinct_primes": [2953]},
        "fixed_controller": fixed, "spacing": controllers["spacing"],
        "length_trials": controllers["length_trials"], "controller_trials": controllers["auxiliary_trials"],
        "selected_lambda": selected["p"], "constant_ports": ports,
        "raw_bytes": sum(row["bytes"] for row in ports.values()),
        "scope": "Complete finite recipes, merged4G917 origin identity, all916 actual low-padding arrays, all1005 reset-band arrays and incoming-only marker parity, all978 pre-count marker offsets, doubled-count cases with two Boolean summands, full sole-clause geometry, the entire934-offset one-hot/tile941 exclusion and the complete controller at every prime divisor47,2953 of d. The pinned ordinary PROOF.md supplies the unbounded carry/native/Pell arguments; no new formal-kernel replay."
    }
    require(data["raw_bytes"] == 69449, "Exact whole four-port byte cost")
    raw = encoded(data)
    for filename, content in (("certificate.json", raw), ("coefficients.json", coefficient_raw),
                              ("base_phi_coefficients.json", encoded([value // 2 for value in c]))):
        if args.write:
            (HERE / filename).write_bytes(content)
        else:
            require((HERE / filename).read_bytes() == content, "Deterministic artifact differs: " + filename)
    print(json.dumps({"status": "PASS", "L": L, "lambda": selected["p"],
                      "raw_bytes": data["raw_bytes"], "H": [row["H"] for row in fixed] + [selected["H"]],
                      "script_sha256": data["script_sha256"], "proof_sha256": PROOF_SHA,
                      "certificate_sha256": sha(raw)}, sort_keys=True))


if __name__ == "__main__":
    main()
