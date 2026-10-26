#!/usr/bin/env python3
"""Reproduce the complete proof-bound phase-split2471 finite certificate."""
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
L, D = 2471, 116137
PROOF = HERE / "PROOF.md"
PROOF_SHA = "934c7984038b578a68b1396fffdb8db71a9039b01a86455a74c8639264a1b966"
SPEC = {"south": 942, "west": 969, "north": 960, "east": 978,
        "dummy": 977, "anchor": 1004, "temporal": 18, "west_copy": 18,
        "spatial": 9, "centers": [1462], "padding": 1, "padding_last": 916, "zero_tail": 2467}



def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def parent_model():
    require(sha(PROOF.read_bytes()) == PROOF_SHA, "Exact frozen complete phase-split2471 ordinary proof")
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
    weight = lambda tile: tile[0] + 256 * tile[1] + 131072 * tile[2] + 33554432 * tile[3]
    selected = selected[:1] + sorted(selected[1:], key=weight, reverse=True)
    require(list(selected[504]) == [3, 436, 4, 4], "Sorted physical initializer504")
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
    c[1:942] = sorted(c[1:942], reverse=True)
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
        elif r in (19, 20):
            require([target - r for target in range(spec["north"], spec["north"] + 9)]
                    == list(range(960-r, 969-r)), "Exact nine global same-cell preimages")
            global_exclusions.append({"offset": r, "method": "Complete512-state graph excludes a closed Start510 walk"})
        else:
            unresolved.append((r, preimages))
    check("zero_phase_is_a_support_candidate", 0 in phase_offsets, True)
    check("all_nonzero_offsets_excluded", unresolved, [])
    check("exact_calibrated_tile941_south", last_tile_south, 511)
    check("no_local_terminal_bit_exclusion", [row["offset"] for row in calibrated_exclusions], [])
    check("all_support_offsets_within_no_wrap_bounds", all(0 <= r <= start for r in phase_offsets), True)
    check("every_nonzero_offset_at_least_anchor_minus_lowmax", all(r >= anchor - max(support - {anchor}) for r in phase_offsets if r), True)
    check("all_offsets_classified", len(phase_offsets), 1 + len(multiple_selectors) + len(calibrated_exclusions) + len(global_exclusions))
    # The logical order is phase-dependent. For phases0..10 the full
    # reflected tail gives reset before counting. For phases11..46 the
    # low clause bits first force at most one selector without label
    # decoding, and every low reflected input is itself a selector.
    low_reflections = []
    for target in range(anchor):
        terms = [(e, center - target + e, c[center - target + e]) for e in support
                 if 0 <= center - target + e < len(c) and c[center - target + e]]
        require(all(0 <= e <= 526 and e < 942 and index >= 459
                    and value % 2 == 0 for e, index, value in terms),
                "Every reset-band reflection has a selector input and an even coefficient in tail459..985")
        require(sum(value for _, _, value in terms) <= sum(c[459:]),
                "Complete small-phase low reflected envelope before any count decoding")
        require(all(value < M for _, _, value in terms),
                "With at most one selector every large-phase low reflected value is below M")
        low_reflections.append((target, terms))
    check("all_reset_band_reflections_even_and_tail_only", len(low_reflections), anchor)
    check("small_phase_unconditional_reset", sum(c[459:]) + 3 + (1 << 10) + 57 < RHO, True)
    check("large_phase_one_selector_reset", M - 1 + 3 + RHO // 2 + 57 < RHO, True)
    check("all_low_reflected_inputs_are_selectors", all(e < 942
          for _, terms in low_reflections for e, _, _ in terms), True)
    check("maximum_low_reflected_selector", max(e for _, terms in low_reflections for e, _, _ in terms), 526)
    check("uniform_old_reset_no_longer_suffices", sum(c[459:]) + 3 + RHO // 2 + 57 >= RHO, True)
    check("marker_reflected_coefficients_even", all(value % 2 == 0
          for e, value in hits(anchor) if e != 0), True)
    check("actual_marker_coefficient_collision", dc[anchor], c[center - anchor] + 1)
    marker_offsets = sorted(anchor - e for e in support)
    check("marker_offsets_after_fractional_phase_exclusion", all(0 <= r <= anchor for r in marker_offsets), True)
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
    check("exact_extra_clause_source", bare_clause_source, 458)
    check("exact_extra_predecessor_source", bare_predecessor_source, 457)
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
    check("phase_reset_numerical", sum(c[459:]) + 3 + (1 << 10) + 57 < RHO, True)
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
                                        "maximum": max(sum(term[2] for term in terms) for _, terms in low_reflections),
                                        "maximum_selector_input": max(e for _, terms in low_reflections for e, _, _ in terms),
                                        "maximum_single_coefficient": max(value for _, terms in low_reflections for _, _, value in terms)},
            "clause_temporal_sources": clause_temporal_sources,
            "phase_targets": phase_targets,
            "phase_support_offsets": {"count": len(phase_offsets), "sha256": sha(encoded(phase_offsets))},
            "multiple_selector_exclusions": {"count": len(multiple_selectors),
                                             "sha256": sha(encoded(multiple_selectors)),
                                             "first": multiple_selectors[0], "last": multiple_selectors[-1]},
            "calibrated_tile941_exclusions": calibrated_exclusions,
            "global_phase_exclusions": global_exclusions,
            "phase_difference": anchor - start, "clause_center": center,
            "integral_phase_marker_offsets": {"count": len(marker_offsets), "sha256": sha(encoded(marker_offsets)), "first": marker_offsets[0], "last": marker_offsets[-1]}, "last_product_exponent": maximum_product,
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
    require((1 << 47) & (MC + 1) == 0, "Sorted physical selector1 is allowed")
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


def phase_graphs(tiles):
    """Complete phase19/20 graphs; the forced Start510 need not be their only-cycle state."""
    require(list(tiles[940]) == [206, 10, 0, 0] and list(tiles[941]) == [0, 0, 0, 0]
            and 511 - tiles[0][3] == 510, "Both sorted terminal South labels511 and forced Start510")
    records = []
    for offset, bits in ((19, 1), (20, 2)):
        first = 960 - offset
        preimages = list(range(first, first + 9))
        require(preimages == list(range(first, 942)) + list(range(942, 951 - bits)),
                "All nine same-cell copy preimages")
        graph = {south: {(south << bits) % 512} for south in range(512)}
        for physical in range(first, 942):
            south = 511 - tiles[physical][3]
            graph[south].add(((south << bits) + (1 << (physical - first))) % 512)
        transitions = [(None, 0, 0)]
        for physical, tile in enumerate(tiles):
            south = 511 - tile[3]
            selector_bits = [int(physical == index) for index in range(first, 942)]
            copied_bits = selector_bits + [(south >> j) & 1 for j in range(9 - bits)]
            current = sum(value << j for j, value in enumerate(copied_bits))
            require(current in graph[south] and sum(selector_bits) <= 1,
                    "Every complete decoded tile transition obeys the graph and one-hot constraint")
            transitions.append((physical, south, current))
        require(len(transitions) == 943, "All942 sorted tiles plus empty state")
        reached, queue = set(), [510]
        while queue:
            source = queue.pop()
            for target in graph[source]:
                if target not in reached:
                    reached.add(target)
                    queue.append(target)
        expected = {0, 256, 384, 448, 480, 496, 504, 508} if offset == 19 else {0, 384, 480, 504}
        require(reached == expected and 510 not in reached and 511 not in reached,
                "Complete nonempty reachability excludes any closed walk through the forced Start")
        require(graph[511] == ({510, 511} if offset == 19 else {508, 509, 510}),
                "Every exceptional transition, including the permitted phase19 nonzero cycle")
        require(offset != 19 or 511 in graph[511],
                "Negative control: claiming all nonzero cycles absent would be false")
        records.append({"offset": offset, "preimages": preimages,
                        "graph": [{"south": s, "successors": sorted(graph[s])} for s in range(512)],
                        "native_transitions": {"count": len(transitions), "sha256": sha(encoded(transitions))},
                        "forced_Start_south": 510, "reachable_by_nonempty_walk_from_Start": sorted(reached),
                        "Start_on_cycle": False,
                        "consequence": "Any finite temporal permutation cycle through the forced Start would give a forbidden nonempty closed walk through510."})
    return records


def universal_phase_controls():
    """Finite stronger controls: neither phase needs a special sorted terminal color."""
    phase19 = []
    for exceptional in range(512):
        reached, queue = set(), [510]
        while queue:
            source = queue.pop()
            successors = {(2 * source) % 512}
            if source == exceptional:
                successors.add((2 * source + 1) % 512)
            for target in successors:
                if target not in reached:
                    reached.add(target)
                    queue.append(target)
        require(510 not in reached, "Phase19 excludes Start for every possible unique exceptional South color")
        phase19.append((exceptional, sorted(reached)))
    phase20 = [(south, delta, (4 * south + delta) % 512)
               for south in range(512) for delta in range(3)]
    require(all(current % 4 != 3 for _, _, current in phase20)
            and all(south % 4 == 3 for south, _, current in phase20 if current == 510),
            "Phase20 forces all colors not3mod4 but Start510 requires a predecessor3mod4")
    require(any(current == 510 for _, _, current in phase20),
            "The phase20 contradiction is global rather than local infeasibility")
    return {"phase19_all512_exceptional_colors_sha256": sha(encoded(phase19)),
            "phase19_cases": 512, "phase20_all1536_cases_sha256": sha(encoded(phase20)),
            "phase20_cases": 1536,
            "phase20_global_contradiction": "Every color is0,1,2mod4, but Start510 requires a predecessor3mod4.",
            "scope": "Uniform finite strengthenings; the actual full two512-state graphs and actual decoded transitions are also checked."}


def fractional_phase_checks(c, support, geo):
    """Check both proof regimes without using decoded label identities first."""
    require(all(value % 2048 == 2 for value in c[:942])
            and all(value % 2048 == 0 for value in c[942:])
            and len(support & set(range(942))) == 942,
            "Before label decoding, every selector contributes2 and every control0 modulo2048")
    low_maximum = 2 * 942 + 57 + 1
    require(low_maximum == 1942 < 2048,
            "Prelabel high-phase count has no low eleven-bit wrap")
    high_survivors = [(n, carry, bare) for n in range(943) for carry in range(58)
                      for bare in (0, 1) if (2 * n + carry + bare) & 2044 == 0]
    require(len(high_survivors) == 10 and max(row[0] for row in high_survivors) == 1
            and all(2 * n + carry + bare <= 3 for n, carry, bare in high_survivors),
            "All high-phase count cases force at most one selector before labels or reset")
    temporal_rows = []
    for phase in range(11, 47):
        unit = 1 << phase
        require(unit < RHO and unit % 2048 == 0,
                "Every large fractional phase contributes an integral multiple of2048 within one radix field")
        residues = [(low, present, ((low + unit * present) % RHO) & 2044)
                    for low in range(low_maximum + 1) for present in (0, 1)]
        require(all(actual == (low & 2044) for low, _, actual in residues),
                "Actual radix reduction and temporal digit preserve every tested low clause bit")
        temporal_rows.append({"phase": phase, "temporal_unit": unit,
                              "complete_low_residue_cases": len(residues),
                              "sha256": sha(encoded(residues))})
    small_rows = [{"phase": phase, "temporal_maximum": 1 << phase,
                   "reset_bound": sum(c[459:]) + 3 + (1 << phase) + 57}
                  for phase in range(11)]
    require(all(row["reset_bound"] < RHO for row in small_rows),
            "All eleven small-phase resets hold before counting")
    require(geo["low_reflected_geometry"]["maximum_selector_input"] == 526
            and geo["low_reflected_geometry"]["maximum_single_coefficient"] < M
            and M - 1 + 3 + RHO // 2 + 57 < RHO,
            "After prelabel count, selector-only low geometry supplies every large-phase reset")
    require(all(c[e] % 2 == 0 for e in range(len(c)))
            and all((1 << phase) % 2 == 0 for phase in range(1, 47)),
            "After either reset argument, every nonzero fractional phase has even reflection and temporal contribution")
    # The threshold11 is essential for this count-first argument: at10,
    # a permitted temporal unit can make a large count invisible in bits2..10.
    negative_raw = 2 * 512 + (1 << 10)
    require(negative_raw == 2048 and negative_raw & 2044 == 0 and 512 <= 942,
            "Actual phase10 negative control rejects applying the high-phase count lemma too early")
    return {"small_phases": small_rows, "large_phases": temporal_rows,
            "large_phase_count": {"tested_triples": 943 * 58 * 2,
                                  "maximum_low_part": low_maximum, "survivors": high_survivors},
            "phase10_count_first_negative": {"selector_count": 512, "carry": 0,
                "bare": 0, "temporal_digit": 1024, "raw_low_part": negative_raw,
                "tested_bits": negative_raw & 2044,
                "scope": "Counterexample to the premature local count lemma, not a complete native solution."},
            "proof_order": "Phases0..10: unconditional tail reset; phases11..46: prelabel low clause count, selector-only reset; every phase1..46: marker parity contradiction."}


def rank_recipe(original, sorted_coefficients):
    """Check a complete short finite floor recipe for every sorted selector exponent."""
    abstract = original[:1] + original[2:943]
    require(len(abstract) == 942 and len(set(abstract)) == 942
            and all(0 < value < BASE_M for value in abstract), "Distinct bounded original admissible weights")
    ranks = [0]
    for value in abstract[1:]:
        comparisons = [(BASE_M - 1 + other - value) // BASE_M for other in abstract[1:]]
        require(all(bit in (0, 1) for bit in comparisons)
                and comparisons == [int(other > value) for other in abstract[1:]],
                "Every941-term floor comparison agrees with exact strict order")
        ranks.append(1 + sum(comparisons))
    require(sorted(ranks) == list(range(942)) and ranks[0] == 0
            and all(sorted_coefficients[ranks[i]] == 2 * value for i, value in enumerate(abstract)),
            "Complete rank-defined permutation equals the physical doubled selector array")
    require(ranks[928] == 504, "Exact rank of the retained initializer")
    all_sorted_start_rank = sum(value > abstract[0] for value in abstract)
    require(all_sorted_start_rank != 0, "Sorting Start with all other tiles would move the forced origin")
    return {"formula": "pi(0)=0; pi(i)=1+sum_{j=1..941}floor((2^44-1+a_j-a_i)/2^44)",
            "abstract_old_indices": [0] + list(range(2, 943)), "all942_ranks": ranks,
            "comparisons_checked": 941 * 941, "initializer_rank": 504,
            "sorting_Start_negative": {"unprotected_Start_rank": all_sorted_start_rank}}


def model():
    """Return authenticated parent, seed, actions, sorted tiles, doubled3297 coefficients, support."""
    parent, seed, actions, tiles, original = parent_model()
    c, support = shifted_model(original, SPEC)
    require(c[:942] == [2 + 2048 * (1 + w + 256 * n + 131072 * east + 33554432 * south)
                        for w, n, east, south in tiles], "Every doubled sorted decoded coefficient")
    require(c[1:942] == sorted(c[1:942], reverse=True) and len(set(c[:942])) == 942,
            "Complete strict descending non-Start order")
    rank_recipe(original, c)
    return parent, seed, actions, tiles, c, support


def constants(c, support):
    """Return all four whole fixed ports and the whole DC at L2471."""
    whole = whole_constants(c, support, SPEC, L)
    return whole, whole["K"] - (1 << (47 * (L + SPEC["spatial"])))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    parent, seed, actions, tiles, c, support = model()
    _, _, _, _, original, _ = parent.model()
    start = [255 - tiles[0][0], 511 - tiles[0][1], 255 - tiles[0][2], 511 - tiles[0][3]]
    require(start == [253, 76, 252, 510] and all((start[3] >> j) & 1 for j in range(1, 9)),
            "Entire unchanged Start0 and eight South one-bits")
    require(support == set(range(951)) | set(range(960, 986)) | {1004},
            "Independent whole978 physical support")
    require(c[977] == 0 and c[978] == 2048 and c[1004] == 0,
            "Boolean dummy and marker remain physical with zero weights")
    require(list(tiles[504]) == [3, 436, 4, 4], "Entire sorted initializer calibration")
    permutation = rank_recipe(original, c)
    graphs = phase_graphs(tiles)
    uniform_phases = universal_phase_controls()
    require(sum(c[459:]) == 137820284543942 and sum(c[458:]) == 140981380502472,
            "Both complete neighboring sorted suffix sums")
    ctl, whole = controller(parent, c, support, tiles, SPEC)
    length, d, fixed = ctl["L"], ctl["d"], ctl["fixed"]
    require(length == L == 2471 == 7 * 353 and d == D == 116137 == 47 * length
            and all(parent.least_factor(p) is None for p in (47, 7, 353)),
            "Exact entire squarefree fixed modulus and all its prime factors")
    require([row["p"] for row in fixed] == [47, 7, 353]
            and [row["base2_order"]["order"] for row in fixed] == [23, 3, 88]
            and [row["B_order"]["order"] for row in fixed] == [23, 3, 88]
            and [row["base2_order"]["prime_factors"] for row in fixed] == [[23], [3], [2, 11]]
            and all(parent.least_factor(p) is None for p in (23, 2, 3, 11)),
            "All exact orders and all prime proper-order tests")
    require(all(gcd(d, row["B_order"]["order"]) == 1 and row["H"] != 0 and row["B_squared"] != 1 for row in fixed)
            and ctl["spacing"] == 6072 and gcd(d, 6072) == 1,
            "Complete controller units and coprime spacing")
    require([row["H"] for row in fixed] == [15, 5, 224],
            "Actual whole-K controller units at all three fixed primes")
    failed_length = next(row for row in ctl["length_trials"] if row["length"] == 2469)
    require(failed_length["rejected_reason"] == "Fixed controller condition fails"
            and any(row["p"] == 3 and row["B_squared"] == 1 for row in failed_length["fixed"]),
            "The preceding odd squarefree length2469 fails its actual fixed-prime3 condition")
    auxiliary = ctl["auxiliary_trials"][-1]
    require(ctl["selected_lambda"] == auxiliary["p"] == 121441 > d
            and parent.least_factor(121441) is None and (121441 - 1) % 6072 == 0
            and auxiliary["B_squared"] != 1 and auxiliary["H"] != 0
            and 0 < auxiliary["lift_quotient"] == 6792 < 121441,
            "Exact auxiliary prime, whole H and valuation1")
    require(auxiliary["H"] == 114271, "Exact auxiliary whole-K unit")
    geo = geometry(c, support, SPEC, length, tiles)
    require(not geo["failed_checks"], "Complete sorted geometry: " + repr(geo["failed_checks"]))
    require(geo["phase_support_offsets"]["count"] == 935
            and geo["multiple_selector_exclusions"]["count"] == 932
            and geo["calibrated_tile941_exclusions"] == []
            and [row["offset"] for row in geo["global_phase_exclusions"]] == [19, 20],
            "All935 phases: zero,932 multiple selectors and both complete global exclusions")
    require(geo["low_reflected_geometry"]["count"] == 1004
            and geo["low_reflected_geometry"]["maximum"] == sum(c[459:])
            and geo["low_padding_geometry"]["count"] == 916
            and geo["low_padding_geometry"]["maximum"] == 5
            and len(geo["clause_temporal_sources"]) == 520,
            "Every full reset/padding array and possible temporal clause source")
    require(geo["first_reflected_exponent"] == 477 and geo["last_product_exponent"] == 2466
            and geo["delta_exponents"] == [2439, 986, 977], "Entire product and safe-dummy geometry")
    require(geo["integral_phase_marker_offsets"]["count"] == 978
            and geo["integral_phase_marker_offsets"]["first"] == 0
            and geo["integral_phase_marker_offsets"]["last"] == 1004,
            "Every integral-phase marker offset after fractional-phase exclusion")
    fractional_phases = fractional_phase_checks(c, support, geo)
    dc_coeffs = dc_coefficients(c, SPEC)
    require(sorted(e for e, value in dc_coeffs.items() if value == 1) == [18]
            and dc_coeffs[1004] == c[458] + 1 == 3161095958531,
            "Whole collided marker and single shared copy coefficient")
    require(L - 1005 > 1 and 42 < RHO
            and all(L - (e + 1) >= 3 for e in geo["delta_exponents"]),
            "Whole scalar slack and all three ordinary dummy degree-plus-one margins")
    survivors = [(n, k, tau, bare) for n in range(943) for k in range(58)
                 for tau in (0, 1) for bare in (0, 1) if (2 * n + k + tau + bare) & 2044 == 0]
    require(len(survivors) == 16 and max(row[0] for row in survivors) == 1
            and all(2 * n + k + tau + bare <= 3 for n, k, tau, bare in survivors)
            and 2 * 942 + 57 + 1 + 1 < 2048, "Entire doubled count lemma")
    require(all((M + 2 + bare) & (M - 4) == 0 for bare in (0, 1)), "Both occupied canonical clause values")
    mask_rank = actual_mask_rank_checks(whole, SPEC, length)
    rebuilt, dc = constants(c, support)
    require(rebuilt == whole, "Public whole-tuple API agrees with the complete controller tuple")
    omitted_geo = geometry(c, support - {1004}, SPEC, L, tiles)
    require("flag_physical_support_retained" in omitted_geo["failed_checks"]
            and "zero_phase_is_a_support_candidate" in omitted_geo["failed_checks"],
            "Marker omission fails complete geometry")
    omission_errors = {}
    for name, position in (("marker", 1004), ("dummy", 977)):
        try:
            whole_constants(c, support - {position}, SPEC, L)
        except ValueError as error:
            require(str(error) == "Whole printed block-MC recipe independently preserves physical support",
                    "Physical " + name + " omission fails independent block-MC identity")
            omission_errors[name] = str(error)
        else:
            raise ValueError("Physical " + name + " omission unexpectedly passed")
    premature = dc_coefficients(c, {**SPEC, "centers": [1461]})
    bad_raw = sum(value for exponent, value in premature.items() if 1003 - exponent in support)
    require(bad_raw + 3 + (1 << 10) + 57 >= RHO, "One smaller center fails the same small-phase tail envelope")
    require(4 <= 5 and 4 & 4 and not 4 & 8,
            "Bit2 padding is not justified by the complete local residue envelope")
    ports = {}
    for name, value in whole.items():
        raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
        ports[name] = {"bits": value.bit_length(), "bytes": len(raw), "sha256": sha(raw)}
    require({name: row["sha256"] for name, row in ports.items()} == {
        "beta": "4a9d0f18ed31c9f1759c106b71244a8a04caf3c8cf128a7241fc280052825cc4",
        "K": "9a863e00e5f9415c1a07d57959f632d0957eabd6967c58cd7822b1eaa116f449",
        "MC": "c5c1f555895bad3c17c23d3a10e61bb72ff830124be74abca843c01477f88871",
        "MF_source": "aed04479ff9beef8912ffb366b19d3259d672a680d150721c8a0fc2027b8b13e"},
        "All four ports agree with the separately reconstructed full2471 tuple")
    raw_bytes = sum(row["bytes"] for row in ports.values())
    require(raw_bytes == 58125, "Exact whole four-port bytes")
    base_c = [v // 2 for v in c]
    require(sha(encoded(base_c)) == "9b33c94814bcbed4a1f0f0e62cdf48d2a026e29c6550470397da7aa491cc0d45",
            "Entire sorted unscaled basePhi coefficient array")
    data = {"schema": "phase_split2471_finite_v1", "L": L, "d": D,
            "script_sha256": sha(Path(__file__).read_bytes()), "proof_sha256": PROOF_SHA,
            "parent_verifier_sha256": PARENT_SHA,
            "source_page_sha256": parent.PAGE_SHA, "decoder_sha256": parent.DECODER_SHA,
            "parent_proof_sha256": parent.PROOF_SHA, "unreordered_base_Phi_sha256": BASE_PHI_SHA,
            "seed_sha256": sha(seed.encode()), "actions_sha256": sha(encoded(actions)),
            "tiles_sha256": sha(encoded(tiles)), "scaled_coefficients_sha256": sha(encoded(c)),
            "base_Phi_coefficients_sha256": sha(encoded(base_c)),
            "recipe_bindings": {"seed_sha256": sha(seed.encode()), "actions_sha256": sha(encoded(actions)),
                                "tiles_sha256": sha(encoded(tiles)), "all3297_coefficients_sha256": sha(encoded(c)),
                                "base_Phi_coefficients_sha256": sha(encoded(base_c))},
            "Start_complemented": start,
            "rank_defined_permutation": permutation, "specification": SPEC,
            "geometry": {**geo, "physical_positions": len(support), "nonzero_coefficients": sum(bool(v) for v in c),
                         "coefficient_sum": sum(c), "coefficient_maximum": max(c), "control_positions": 35,
                         "native_core_population": 62, "padding_population": 916, "native_population": 978,
                         "MC_population": D - 978, "DC_bits": dc.bit_length()},
            "phase_graphs": graphs, "uniform_phase_controls": uniform_phases, "controller": ctl,
            "fractional_phase_split": fractional_phases,
            "full_tail459_sum": sum(c[459:]),
            "complete_d_factorization": {"d": D, "distinct_primes": [47, 7, 353], "L": L, "L_distinct_primes": [7, 353]},
            "fixed_controller": fixed, "spacing": ctl["spacing"], "length_trials": ctl["length_trials"],
            "controller_trials": ctl["auxiliary_trials"], "selected_lambda": auxiliary["p"],
            "constant_ports": ports, "raw_bytes": raw_bytes, "actual_mask_rank_checks": mask_rank,
            "count_lemma": {"tested_quadruples": 943 * 58 * 2 * 2, "survivors": survivors},
            "populations": {"physical": 978, "native": 978, "native_core": 62, "padding": 916},
            "origin_padding_identity": "4+8rhoG916(rho)=8G917(rho)-4",
            "center1461_negative": {"field": 1003, "raw": bad_raw,
                "scope": "Failure of the same small-phase envelope, not a complete native counterexample."},
            "negative_physical_omission": {"marker_failed_geometry": omitted_geo["failed_checks"],
                                          "whole_mask_errors": omission_errors},
            "bit2_padding_negative": {"allowed_residue": 4, "bit2_overlap": 4, "bit3_overlap": 0,
                "scope": "Failure of the uniform residue-envelope argument, not a native counterexample."},
            "scope": "Complete proof-bound finite floor-rank permutation, phase-split geometry, prelabel high-phase count bound, bit3 padding, both global Start-cycle exclusions, actual masks and controller. The pinned ordinary proof supplies unbounded native and Pell witness maps; no new formal-kernel replay or printed-cost claim."}
    raw = encoded(data)
    for filename, content in (("certificate.json", raw), ("coefficients.json", encoded(c)),
                              ("base_phi_coefficients.json", encoded(base_c))):
        if args.write:
            (HERE / filename).write_bytes(content)
        else:
            require((HERE / filename).read_bytes() == content, "Deterministic artifact differs: " + filename)
    print(json.dumps({"status": "PASS", "L": length, "raw_bytes": raw_bytes,
                      "lambda": auxiliary["p"], "H": [row["H"] for row in fixed] + [auxiliary["H"]],
                      "script_sha256": data["script_sha256"], "proof_sha256": PROOF_SHA,
                      "certificate_sha256": sha(raw)}, sort_keys=True))


if __name__ == "__main__":
    main()
