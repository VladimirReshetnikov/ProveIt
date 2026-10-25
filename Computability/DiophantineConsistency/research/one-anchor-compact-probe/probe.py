#!/usr/bin/env python3
"""Exploratory complete finite probe for one anchor2079 and a compact field."""
import argparse
import hashlib
import importlib.util
import json
from math import gcd, isqrt, lcm
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DECODER = ROOT / "research/complemented47-controller-independent/certify.py"
PAGE = ROOT / "candidates/one-page-compact66-radix55/equation.tex"
DECODER_SHA = "318665c36d7600a99dbddbacca11ef9a2d30f65e04a761efe25d1f3653e662ed"
PAGE_SHA = "440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff"
RHO, M, ANCHOR = 1 << 47, 1 << 44, 2079
CENTERS = (4161, 5228)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def least_factor(n):
    require(n >= 2, "Positive primality candidate")
    if n % 2 == 0:
        return None if n == 2 else 2
    for p in range(3, isqrt(n) + 1, 2):
        if n % p == 0:
            return p
    return None


def factors(n):
    found, p = [], 2
    while p * p <= n:
        if n % p == 0:
            found.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        found.append(n)
    return found


def order(base, p):
    require(least_factor(p) is None and base % p != 0, "Prime-field order")
    value = p - 1
    for f in factors(value):
        while value % f == 0 and pow(base, value // f, p) == 1:
            value //= f
    tests = {str(f): pow(base, value // f, p) for f in factors(value)}
    require(pow(base, value, p) == 1 and all(t != 1 for t in tests.values()), "Exact order proof")
    return {"order": value, "prime_factors": factors(value), "proper_tests": tests}


def model():
    require(sha(DECODER.read_bytes()) == DECODER_SHA, "Exact inherited decoder source")
    require(sha(PAGE.read_bytes()) == PAGE_SHA, "Exact complete original decoded seed page")
    spec = importlib.util.spec_from_file_location("pinned_one_anchor_decoder", DECODER)
    require(spec is not None and spec.loader is not None, "Decoder import specification")
    parent = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parent)
    seed, actions, tiles = parent.decode_tiles()
    c = parent.coefficients(tiles)
    original_sum = sum(c)
    for e in (1095, 2195, 3296):
        c[e] = 0
    c[ANCHOR] = 3 * M
    support = {e for e, value in enumerate(c) if value} | {1063, 1064}
    require(len(c) == 3297 and len(support) == 980 and max(support) == ANCHOR,
            "Complete modified physical support")
    require(sum(bool(x) for x in c) == 978 and sum(c[943:]) == 4 * M - 1024,
            "Complete modified coefficient array")
    require(max(c) == 3 * M and all(x == 0 for x in c[2080:]), "Anchor maximum and full zero tail")
    require(sum(c) == original_sum, "Whole coefficient sum preserved exactly")
    # Independently expand the proposed shared Psi(x,t), including 2t-1.
    arrays = []
    for t in (1, 2):
        a = [0] * 3297
        for j in range(8):
            a[1023 + j] += t ** j
            a[1003 + j] += t ** (17 + j)
        for j in range(9):
            a[1013 + j] += t ** (8 + j)
            a[983 + j] += t ** (25 + j)
        a[ANCHOR] += t ** 34 * (2 * t - 1)
        arrays.append(a)
    require(sum(arrays[0]) == 35 and all(v in (0, 1) for v in arrays[0]), "Psi-one exact indicator")
    require([1024 * v for v in arrays[1][943:]] == c[943:], "Psi-two exact weighted control array")
    return seed, actions, tiles, c, support


def dc_coefficients(c):
    result, origins = {}, {}
    for center in CENTERS:
        for e, coefficient in enumerate(c):
            if coefficient:
                exponent = center - e
                require(exponent not in result, "Reflected coefficient collision")
                result[exponent] = coefficient
                origins[exponent] = ["reflected", center, e]
    for exponent in [30, 62] + list(range(1137, 2080)):
        require(exponent not in result, "Unit/reflected coefficient collision")
        result[exponent] = 1
        origins[exponent] = ["unit"]
    return result, origins


def geometry(c, support):
    dc, origins = dc_coefficients(c)
    checks = {}

    def check(name, actual, expected):
        checks[name] = {"pass": actual == expected, "actual": actual, "expected": expected}

    def hits(target):
        return sorted((e, dc[target - e]) for e in support if target - e in dc)

    def reflected_hits(target, center):
        return sorted((e, c[center + e - target]) for e in support
                      if 0 <= center + e - target < len(c) and c[center + e - target])

    reflected_positions = [e for e, origin in origins.items() if origin[0] == "reflected"]
    check("first_reflected_exponent", min(reflected_positions), 2082)
    check("no_low_reflections", any(e < 2082 for e in reflected_positions), False)
    check("unit_kernel_exact", sorted(e for e, origin in origins.items() if origin[0] == "unit"),
          [30, 62] + list(range(1137, 2080)))
    check("phase_difference1065", sorted((a, b) for a in support for b in support if a - b == 1065),
          [(2079, 1014)])
    check("clause_difference1067_absent", sorted((a, b) for a in support for b in support if a - b == 1067), [])
    check("neighbor_difference1066_PRESENT", sorted((a, b) for a in support for b in support if a - b == 1066),
          [(2079, 1013)])
    check("neighbor_difference1068_absent", sorted((a, b) for a in support for b in support if a - b == 1068), [])
    check("Start_phase_target1014", hits(1014), [(984, 1)])
    check("anchor2079_counts_all_selectors", hits(2079), [(e, 1) for e in range(943)])
    check("anchor_bare_and_spatial_sources_absent", [e for e in (2049, 2017, 2037) if e in support], [])
    check("phase_spatial_predecessors_absent", sorted(e for e in (1014 - 42, 2079 - 42) if e in support), [])
    for j in range(9):
        target = 1013 + j
        check("temporal_copy_" + str(j), hits(target), [(983 + j, 1)])
        check("temporal_copy_no_spatial_" + str(j), target - 42 in support, False)
    for j in range(8):
        target = 1065 + j
        check("spatial_copy_" + str(j), hits(target), [(1003 + j, 1)])
        check("spatial_copy_source_" + str(j), target - 42 in support, True)
        check("spatial_copy_no_temporal_" + str(j), target in support, False)
    clause = sorted((e, c[e]) for e in support if c[e])
    adjacent = sorted((e, c[e + 1]) for e in support if c[e + 1])
    for center in CENTERS:
        check("whole_clause_" + str(center), hits(center), clause)
        check("clause_spatial_absent_" + str(center), center - 42 in support, False)
        check("preclause_spatial_absent_" + str(center), center - 43 in support, False)
    check("lower_predecessor4160", hits(4160), adjacent)
    check("upper_predecessor5227_WITH_extra", hits(5227), sorted(adjacent + [(2079, c[1013])]))
    check("upper_predecessor_foreign_component", reflected_hits(5227, 4161), [(2079, 1 << 18)])
    check("lower_predecessor_foreign_component", reflected_hits(4160, 5228), [])
    check("padding_predecessor6324", hits(6324), [(2079, 1 << 35)])
    check("entire_padding_zero_band6325_6364", [(e, hits(e)) for e in range(6325, 6365) if hits(e)], [])
    check("padding_spatial_zero_band", [e for e in range(6325, 6365) if e - 42 in support], [])
    check("last_nonzero_field7307", hits(7307), [(2079, c[0])])
    check("next_field7308_zero", hits(7308), [])
    check("complete_max_product_exponent", max(dc) + max(support), 7307)
    check("last_input_field2079", max(support), 2079)
    check("dummy_local_maximum_exponent", max(dc) + 1063, 6291)
    check("dummy_spatial_exponent", 1063 + 42, 1105)
    check("dummy_temporal_exponent", 1063, 1063)
    adjacent_selector_max = max(c[e + 1] for e in support if e < 943 and c[e + 1])
    adjacent_control_sum = sum(c[e + 1] for e in support if e >= 943 and c[e + 1])
    check("one_selected_tile_adjacent_bound", adjacent_selector_max + adjacent_control_sum <= 2 * M - 1024, True)
    check("adjacent_controls_below_full_label_sum", adjacent_control_sum <= M - 1024, True)
    check("each_selector_coefficient_below_M", max(c[:943]) < M, True)
    check("clause_predecessor_reset_inequality", 2 * M - 1024 + (1 << 18) + 29 < RHO, True)
    check("low_phase_reset_inequality", 952 + 3 * RHO // 4 + 29 < RHO, True)
    check("conservative_top_reset_inequality", 7 * (M + 30) < RHO, True)

    # Exact Boolean local convolution envelope, with two separately allowed
    # extra units at dummy1063. This is stronger finite data than samples.
    boolean_envelope = [0] * 7308
    for e in support:
        for exponent, value in dc.items():
            boolean_envelope[e + exponent] += value
    enhanced_envelope = boolean_envelope.copy()
    for exponent, value in dc.items():
        enhanced_envelope[1063 + exponent] += 2 * value
    boolean_maximum, enhanced_maximum = max(boolean_envelope), max(enhanced_envelope)
    check("global29_numerical_bound_given_temporal_bound",
          enhanced_maximum + 3 + 3 * RHO // 4 + 29 < 30 * RHO, True)
    envelope = {
        "boolean_maximum": boolean_maximum,
        "boolean_maximum_fields": [e for e, value in enumerate(boolean_envelope) if value == boolean_maximum],
        "with_extra_dummy_maximum": enhanced_maximum,
        "with_extra_dummy_maximum_fields": [e for e, value in enumerate(enhanced_envelope) if value == enhanced_maximum],
        "own_adjacent_coefficient_sum": sum(v for _, v in adjacent),
        "one_selected_tile_adjacent_selector_maximum": adjacent_selector_max,
        "one_selected_tile_adjacent_control_sum": adjacent_control_sum,
        "one_selected_tile_adjacent_bound": adjacent_selector_max + adjacent_control_sum,
        "unit_kernel_terms": 943, "bare_terms": 2, "spatial_terms": 1,
        "first_unit_dummy_target": 1137 + 1063,
        "last_unit_dummy_target": 2079 + 1063,
        "first_reflected_dummy_target": 2082 + 1063,
    }
    return checks, envelope


def constants(c, support, length):
    power = lambda e: 1 << (47 * e)
    B, beta = power(length), power(length) - 1
    dc, _ = dc_coefficients(c)
    dc_value = sum(v * power(e) for e, v in dc.items())
    K = dc_value + B * power(42)
    MC = beta - sum(power(e) for e in support if e != 1) - 2 * power(1063)
    core = sum(power(e) for e in range(1013, 1022))
    core += sum(power(e) for e in range(1065, 1073)) + power(2079)
    padding = (1 << 25) * power(6343) - power(6325)
    positive_padding = (RHO - 1) * sum(power(e) for e in range(6325, 6343))
    positive_padding += ((1 << 25) - 1) * power(6343)
    require(padding == positive_padding and padding.bit_count() == 871, "Exact871-bit padding identity")
    native = 4 + ((1 << 46) - 2) * sum(power(e) for e in CENTERS) + core + padding
    require(0 < dc_value < B and 0 < MC < beta and 0 < native < beta, "Whole scalar boxes")
    require(MC % 4 == 2 and native % 8 == 4, "Whole origin residues")
    require(native.bit_count() == 980 and MC.bit_count() == 47 * length - 980, "Whole mask populations")
    return {"beta": beta, "K": K, "MC": MC, "MF_source": native + beta}


def modular(p, c, tiles, length, whole):
    power = lambda e: pow(2, 47 * e, p)
    inverse = pow(power(1), -1, p)
    phi = 0
    for value in reversed(c):
        phi = (phi * inverse + value) % p
    kernel = sum(power(e) for e in range(1137, 2080))
    K = (power(30) + power(62) + kernel + power(length + 42)
         + (power(4161) + power(5228)) * phi) % p
    direct = power(30) + power(62) + kernel + power(length + 42)
    for center in CENTERS:
        for j, (w, n, east, south) in enumerate(tiles):
            direct += (1 + 1024 * (1 + w + 256 * n + 131072 * east + 33554432 * south)) * power(center - j)
        for start, bits, count in ((1023, 10, 8), (1003, 27, 8), (1013, 18, 9), (983, 35, 9)):
            direct += sum((1 << (bits + j)) * power(center - start - j) for j in range(count))
        direct += 3 * M * power(center - 2079)
    require(K == direct % p == whole["K"] % p, "Three complete modular K routes")
    B = power(length)
    return {"p": p, "B": B, "K": K, "B_squared": B * B % p,
            "H": (1 + B * K + B * B) % p}


def controllers(c, tiles, support):
    length_trials = []
    for length in range(7308, 7409):
        divisor = least_factor(length)
        item = {"length": length, "least_factor": divisor}
        length_trials.append(item)
        if divisor is not None:
            continue
        whole = constants(c, support, length)
        fixed = []
        for p in (47, length):
            row = modular(p, c, tiles, length, whole)
            row["base2_order"] = order(2, p)
            row["B_order"] = order(row["B"], p)
            fixed.append(row)
        item["fixed_moduli"] = fixed
        if any(row["B_squared"] == 1 or row["H"] == 0 for row in fixed):
            item["rejected_reason"] = "A fixed controller factor vanishes"
            continue
        spacing = lcm(*(row["B_order"]["order"] for row in fixed))
        d = 47 * length
        if gcd(spacing, d) != 1:
            item["rejected_reason"] = "Controller spacing not coprime to d"
            continue
        lambda_trials = []
        for multiplier in range((d - 1) // spacing + 1, (d - 1) // spacing + 502):
            p = spacing * multiplier + 1
            divisor = least_factor(p)
            trial = {"multiplier": multiplier, "candidate": p, "least_factor": divisor}
            lambda_trials.append(trial)
            if divisor is not None:
                continue
            trial.update(modular(p, c, tiles, length, whole))
            trial["lift_residue"] = pow(2, d * (p - 1), p * p)
            require(trial["lift_residue"] % p == 1, "Fermat lift")
            trial["lift_quotient"] = (trial["lift_residue"] - 1) // p
            if trial["B_squared"] != 1 and trial["H"] != 0 and trial["lift_quotient"]:
                item["selected"] = True
                return {"length_trials": length_trials, "L": length, "d": d,
                        "spacing": spacing, "lambda_trials": lambda_trials,
                        "lambda": p, "selected_controller": trial}, whole
        item["rejected_reason"] = "No auxiliary prime in501 specified progression trials"
    raise ValueError("No compatible length/controller in the explicitly bounded exploration")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    seed, actions, tiles, c, support = model()
    checks, envelope = geometry(c, support)
    controller, whole = controllers(c, tiles, support)
    require(controller["L"] - 6292 >= 3 and controller["L"] - 1106 >= 3
            and controller["L"] - 1064 >= 3 and RHO > 3,
            "Three safe dummy contributions sum below q/rho^2")
    ports = {}
    for name, value in whole.items():
        raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
        ports[name] = {"bits": value.bit_length(), "raw_bytes": len(raw), "sha256_big_endian": sha(raw)}
    failed = {name: result for name, result in checks.items() if not result["pass"]}
    data = {"schema": "one_anchor2079_compact_exploration_v1",
            "source_bindings": {"decoder_sha256": DECODER_SHA, "original_page_sha256": PAGE_SHA,
                                "probe_sha256": sha(Path(__file__).read_bytes()),
                                "seed_sha256": sha(seed.encode()), "actions_sha256": sha(encoded(actions)),
                                "tiles_sha256": sha(encoded(tiles)), "all3297_coefficients_sha256": sha(encoded(c))},
            "geometry_checks": checks, "failed_geometry_checks": failed,
            "complete_local_convolution_envelope": envelope,
            "coefficient_maximum": max(c), "coefficient_sum": sum(c),
            "nonselector_coefficient_sum": sum(c[943:]), "physical_positions": len(support),
            "nonzero_coefficients": sum(bool(v) for v in c),
            "core_population": 109, "padding_population": 871, "native_population": 980,
            "controller": controller, "ports": ports,
            "raw_bytes": sum(port["raw_bytes"] for port in ports.values()),
            "scope": "Exploratory finite whole-model evidence only; not an accepted compiler, whole ordinary proof or equation promotion."}
    raw = encoded(data)
    coefficient_raw = encoded(c)
    for filename, content in (("RESULTS.json", raw), ("COEFFICIENTS.json", coefficient_raw)):
        if args.write:
            (HERE / filename).write_bytes(content)
        else:
            require((HERE / filename).read_bytes() == content, "Deterministic artifact differs: " + filename)
    print(json.dumps({"status": "PASS" if not failed else "COUNTEREXAMPLE", "failed_checks": list(failed),
                      "L": controller["L"], "lambda": controller["lambda"], "raw_bytes": data["raw_bytes"],
                      "results_sha256": sha(raw), "local_boolean_maximum": envelope["boolean_maximum"],
                      "local_extra_dummy_maximum": envelope["with_extra_dummy_maximum"]}, sort_keys=True))


if __name__ == "__main__":
    main()
