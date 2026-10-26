"""Held fixed49/2039 direct finite probe; requires a separate ROOT release."""
import hashlib
import json
import math
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
RHO, M, D, STEP = 1 << 49, 1 << 46, 99911, 6114
B = None  # Materialized only after authenticating every declared source/input.
OLD = "research/parity-clause-independent/coefficients.json"
OLD_SHA = "626c3a671efc045c6127991a2e636c7db64a9afb146a3402c6e6322e1fa9854f"


def need(ok, reason):
    if not ok:
        raise ValueError(reason)


def unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, "DUPLICATE_KEY")
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError("NONFINITE_JSON")


def load(raw):
    return json.loads(raw, object_pairs_hook=unique, parse_constant=reject_constant)


def packed(value):
    return (json.dumps(value, sort_keys=True, indent=2) + "\n").encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def authenticate():
    pins_raw = (HERE / "PINS.json").read_bytes()
    hold = load((HERE / "HOLD.json").read_bytes())
    need(hold == {"status": "CODE_ONLY_HOLD", "pins_sha256": sha(pins_raw)}, "HOLD")
    pins = load(pins_raw)
    need(type(pins) is dict and set(pins) == {"schema", "files"}, "PINS")
    need(pins["schema"] == "tile_biased49_2039_probe_inputs_v1", "SCHEMA")
    need(type(pins["files"]) is dict and len(pins["files"]) >= 15, "PIN_FILES")
    for name, record in pins["files"].items():
        path = BASE / name
        need(type(name) is str and not Path(name).is_absolute()
             and ".." not in Path(name).parts and path.resolve() == path.absolute(), "PIN_PATH")
        need(type(record) is dict and set(record) == {"bytes", "sha256"}
             and type(record["bytes"]) is int and record["bytes"] >= 0
             and type(record["sha256"]) is str, "PIN_RECORD")
        raw = path.read_bytes()
        need(len(raw) == record["bytes"] and sha(raw) == record["sha256"], "PIN_BYTES:" + name)
    need("research/tile-biased49-length2039-controller-probe/probe.py" in pins["files"]
         and OLD in pins["files"], "PIN_CLOSURE")
    raw = (BASE / OLD).read_bytes()
    need(sha(raw) == OLD_SHA, "OLD_HASH")
    return raw, sha(pins_raw)


def coefficients(raw):
    old = load(raw)
    need(type(old) is list and len(old) == 3297 and all(type(x) is int for x in old), "OLD_TYPES")
    a, b, expected_old = [0] * 3297, [0] * 3297, [0] * 3297
    for start, width, shift in [(978, 8, 10), (969, 8, 27), (960, 9, 18), (942, 9, 35)]:
        for i in range(width):
            expected_old[start + i] = 1 << (shift + i)
            a[start + i] = 4 * expected_old[start + i]
    for j in range(942):
        need(old[j] >= 1025 and old[j] % 1024 == 1, "OLD_SELECTOR")
        u = (old[j] - 1) // 1024 - 1
        need(0 <= u < 1 << 34, "OLD_WORD")
        expected_old[j] = old[j]
        comp = (1 << 34) - 1 - u
        enc, toggle = comp % (1 << 17), 0
        for offset, width, target in [(17, 8, 987), (25, 9, 960)]:
            for i in range(width):
                bit, eps = (comp >> (offset + i)) & 1, (target + i + 877 - j) // 942
                need(eps in (0, 1), "BIAS_RANGE")
                enc += (bit + eps - 2 * bit * eps) << (offset + i)
                if 0 <= 1006 + j - target - i <= 941:
                    toggle |= 1 << (offset + i)
        a[j] = 1 + 4096 * ((1 << 34) - enc)
        b[j] = 1 + (1 << 12) * ((1 << 34) - (comp ^ toggle))
        need(0 < enc < 1 << 34 and 0 < a[j] < M, "ENCODED_BOUND")
    need(old == expected_old, "OLD_FULL_SHAPE")
    for start, width, shift in [(978, 8, 12), (969, 8, 29), (960, 9, 20), (942, 9, 37)]:
        for i in range(width):
            b[start + i] = 1 << (shift + i)
    need(a == b, "ENCODING_ROUTES")
    return a, b


def ports(a, b):
    kernel = 0
    for value in a[:1007]:
        kernel = kernel * RHO + value
    kernel += RHO ** 18 + B * RHO ** 9
    other = RHO ** 18 + (1 << (49 * (2039 + 9)))
    other += sum(value << (49 * (1006 - e)) for e, value in enumerate(b) if value)
    need(kernel == other, "KERNEL_ROUTES")
    es = set(range(951)) | set(range(960, 986)) | {1005}
    core = sum(RHO ** e for e in list(range(960, 969)) + list(range(987, 995)) + [1005])
    native = 4 + (M - 2) * RHO ** 1006 + core
    native += (RHO - 1) * sum(RHO ** e for e in range(2012, 2030)) + ((1 << 32) - 1) * RHO ** 2030
    result = {"beta": B - 1, "K": kernel, "MC": B - 1 - sum(RHO ** e for e in es), "MF_source": native + B - 1}
    geometric = lambda n: (RHO ** n - 1) // (RHO - 1)
    need(result["MC"] == B - 1 - geometric(951) - RHO ** 960 * geometric(26) - RHO ** 1005, "MC_ROUTE")
    need(result["MF_source"] == B + 3 + (M - 2) * RHO ** 1006 + core + (1 << 32) * RHO ** 2030 - RHO ** 2012, "MF_ROUTE")
    need(len(es) == 978 and result["MC"].bit_count() == D - 978 and native.bit_count() == 978, "POPULATION")
    need(0 < result["MC"] < B - 1 and 0 < native < B - 1 and 0 < kernel - B * RHO ** 9 < B, "SCALAR_BOX")
    need(result["MC"] % 4 == 2 and native % 8 == 4, "ORIGIN")
    independent_es = set(range(942)) | set(range(942, 951)) | set(range(960, 969)) | set(range(969, 977)) | set(range(978, 986)) | {977, 1005}
    independent = {"beta": (1 << D) - 1, "K": other,
                   "MC": B - 1 - geometric(951) - RHO ** 960 * geometric(26) - RHO ** 1005,
                   "MF_source": B + 3 + (M - 2) * RHO ** 1006 + core + (1 << 32) * RHO ** 2030 - RHO ** 2012}
    return result, es, (b, independent_es, independent)


def validate_model(c, positions, values, independent):
    expected_c, expected_positions, expected_values = independent
    need(type(c) is list and all(type(v) is int for v in c) and c == expected_c, "COEFFICIENTS")
    need(type(positions) is set and all(type(v) is int for v in positions) and positions == expected_positions, "PHYSICAL")
    need(type(values) is dict and all(type(v) is int for v in values.values()) and values == expected_values, "PORTS")


def residue(p, a, b, kernel):
    br, rr, dense = pow(2, D, p), RHO % p, 0
    for value in a[:1007]:
        dense = (dense * rr + value) % p
    dense = (dense + pow(rr, 18, p) + br * pow(rr, 9, p)) % p
    terms = (pow(rr, 18, p) + br * pow(rr, 9, p)
             + sum(value * pow(rr, 1006 - e, p) for e, value in enumerate(b) if value)) % p
    need(dense == terms == kernel % p, "MODULAR_ROUTES")
    return {"p": p, "B": br, "K": dense, "H": (1 + br * dense + br * br) % p}


def finite_checks(whole_d_power, unit_gcd, lift_quotient):
    return {"whole_d_congruence": whole_d_power == 1,
            "full_unit": unit_gcd == 1, "valuation_one": lift_quotient != 0}


def least_factor(n):
    if n == 2:
        return 0
    if n % 2 == 0:
        return 2
    for divisor in range(3, math.isqrt(n) + 1, 2):
        if n % divisor == 0:
            return divisor
    return 0


def validate_factor(n, factor):
    need(type(n) is int and n >= 2 and type(factor) is int, "PRIME_TYPES")
    if factor:
        need(2 <= factor <= math.isqrt(n) and n % factor == 0
             and all(n % t != 0 for t in range(2, factor)), "FACTOR")
    else:
        need(all(n % t != 0 for t in range(2, math.isqrt(n) + 1)), "PRIME")


def controller(a, b, kernel):
    fixed = residue(D, a, b, kernel)
    unit_product = (B * B - 1) * (1 + B * kernel + B * B)
    fixed["gcd"] = math.gcd(unit_product, D)
    need(fixed["gcd"] == math.gcd((fixed["B"] ** 2 - 1) * fixed["H"], D), "FIXED_GCD_ROUTES")
    evidence = {"fixed": fixed, "search_k_inclusive": [17, 216], "step": STEP, "candidates": [], "lambda": None}
    if fixed["gcd"] != 1:
        evidence["status"] = "REJECTED_FIXED_PREMISE"
        return evidence
    for k in range(17, 217):
        prime = STEP * k + 1
        factor = least_factor(prime)
        validate_factor(prime, factor)
        entry = {"k": k, "candidate": prime, "least_factor_or_zero": factor}
        if factor == 0:
            r = residue(prime, a, b, kernel)
            lift = pow(2, D * (prime - 1), prime * prime)
            need(prime > D and lift % prime == 1 and (prime - 1) % STEP == 0, "LAMBDA_BASE")
            entry.update(r)
            entry["whole_d_power"] = pow(2, D * (prime - 1), D)
            entry["unit_gcd"] = math.gcd(unit_product, D * prime)
            need(entry["unit_gcd"] == math.gcd((r["B"] ** 2 - 1) * r["H"], prime), "LAMBDA_GCD_ROUTES")
            entry["lift_quotient"] = (lift - 1) // prime
            entry["checks"] = finite_checks(entry["whole_d_power"], entry["unit_gcd"], entry["lift_quotient"])
            if all(entry["checks"].values()):
                evidence["lambda"] = prime
        evidence["candidates"].append(entry)
        if evidence["lambda"] is not None:
            evidence["status"] = "P_BIAS_CERTIFIED"
            return evidence
    evidence["status"] = "REJECTED_BOUNDED_SEARCH"
    return evidence


def controls(a, es, result, independent):
    passed = []
    def reject(label, expected, action):
        try:
            action()
        except ValueError as error:
            need(str(error) == expected, "CONTROL_REASON:" + label)
            passed.append(label)
        else:
            raise ValueError("CONTROL_ACCEPTED:" + label)
    model = lambda c, positions, values: validate_model(c, positions, values, independent)
    model(list(a), set(reversed(sorted(es))), dict(reversed(list(result.items()))))
    for n in (2, 3, 5):
        validate_factor(n, 0)
    validate_factor(9, 3)
    for index, delta in [(0, 4096), (969, 1), (3296, 1)]:
        mutant = list(a)
        mutant[index] += delta
        reject("coefficient_" + str(index), "COEFFICIENTS", lambda: model(mutant, es, result))
    for index in (977, 1005):
        values = dict(result, MC=result["MC"] + RHO ** index)
        need(values["MC"].bit_count() == D - 977 and values["MC"] & (RHO ** index), "PHYSICAL_MUTATION")
        reject("physical_" + str(index), "PHYSICAL", lambda: model(a, es - {index}, values))
    for name, delta in [("K", 1), ("beta", -1), ("MF_source", -(B - 1))]:
        reject("port_" + name, "PORTS", lambda: model(a, es, dict(result, **{name: result[name] + delta})))
    reject("restored_bare_marker", "PORTS", lambda: model(a, es, dict(result, K=result["K"] + RHO ** 1005)))
    reject("composite_as_prime", "PRIME", lambda: validate_factor(9, 0))
    for label, args in [("whole_d_congruence", (0, 1, 1)), ("full_unit", (1, D, 1)), ("valuation_one", (1, 1, 0))]:
        need(not all(finite_checks(*args).values()) and not finite_checks(*args)[label], "FINITE_CONTROL:" + label)
        passed.append(label)
    reject("duplicate_json", "DUPLICATE_KEY", lambda: load(b'{"x":1,"x":2}'))
    reject("nonfinite_json", "NONFINITE_JSON", lambda: load(b'NaN'))
    for value in (True, 1.0):
        mutant = list(a)
        mutant[0] = value
        reject("noninteger_" + type(value).__name__, "COEFFICIENTS", lambda: model(mutant, es, result))
    return {"negative": passed, "valid": ["copied_coefficients_reordered_set_and_ports", "prime_2", "prime_3", "prime_5", "factor_9_3"]}


def main():
    global B
    need(sys.argv[1:] in ([], ["--write"]), "CLI")
    authenticated = authenticate()
    B = 1 << D
    a, b = coefficients(authenticated[0])
    result, es, independent = ports(a, b)
    validate_model(a, es, result, independent)
    blobs = {name + ".bin": value.to_bytes((value.bit_length() + 7) // 8, "big") for name, value in result.items()}
    report = {"schema": "tile_biased49_2039_finite_v1", "parameters": {"b": 49, "L": 2039, "d": D},
              "controller": controller(a, b, result["K"]), "controls": controls(a, es, result, independent),
              "ports": {name: {"bytes": len(blob), "sha256": sha(blob)} for name, blob in blobs.items()}}
    blobs["COEFFICIENTS.json"], blobs["RESULTS.json"] = packed(a), packed(report)
    target = HERE / "data"
    if sys.argv[1:] == ["--write"]:
        target.mkdir()
        for name, blob in sorted(blobs.items()):
            with (target / name).open("xb") as stream:
                stream.write(blob)
    need(target.is_dir() and not target.is_symlink() and target.resolve() == target.absolute()
         and {p.name for p in target.iterdir()} == set(blobs), "DATA_MEMBERS")
    need(all((target / name).is_file() and not (target / name).is_symlink()
             and (target / name).read_bytes() == blob for name, blob in blobs.items()), "DATA_BYTES")
    need(authenticate() == authenticated, "AUTH_CHANGED")
    sys.stdout.buffer.write(packed(report))


if __name__ == "__main__":
    main()
