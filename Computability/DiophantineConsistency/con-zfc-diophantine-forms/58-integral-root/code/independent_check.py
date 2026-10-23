#!/usr/bin/env python3
"""Independent formula checks for the 15-positive-variable constructions.

This standard-library program does not import build.py, verify.py, or their
algebra implementations.  It authenticates the four packaged coefficient
payloads, validates circuit wiring and operation counts, and evaluates an
independent transcription of the displayed equations against all six JSON
circuits.  It also evaluates polynomials on deterministic generic rays over
three finite fields.  Nonzero top coefficients on those rays certify total
degree lower bounds for the actual fixed integer coefficients.  Matching
upper bounds are derived separately from the explicit cancellation formulas
in direct_formula(reduced=True).

The cancellation identities used for those upper bounds are just

  (q^3(ell+r)+Y)^2-q^6(ell(ell+k)+1)
    = q^6(2 ell r+r^2-ell k-1)+2q^3Y(ell+r)+Y^2;
  (ac+Z)^2-(a^2+H)c^2 = 2acZ+Z^2-Hc^2;
  (qD+XH)^2-q^2(Delta c^2+1)
    = q^2(D^2-Delta c^2-1)+2qDXH+(XH)^2.

This is an internal AI-assisted independent implementation check, not an
external certification, a proof-assistant check, or a consistency test.
The finite-field comparisons do not replace the mathematical soundness
and completeness proofs or the inherited compiler theorem.
"""

from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import random
import sys


ROOT = Path(__file__).resolve().parents[1]
PRIMES = (65537, 1000003, 1000000007)
SEED = 0xC05FC024
RANDOM_CASES_PER_PRIME = 64
RAYS_PER_PRIME = 4
PORT_ALIASES = {"beta": "beta", "K0": "K", "MC": "MC", "MF": "MF_source"}
WITNESSES_BOTH = ["j", "F", "alpha", "z", "f", "h", "i", "T", "X", "Y",
                  "r", "eta", "zeta", "u", "gamma"]
WITNESSES_SINGLE = ["J", "F", "alpha", "z", "f", "h", "i", "T", "w", "Y",
                    "r", "eta", "zeta", "u", "gamma"]
EXPECTED = {
    24: {"operations": 90, "certificate_operations": 102,
         "residuals": ["A", "B", "index_res", "transport_res", "auxiliary", "strong"],
         "residual_degrees": [11, 9, 4, 3, 12, 10]},
    26: {"operations": 88, "certificate_operations": 100,
         "residuals": ["A", "B", "coupled", "auxiliary", "strong"],
         "residual_degrees": [11, 9, 7, 13, 10]},
    30: {"operations": 79, "certificate_operations": 86,
         "residuals": ["A", "paired", "auxiliary", "strong"],
         "residual_degrees": [12, 15, 15, 10]},
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def within_root(path):
    resolved = path.resolve()
    require(resolved.is_relative_to(ROOT), "Path escapes submission: " + str(path))
    return resolved


def prime_check(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    trial = 3
    while trial * trial <= n:
        if n % trial == 0:
            return False
        trial += 2
    return True


def load_coefficients():
    binding_path = ROOT / "coefficients" / "COEFFICIENT_BINDING.json"
    binding = read_json(binding_path)
    entries = binding["materialization"]["files"]
    require(len(entries) == 4, "Binding must contain exactly four coefficient payloads")
    actual_ports = [item["port"] for item in entries]
    require(set(actual_ports) == set(PORT_ALIASES.values()) and len(set(actual_ports)) == 4,
            "Incomplete or duplicated coefficient tuple")
    by_port = {}
    receipts = []
    for entry in entries:
        path = within_root(binding_path.parent / entry["file"])
        compressed = path.read_bytes()
        raw = gzip.decompress(compressed)
        require(len(compressed) == entry["gzip_bytes"], "Compressed byte count differs: " + entry["port"])
        require(sha256(compressed) == entry["gzip_sha256"], "Compressed SHA-256 differs: " + entry["port"])
        require(len(raw) == entry["raw_bytes"], "Raw byte count differs: " + entry["port"])
        require(sha256(raw) == entry["sha256"], "Raw SHA-256 differs: " + entry["port"])
        value = int.from_bytes(raw, "little", signed=False)
        require(value > 0 and value.bit_length() == entry["bits"], "Bad coefficient value: " + entry["port"])
        by_port[entry["port"]] = value
        receipts.append({"port": entry["port"], "file": str(path.relative_to(ROOT)),
                         "raw_bytes": len(raw), "bits": value.bit_length(),
                         "sha256": sha256(raw), "gzip_sha256": sha256(compressed)})
    ports = {alias: by_port[name] for alias, name in PORT_ALIASES.items()}
    d = binding["d"]
    require(isinstance(d, int) and d > 0 and d % 2 == 1, "Expected an odd positive radix exponent")
    require(ports["beta"] + 1 == 1 << d, "beta is not the bound power of two minus one")
    require(0 < ports["MC"] < ports["beta"], "Low mask outside the inherited range")
    require(0 < ports["MF"] - ports["beta"] < ports["beta"], "High mask is not in shifted native range")
    padding_prime = binding["padding_controller"]["padding_prime"]
    require(padding_prime % 2 == 1, "Canonical padding prime must be odd")
    return ports, {
        "binding_file": str(binding_path.relative_to(ROOT)),
        "binding_sha256": sha256(binding_path.read_bytes()),
        "instance": binding["instance"], "source_commit": binding["source_commit"],
        "d": d, "padding_prime": padding_prime,
        "payloads": receipts,
        "scope": "Payload authentication and elementary tuple invariants only; native compiler audit is separate.",
    }


def reachable(rows, outputs):
    needed = set(outputs)
    for name, _op, left, right in reversed(rows):
        if name in needed:
            needed.add(left)
            needed.add(right)
    return {row[0] for row in rows if row[0] in needed}, needed


def read_circuit(path, degree, certificate):
    packet = read_json(path)
    want = EXPECTED[degree]
    witnesses = WITNESSES_BOTH if degree != 30 else WITNESSES_SINGLE
    require(packet["witnesses"] == witnesses, "Unexpected witness list: " + path.name)
    require(packet["domain"] == "strictly positive integers", "Unexpected domain: " + path.name)
    require(packet["fixed_numerals"] == list(PORT_ALIASES), "Unexpected coefficient ports: " + path.name)
    require(packet["port_aliases"] == PORT_ALIASES, "Mixed coefficient aliases: " + path.name)
    require(within_root(path.parent / packet["coefficient_binding_file"])
            == ROOT / "coefficients" / "COEFFICIENT_BINDING.json", "Wrong coefficient binding: " + path.name)
    require(packet["exact_degree"] == degree, "Wrong advertised degree: " + path.name)
    require(packet["degree_certificate_only"] is certificate, "Wrong certificate flag: " + path.name)
    require(packet["residuals"] == want["residuals"], "Wrong residual list: " + path.name)
    rows = packet["source"]
    available = set(witnesses) | set(PORT_ALIASES)
    for row in rows:
        require(isinstance(row, list) and len(row) == 4, "Malformed gate: " + path.name)
        name, op, left, right = row
        require(isinstance(name, str) and name not in available, "Duplicate or invalid gate: " + str(name))
        require(op in ("+", "-", "*"), "Unsupported gate operation: " + str(op))
        for value in (left, right):
            require(type(value) is int or isinstance(value, str) and value in available,
                    "Invalid or forward reference at " + name + ": " + str(value))
        available.add(name)
    for name in packet["residuals"] + [packet["output"]]:
        require(name in available, "Unknown output: " + name)
    expected_count = want["certificate_operations"] if certificate else want["operations"]
    require(len(rows) == expected_count == packet["operations"], "Operation count differs: " + path.name)
    breakdown = dict(Counter(row[1] for row in rows))
    require(breakdown == packet["operation_breakdown"], "Operation breakdown differs: " + path.name)
    live_rows, needed = reachable(rows, [packet["output"]])
    require(len(live_rows) == len(rows), "Dead gate present: " + path.name)
    require(set(witnesses) | set(PORT_ALIASES) <= needed, "Dead input present: " + path.name)
    core_rows, _ = reachable(rows, packet["residuals"])
    require(len(core_rows) == packet["residual_evaluator_operations"], "Residual count differs: " + path.name)
    return packet, {"file": str(path.relative_to(ROOT)), "sha256": sha256(path.read_bytes()),
                    "operations": len(rows), "operation_breakdown": breakdown,
                    "residual_evaluator_operations": len(core_rows),
                    "all_gates_and_inputs_live": True, "certificate_only": certificate}


class Polynomial:
    """Small exact univariate polynomial over the field with p elements."""

    def __init__(self, coefficients, p):
        values = [v % p for v in coefficients]
        while len(values) > 1 and values[-1] == 0:
            values.pop()
        self.coefficients = tuple(values or [0])
        self.p = p

    @property
    def degree(self):
        return -1 if self.coefficients == (0,) else len(self.coefficients) - 1

    def coerce(self, other):
        if isinstance(other, Polynomial):
            require(other.p == self.p, "Mixed finite fields")
            return other
        require(type(other) is int, "Unsupported polynomial operand")
        return Polynomial([other], self.p)

    def __add__(self, other):
        other = self.coerce(other)
        size = max(len(self.coefficients), len(other.coefficients))
        values = [0] * size
        for index, value in enumerate(self.coefficients):
            values[index] += value
        for index, value in enumerate(other.coefficients):
            values[index] += value
        return Polynomial(values, self.p)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial([-value for value in self.coefficients], self.p)

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        other = self.coerce(other)
        values = [0] * (len(self.coefficients) + len(other.coefficients) - 1)
        for left_index, left in enumerate(self.coefficients):
            for right_index, right in enumerate(other.coefficients):
                values[left_index + right_index] += left * right
        return Polynomial(values, self.p)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        require(type(exponent) is int and exponent >= 0, "Polynomial exponent must be a nonnegative integer")
        answer = Polynomial([1], self.p)
        base = self
        while exponent:
            if exponent % 2:
                answer = answer * base
            base = base * base
            exponent //= 2
        return answer

    def __eq__(self, other):
        other = self.coerce(other)
        return self.coefficients == other.coefficients


class DegreeBound:
    """Syntactic total-degree upper bound, used only on reduced formulas."""

    def __init__(self, degree):
        self.degree = degree

    @staticmethod
    def of(value):
        if isinstance(value, DegreeBound):
            return value.degree
        require(type(value) is int, "Unsupported degree operand")
        return 0

    def __add__(self, other):
        return DegreeBound(max(self.degree, self.of(other)))

    __radd__ = __add__
    __sub__ = __add__
    __rsub__ = __add__

    def __mul__(self, other):
        return DegreeBound(self.degree + self.of(other))

    __rmul__ = __mul__

    def __pow__(self, exponent):
        require(type(exponent) is int and exponent >= 0, "Bad degree exponent")
        return DegreeBound(self.degree * exponent)


def direct_formula(degree, w, constants, reduced=False):
    """Independent transcription; valid for integers and the two arithmetic types."""
    J = 3 * w["j"] + 1 if degree in (24, 26) else w["J"]
    q = constants["beta"] * J + 1
    X = w["X"] if degree in (24, 26) else w["w"] * q
    Y = w["Y"]
    C = q - w["F"] - w["alpha"]
    k = w["eta"] + w["zeta"]
    c = k * Y + w["eta"]
    a = X * Y + Y
    H = 4 * a + 3
    Delta = a ** 2 + H
    Z = X + w["gamma"] * H
    D = a * c + Z
    R = ((q - 1) * (q - w["F"]) + w["alpha"]) * (q ** 2 - 1) + (constants["MC"] + q * constants["MF"]) * J
    Rhat = k - w["h"] * X * Y - 1
    ell = X * Y ** 2 * k
    r = w["r"]
    if reduced:
        first = q ** 6 * (2 * ell * r + r ** 2 - ell * k - 1) + 2 * q ** 3 * Y * (ell + r) + Y ** 2
        norm = 2 * a * c * Z + Z ** 2 - H * c ** 2
    else:
        first = (q ** 3 * (ell + r) + Y) ** 2 - q ** 6 * (ell * (ell + k) + 1)
        norm = D ** 2 - Delta * c ** 2
    residuals = {"A": first}
    if degree in (24, 26):
        if reduced:
            main = q ** 2 * (norm - 1) + 2 * q * D * X * H + (X * H) ** 2
        else:
            main = (q * D + X * H) ** 2 - q ** 2 * (Delta * c ** 2 + 1)
        residuals["B"] = main
        transport = q * (constants["K0"] * C + q - w["F"] - w["z"] * (q - 1)) + X * C
        if degree == 24:
            residuals["index_res"] = Rhat - R
            residuals["transport_res"] = transport - q
        else:
            residuals["coupled"] = (k - w["h"] * X * Y - R) * transport - q
    else:
        index = k - w["h"] * X * Y - R
        transport = (constants["K0"] + w["w"]) * C + q - w["F"] - w["z"] * (q - 1)
        residuals["paired"] = norm * index * transport - 1
    U = Delta * (w["f"] ** 2 - 1)
    I = w["i"] * c ** 2
    V = w["f"] ** 2 * (c * w["T"] - (Rhat if degree == 24 else R)) - c
    gap = w["u"]
    residuals["auxiliary"] = (V + gap) ** 2 - U * gap * (2 * V + gap) - 1
    residuals["strong"] = I ** 2 - U
    result = sum(value ** 2 for value in residuals.values())
    return residuals, result


def circuit_formula(packet, witnesses, constants, modulus=None):
    values = dict(constants)
    values.update(witnesses)

    def operand(value):
        return value if type(value) is int else values[value]

    for name, operation, left, right in packet["source"]:
        x, y = operand(left), operand(right)
        if operation == "+":
            value = x + y
        elif operation == "-":
            value = x - y
        elif operation == "*":
            value = x * y
        else:
            raise ValueError("Unexpected operation")
        values[name] = value % modulus if modulus is not None else value
    return {name: values[name] for name in packet["residuals"]}, values[packet["output"]]


def compare_values(expected, observed, context, modulus=None):
    expected_residuals, expected_output = expected
    observed_residuals, observed_output = observed
    require(list(expected_residuals) == list(observed_residuals), "Residual order mismatch: " + context)
    for name, value in expected_residuals.items():
        if modulus is not None:
            value %= modulus
        require(value == observed_residuals[name], "Residual mismatch: " + context + ": " + name)
    if modulus is not None:
        expected_output %= modulus
    require(expected_output == observed_output, "Output mismatch: " + context)


def run():
    require(all(prime_check(p) for p in PRIMES), "A diagnostic modulus is not prime")
    authentic_ports, coefficient_receipt = load_coefficients()
    records = []
    comparison_count = 0
    for degree in (24, 26, 30):
        witnesses = WITNESSES_BOTH if degree != 30 else WITNESSES_SINGLE
        bounds, bound_output = direct_formula(degree,
            {name: DegreeBound(1) for name in witnesses},
            {name: DegreeBound(0) for name in PORT_ALIASES}, reduced=True)
        upper_bounds = [value.degree for value in bounds.values()]
        require(upper_bounds == EXPECTED[degree]["residual_degrees"] and bound_output.degree == degree,
                "Reduced formula gives unexpected upper degree bounds")
        for certificate in (False, True):
            filename = "p15_degree" + str(degree) + ("_degree_certificate" if certificate else "") + ".json"
            packet, record = read_circuit(ROOT / "circuits" / filename, degree, certificate)
            rng = random.Random(SEED + degree)
            sample_digest = hashlib.sha256()
            ray_records = []
            observed_maximum = [-1] * len(upper_bounds)
            observed_output_maximum = -1
            scalar_cases = 0
            for p in PRIMES:
                constants = {name: value % p for name, value in authentic_ports.items()}
                cases = [dict.fromkeys(witnesses, value) for value in (0, 1, -1)]
                cases.append({name: index + 1 for index, name in enumerate(witnesses)})
                cases.extend({name: rng.randrange(-p, p + 1) for name in witnesses}
                             for _ in range(RANDOM_CASES_PER_PRIME))
                for index, assignment in enumerate(cases):
                    context = filename + ", p=" + str(p) + ", scalar=" + str(index)
                    direct = direct_formula(degree, assignment, constants)
                    reduced = direct_formula(degree, assignment, constants, reduced=True)
                    compare_values(direct, reduced, context + ", cancellation formulas")
                    evaluated = circuit_formula(packet, assignment, constants, p)
                    compare_values(direct, evaluated, context, p)
                    payload = [evaluated[0][name] for name in packet["residuals"]] + [evaluated[1]]
                    sample_digest.update(json.dumps(payload, separators=(",", ":")).encode("ascii"))
                    scalar_cases += 1
                    comparison_count += len(payload)
                for index in range(RAYS_PER_PRIME):
                    slopes = {name: rng.randrange(1, p) for name in witnesses}
                    assignment = {name: Polynomial([0, slope], p) for name, slope in slopes.items()}
                    field_constants = {name: Polynomial([value], p) for name, value in constants.items()}
                    context = filename + ", p=" + str(p) + ", ray=" + str(index)
                    direct = direct_formula(degree, assignment, field_constants)
                    reduced = direct_formula(degree, assignment, field_constants, reduced=True)
                    compare_values(direct, reduced, context + ", cancellation formulas")
                    evaluated = circuit_formula(packet, assignment, field_constants)
                    compare_values(direct, evaluated, context)
                    degrees = [evaluated[0][name].degree for name in packet["residuals"]]
                    output_degree = evaluated[1].degree
                    for slot, value in enumerate(degrees):
                        require(value <= upper_bounds[slot], "A ray exceeds its residual degree upper bound")
                        observed_maximum[slot] = max(observed_maximum[slot], value)
                    require(output_degree <= degree, "A ray exceeds the output degree upper bound")
                    observed_output_maximum = max(observed_output_maximum, output_degree)
                    ray_records.append({"prime": p, "ray_index": index, "slopes": slopes,
                        "residual_degrees": degrees, "output_degree": output_degree,
                        "residual_leading_coefficients": [evaluated[0][name].coefficients[-1] for name in packet["residuals"]],
                        "output_leading_coefficient": evaluated[1].coefficients[-1]})
            require(observed_maximum == upper_bounds and observed_output_maximum == degree,
                    "Generic rays did not witness every claimed degree: " + filename)
            record.update({"scalar_cases": scalar_cases,
                           "scalar_comparisons_sha256": sample_digest.hexdigest(),
                           "residual_order": packet["residuals"],
                           "residual_degree_upper_bounds": upper_bounds,
                           "residual_degree_lower_bounds_witnessed_modulo_primes": observed_maximum,
                           "output_degree_upper_bound": degree,
                           "output_degree_lower_bound_witnessed_modulo_primes": observed_output_maximum,
                           "ray_checks": ray_records, "status": "PASS"})
            records.append(record)
    receipt = {
        "status": "PASS", "review_type": "Internal AI-assisted independent implementation check",
        "script": "code/independent_check.py", "script_sha256": sha256(Path(__file__).read_bytes()),
        "imports_project_code": False, "uses_python_assert": False,
        "python": sys.version.split()[0], "seed": SEED, "primes": list(PRIMES),
        "random_scalar_cases_per_prime": RANDOM_CASES_PER_PRIME,
        "fixed_scalar_cases_per_prime": 4, "rays_per_prime": RAYS_PER_PRIME,
        "scalar_residual_and_output_comparisons": comparison_count,
        "coefficient_authentication": coefficient_receipt, "circuits": records,
        "degree_method": "Upper bounds from explicit cancellation identities; lower bounds from nonzero coefficients on exact univariate rays modulo primes, using authentic integer ports.",
        "limits": "Finite diagnostics and arithmetic degree certificates do not prove soundness/completeness or the compiler/calibration theorem. This is not external or proof-assistant certification and does not test Con(ZFC).",
    }
    target = ROOT / "certificates" / "INDEPENDENT_FORMULA_CHECK.json"
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": receipt["status"], "circuits": len(records),
                      "scalar_residual_and_output_comparisons": comparison_count,
                      "exact_degrees": [24, 26, 30],
                      "receipt": str(target)}, indent=2))


if __name__ == "__main__":
    try:
        run()
    except (ValueError, OSError, KeyError, TypeError) as error:
        print("INDEPENDENT CHECK FAILED: " + str(error), file=sys.stderr)
        sys.exit(1)
