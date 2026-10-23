#!/usr/bin/env python3
"""Explicit domain translations of the primary degree-24 polynomial.

The fifteen nonnegative coordinates use x_positive=1+x_nonnegative.
The sixty unrestricted integer coordinates use
    x_positive=1+x_1^2+x_2^2+x_3^2+x_4^2.
The latter existence equivalence is Lagrange's four-square theorem.
These standard translations clarify the domain; they are not frontier
claims.  All substitutions are emitted as literal division-free gates.

No project builder or evaluator is imported.  The program independently
validates circuit structure and liveness, authenticates the fixed payloads,
and compares the translated circuit with the primary circuit evaluated at
the substituted coordinates.  Exact finite differences on the all-equal
ray provide degree lower bounds.  The upper bounds follow from the degree
24 parent and substitution degrees one and two.
"""

from collections import Counter
import gzip
import hashlib
import json
from math import factorial
from pathlib import Path
import random
import sys


ROOT = Path(__file__).resolve().parents[1]
PARENT_PATH = ROOT / "circuits" / "p15_degree24.json"
PRIMES = (65537, 1000003, 1000000007)
SEED = 0xD04A1024
RANDOM_CASES_PER_PRIME = 96
ALIASES = {"beta": "beta", "K0": "K", "MC": "MC", "MF": "MF_source"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def resolve_local(path):
    result = path.resolve()
    require(result.is_relative_to(ROOT), "Path escapes submission: " + str(path))
    return result


def live_set(rows, outputs):
    needed = set(outputs)
    for name, _op, left, right in reversed(rows):
        if name in needed:
            needed.update((left, right))
    return {row[0] for row in rows if row[0] in needed}, needed


def validate(packet):
    witnesses = packet["witnesses"]
    ports = packet["fixed_numerals"]
    require(len(witnesses) == len(set(witnesses)), "Repeated witness name")
    require(ports == list(ALIASES) and packet["port_aliases"] == ALIASES,
            "Unexpected or mixed fixed coefficient ports")
    require(not set(witnesses).intersection(ports), "A witness shadows a fixed port")
    available = set(witnesses + ports)
    rows = packet["source"]
    for row in rows:
        require(isinstance(row, list) and len(row) == 4, "Malformed circuit gate")
        name, operation, left, right = row
        require(isinstance(name, str) and name not in available, "Repeated or invalid gate name")
        require(operation in ("+", "-", "*"), "Unsupported gate operation")
        for value in (left, right):
            require(type(value) is int or isinstance(value, str) and value in available,
                    "Invalid or forward reference: " + str(value))
        available.add(name)
    require(packet["output"] in available, "Unknown circuit output")
    require(all(name in available for name in packet["residuals"]), "Unknown residual")
    require(packet["operations"] == len(rows), "Operation count mismatch")
    require(packet["operation_breakdown"] == dict(Counter(row[1] for row in rows)),
            "Operation breakdown mismatch")
    used, needed = live_set(rows, [packet["output"]])
    require(len(used) == len(rows), "A literal gate is unused")
    require(set(witnesses + ports) <= needed, "An advertised witness or fixed port is unused")
    core, _ = live_set(rows, packet["residuals"])
    require(packet["residual_evaluator_operations"] == len(core), "Residual evaluator count mismatch")


def coefficients(parent):
    binding_path = resolve_local(PARENT_PATH.parent / parent["coefficient_binding_file"])
    binding = read_json(binding_path)
    entries = binding["materialization"]["files"]
    require(len(entries) == 4 and {entry["port"] for entry in entries} == set(ALIASES.values()),
            "A complete four-port coefficient tuple is required")
    originals = {}
    receipt = []
    for entry in entries:
        path = resolve_local(binding_path.parent / entry["file"])
        compressed = path.read_bytes()
        require(sha256(compressed) == entry["gzip_sha256"], "Compressed coefficient hash mismatch")
        raw = gzip.decompress(compressed)
        require(sha256(raw) == entry["sha256"], "Raw coefficient hash mismatch")
        require(len(raw) == entry["raw_bytes"] and len(compressed) == entry["gzip_bytes"],
                "Coefficient byte count mismatch")
        value = int.from_bytes(raw, "little", signed=False)
        require(value > 0 and value.bit_length() == entry["bits"], "Coefficient bit length mismatch")
        originals[entry["port"]] = value
        receipt.append({"port": entry["port"], "sha256": sha256(raw),
                        "gzip_sha256": sha256(compressed)})
    return {alias: originals[port] for alias, port in ALIASES.items()}, {
        "binding_file": str(binding_path.relative_to(ROOT)),
        "binding_sha256": sha256(binding_path.read_bytes()),
        "instance": binding["instance"], "payloads": receipt,
    }


def build(parent, integer_domain):
    prefix = []
    replacement = {}
    variables = []
    recipes = []
    for old in parent["witnesses"]:
        positive = "positive_" + old
        replacement[old] = positive
        if integer_domain:
            group = [old + "_" + str(index) for index in range(1, 5)]
            variables.extend(group)
            squares = []
            for index, variable in enumerate(group, 1):
                square = "domain_" + old + "_square_" + str(index)
                prefix.append([square, "*", variable, variable])
                squares.append(square)
            first_sum = "domain_" + old + "_sum_2"
            second_sum = "domain_" + old + "_sum_3"
            last_sum = "domain_" + old + "_sum_4"
            prefix.extend([[first_sum, "+", squares[0], squares[1]],
                           [second_sum, "+", first_sum, squares[2]],
                           [last_sum, "+", second_sum, squares[3]],
                           [positive, "+", 1, last_sum]])
            expression = "1 + " + " + ".join(name + "^2" for name in group)
        else:
            group = [old]
            variables.extend(group)
            prefix.append([positive, "+", 1, old])
            expression = "1 + " + old
        recipes.append({"positive_coordinate": old, "translated_witnesses": group,
                        "positive_coordinate_gate": positive, "expression": expression})
    prefix_names = {row[0] for row in prefix}
    require(not prefix_names.intersection(row[0] for row in parent["source"]),
            "Domain prefix collides with a parent gate")
    rows = prefix + [[name, operation, replacement.get(left, left), replacement.get(right, right)]
                     for name, operation, left, right in parent["source"]]
    degree = 48 if integer_domain else 24
    count = 60 if integer_domain else 15
    domain = "unrestricted integers" if integer_domain else "nonnegative integers"
    packet = {
        "name": "sixty_integer_degree_48" if integer_domain else "fifteen_nonnegative_degree_24",
        "domain": domain, "witnesses": variables,
        "fixed_numerals": parent["fixed_numerals"],
        "coefficient_binding_file": parent["coefficient_binding_file"],
        "port_aliases": parent["port_aliases"],
        "source": rows, "residuals": parent["residuals"], "output": parent["output"],
        "exact_degree": degree, "operations": len(rows),
        "operation_breakdown": dict(Counter(row[1] for row in rows)),
        "residual_evaluator_operations": len(live_set(rows, parent["residuals"])[0]),
        "degree_certificate_only": False,
        "source_positive_circuit": PARENT_PATH.name,
        "source_positive_circuit_sha256": sha256(PARENT_PATH.read_bytes()),
        "domain_translation": {
            "coordinates": recipes, "added_operations": len(prefix),
            "explanation": (
                "Each positive coordinate is one plus a sum of four integer squares. "
                "Every positive integer has such a representation by Lagrange's four-square theorem, "
                "so the existence of an integer zero is equivalent to a positive zero of the parent."
                if integer_domain else
                "Each positive coordinate is one plus a nonnegative coordinate. "
                "This coordinatewise bijection preserves existence of a zero."
            ),
            "degree_explanation": (
                "Homogeneous quadratic substitutions give degree at most 48. "
                "On the all-equal ray the degree-48 coefficient is 36*4^24, which is nonzero."
                if integer_domain else
                "An invertible affine translation preserves total degree 24. "
                "On the all-equal ray the degree-24 coefficient is 36."
            ),
            "frontier_claim": False,
        },
        "proof": "../report/report.pdf",
        "status": "Standard domain translation of the primary positive equation; ordinary mathematical proof, no new end-to-end proof-assistant certificate.",
    }
    require(len(variables) == count, "Incorrect witness count after translation")
    require(len(prefix) == (120 if integer_domain else 15), "Incorrect number of substitution gates")
    require(packet["operations"] == (210 if integer_domain else 105), "Incorrect translated operation count")
    validate(packet)
    return packet


def evaluate(packet, witnesses, fixed, modulus):
    values = {name: value % modulus for name, value in fixed.items()}
    values.update({name: value % modulus for name, value in witnesses.items()})
    for name, operation, left, right in packet["source"]:
        x = left if type(left) is int else values[left]
        y = right if type(right) is int else values[right]
        if operation == "+":
            value = x + y
        elif operation == "-":
            value = x - y
        elif operation == "*":
            value = x * y
        else:
            raise ValueError("Unsupported operation during evaluation")
        values[name] = value % modulus
    return [values[name] for name in packet["residuals"]] + [values[packet["output"]]]


def substitute(assignment, parent, integer_domain):
    # This is intentionally implemented from the mathematical formulas,
    # independently of the generated prefix or its recipe metadata.
    if integer_domain:
        return {name: 1 + sum(assignment[name + "_" + str(index)] ** 2 for index in range(1, 5))
                for name in parent["witnesses"]}
    return {name: 1 + assignment[name] for name in parent["witnesses"]}


def top_coefficient_on_equal_ray(packet, fixed, prime):
    degree = packet["exact_degree"]
    values = [evaluate(packet, dict.fromkeys(packet["witnesses"], parameter), fixed, prime)[-1]
              for parameter in range(degree + 1)]
    while len(values) > 1:
        values = [(right - left) % prime for left, right in zip(values, values[1:])]
    return values[0] * pow(factorial(degree), -1, prime) % prime


def check_translation(parent, packet, fixed, integer_domain):
    rng = random.Random(SEED + (60 if integer_domain else 15))
    digest = hashlib.sha256()
    comparisons = 0
    sample_count = 0
    ray_checks = []
    for prime in PRIMES:
        names = packet["witnesses"]
        samples = [dict.fromkeys(names, 0), dict.fromkeys(names, 1)]
        if integer_domain:
            samples.append(dict.fromkeys(names, -1))
        else:
            samples.append({name: index for index, name in enumerate(names)})
        samples.extend({name: rng.randrange(-prime, prime + 1) if integer_domain else rng.randrange(2 * prime + 1)
                        for name in names} for _ in range(RANDOM_CASES_PER_PRIME))
        for index, assignment in enumerate(samples):
            positive = substitute(assignment, parent, integer_domain)
            require(all(value > 0 for value in positive.values()), "Substitution did not produce positive coordinates")
            expected = evaluate(parent, positive, fixed, prime)
            observed = evaluate(packet, assignment, fixed, prime)
            require(observed == expected,
                    "Substitution mismatch at prime " + str(prime) + ", case " + str(index))
            digest.update(json.dumps(observed, separators=(",", ":")).encode("ascii"))
            comparisons += len(observed)
            sample_count += 1
        expected_leader = (36 * 4 ** 24 if integer_domain else 36) % prime
        observed_leader = top_coefficient_on_equal_ray(packet, fixed, prime)
        require(observed_leader == expected_leader and observed_leader != 0,
                "Equal-ray degree certificate failed at prime " + str(prime))
        ray_checks.append({"prime": prime, "degree": packet["exact_degree"],
                           "observed_leading_coefficient": observed_leader,
                           "expected_leading_coefficient": expected_leader,
                           "method": "Exact degree-th finite difference divided by degree factorial"})
    return {"status": "PASS", "domain": packet["domain"],
            "witness_count": len(packet["witnesses"]), "exact_degree": packet["exact_degree"],
            "operations": packet["operations"], "operation_breakdown": packet["operation_breakdown"],
            "added_operations": packet["domain_translation"]["added_operations"],
            "residual_evaluator_operations": packet["residual_evaluator_operations"],
            "all_literal_gates_and_witnesses_live": True,
            "modular_cases": sample_count, "residual_and_output_comparisons": comparisons,
            "modular_comparisons_sha256": digest.hexdigest(), "degree_ray_checks": ray_checks}


def run():
    parent = read_json(PARENT_PATH)
    validate(parent)
    require(parent["domain"] == "strictly positive integers" and len(parent["witnesses"]) == 15,
            "Expected the fifteen-positive-variable parent")
    require(parent["exact_degree"] == 24 and parent["operations"] == 90,
            "Expected the degree-24, 90-operation primary parent")
    require(parent["degree_certificate_only"] is False, "Primary parent cannot be a degree-only circuit")
    fixed, coefficient_receipt = coefficients(parent)
    outputs = []
    for integer_domain, filename in ((False, "p15_nonnegative_degree24.json"),
                                     (True, "p60_integer_degree48.json")):
        packet = build(parent, integer_domain)
        record = check_translation(parent, packet, fixed, integer_domain)
        path = ROOT / "circuits" / filename
        encoded = (json.dumps(packet, indent=2) + "\n").encode("utf-8")
        path.write_bytes(encoded)
        record.update({"file": str(path.relative_to(ROOT)), "sha256": sha256(encoded)})
        outputs.append(record)
    receipt = {
        "status": "PASS", "script": "code/domain_translations.py",
        "script_sha256": sha256(Path(__file__).read_bytes()),
        "source_positive_circuit": str(PARENT_PATH.relative_to(ROOT)),
        "source_positive_circuit_sha256": sha256(PARENT_PATH.read_bytes()),
        "coefficient_authentication": coefficient_receipt,
        "primes": list(PRIMES), "seed": SEED,
        "random_cases_per_prime_per_translation": RANDOM_CASES_PER_PRIME,
        "imports_project_code": False, "uses_python_assert": False,
        "translations": outputs,
        "proof_scope": "Nonnegative translation is an affine bijection. Integer translation is surjective by Lagrange's four-square theorem. Degree upper bounds use the independently established parent degree; equal-ray leading coefficients prove the lower bounds.",
        "limits": "Standard domain clarification, not a frontier claim. Modular tests are implementation diagnostics, not a substitute for the existence-equivalence or inherited compiler proofs.",
    }
    target = ROOT / "certificates" / "DOMAIN_TRANSLATIONS.json"
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "translations": [
        {"file": item["file"], "witnesses": item["witness_count"],
         "domain": item["domain"], "degree": item["exact_degree"],
         "operations": item["operations"]} for item in outputs],
        "receipt": str(target)}, indent=2))


if __name__ == "__main__":
    try:
        run()
    except (ValueError, OSError, KeyError, TypeError) as error:
        print("DOMAIN TRANSLATION CHECK FAILED: " + str(error), file=sys.stderr)
        sys.exit(1)
