#!/usr/bin/env python3
"""Share the split116 base powers globally, with an exact rewrite receipt.

The certificate checks fixed exponent identities and a structural remap of
every other gate. It therefore describes an identity over commutative rings,
not just equality at the modular diagnostic assignments. Lean checking of
this particular transformation remains a separate task.
"""
import argparse
import collections
import copy
import gzip
import hashlib
import json
from pathlib import Path

from review_proposal_frontier import audit, require

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "candidates/split116-compact/compact54-sharp"
DEST = ROOT / "candidates/split116-joint-powers"
PINS = {
    "positive": "c3d16f56ca868cf1a0773889ed06e89a865ea41057497467325ef2c09e7de96f",
    "natural": "cb0caa3a14370e9a5d43be9cabbfef86f92481301b09f4fd7bc7c19f550804db",
}
HELPERS = {114: (57, 57), 256: (220, 36), 565: (522, 43),
           1044: (522, 522), 1078: (1044, 34)}
SPECIAL = {522: (266, 256), 636: (522, 114), 1201: (636, 565), 2279: (1201, 1078)}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(data):
    return (json.dumps(data, indent=2) + "\n").encode()


def powers(body):
    base = body["named_nodes"]["B"]
    exponents = {base: 1}
    for i, node in enumerate(body["nodes"]):
        if node["kind"] == "mul" and node["left"] in exponents and node["right"] in exponents:
            exponents[i] = exponents[node["left"]] + exponents[node["right"]]
    required = set()
    for i, node in enumerate(body["nodes"]):
        if node["kind"] in ("add", "sub", "mul") and i not in exponents:
            required.update(exponents[node[k]] for k in ("left", "right") if node[k] in exponents)
    return base, exponents, required


def transform(parent):
    base, old_powers, required = powers(parent)
    require(len(old_powers) == 108 and len(required) == 86, "parent power inventory")
    nodes = copy.deepcopy(parent["nodes"][:base+1])
    mapping = {i: i for i in range(base+1)}
    by_exponent = {1: base}
    chain = []
    for e in sorted(required | HELPERS.keys()):
        if e == 1:
            continue
        if e in HELPERS or e in SPECIAL:
            a, b = HELPERS.get(e, SPECIAL.get(e))
        else:
            pairs = [(a, e-a) for a in by_exponent if a <= e-a and e-a in by_exponent]
            require(pairs, f"no earlier target decomposition for {e}")
            a, b = min(pairs, key=lambda pair: (max(pair), min(pair)))
        require(a+b == e and a in by_exponent and b in by_exponent, "chain edge")
        index = len(nodes)
        nodes.append(dict(kind="mul", left=by_exponent[a], right=by_exponent[b]))
        by_exponent[e] = index
        chain.append(dict(node=index, exponent=e, left_exponent=a, right_exponent=b))
    for old, e in old_powers.items():
        if e in by_exponent:
            mapping[old] = by_exponent[e]
    for i, node in enumerate(parent["nodes"]):
        if i <= base or i in old_powers:
            continue
        new = dict(node)
        if node["kind"] in ("add", "sub", "mul"):
            new.update(left=mapping[node["left"]], right=mapping[node["right"]])
        mapping[i] = len(nodes)
        nodes.append(new)
    result = copy.deepcopy(parent)
    result.update(nodes=nodes, output=mapping[parent["output"]],
                  named_nodes={k: mapping[v] for k, v in parent["named_nodes"].items()},
                  power_method="global joint addition chain", exact_degree=1910404,
                  fixed_binding="../split116-compact/compact54-sharp/fixed/BINDING.json")
    counts = collections.Counter(n["kind"] for n in nodes if n["kind"] in ("add", "sub", "mul"))
    result.update(operation_counts=dict(sorted(counts.items())), total_operations=sum(counts.values()))
    certificate = dict(base_node=base, old_power_nodes=len(old_powers)-1,
                       new_power_nodes=len(chain), required_exponents=sorted(required),
                       chain=chain, retained_remap={str(k): v for k, v in sorted(mapping.items())
                         if k not in old_powers or old_powers[k] in required})
    return result, certificate


def verify_remap(parent, child, certificate):
    """Independent exponent labels and retained-gate correspondence check."""
    base, old_powers, required = powers(parent)
    child_base, new_powers, child_required = powers(child)
    require(child_base == base and child_required == required, "same external powers")
    require(len(new_powers) == 91, "ninety new power multiplications")
    mapping = {int(k): v for k, v in certificate["retained_remap"].items()}
    covered = set()
    for i, node in enumerate(parent["nodes"]):
        if i in old_powers:
            if old_powers[i] in required:
                require(new_powers[mapping[i]] == old_powers[i], "power identity")
            continue
        new = dict(node)
        if node["kind"] in ("add", "sub", "mul"):
            new.update(left=mapping[node["left"]], right=mapping[node["right"]])
        require(child["nodes"][mapping[i]] == new, "retained gate identity")
        covered.add(mapping[i])
    require(covered | set(new_powers) == set(range(len(child["nodes"]))), "complete new coverage")
    require(child["output"] == mapping[parent["output"]], "output identity")
    require(child["variables"] == parent["variables"] and
            child["coefficient_recipes"] == parent["coefficient_recipes"], "same polynomial leaves")


def evaluate(body, variables, fixed, modulus):
    values = []
    for node in body["nodes"]:
        kind = node["kind"]
        if kind == "variable":
            value = variables[node["name"]]
        elif kind == "fixed":
            value = fixed[node["name"]]
        elif kind == "literal":
            value = node["value"]
        elif kind == "add":
            value = values[node["left"]]+values[node["right"]]
        elif kind == "sub":
            value = values[node["left"]]-values[node["right"]]
        else:
            require(kind == "mul", "operation kind")
            value = values[node["left"]]*values[node["right"]]
        values.append(value % modulus)
    return values[body["output"]]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare generated bytes without writing")
    args = parser.parse_args()
    output, rows = {}, []
    binding_raw = (PARENT/"fixed/BINDING.json").read_bytes()
    fixed = {}
    for leaf in json.loads(binding_raw)["live_fixed_leaves"]:
        raw = gzip.decompress((PARENT/leaf["path"]).read_bytes())
        require(sha(raw) == leaf["sha256"], "fixed integer identity")
        fixed[leaf["name"]] = leaf["sign"]*int.from_bytes(raw, "little")
    for domain, operations in (("positive", 456), ("natural", 463)):
        name = f"split_116_{domain}.json"
        raw = (PARENT/"generated"/name).read_bytes()
        require(sha(raw) == PINS[domain], "parent DAG pin")
        parent = json.loads(raw)
        child, receipt = transform(parent)
        verify_remap(parent, child, receipt)
        require(child["total_operations"] == operations, "reduced operation count")
        for modulus in (65537, 1000000007, 2147483647):
            for seed in range(12):
                variables = {v: seed*(i+3)+(domain == "positive") for i, v in enumerate(child["variables"])}
                require(evaluate(parent, variables, fixed, modulus) == evaluate(child, variables, fixed, modulus),
                        "modular diagnostic")
        output[name] = encoded(child)
        receipt.update(parent_sha256=sha(raw), child_sha256=sha(output[name]),
                       fixed_binding_sha256=sha(binding_raw), modular_diagnostics=36,
                       scope="Exact fixed-exponent identities and structural gate remap; Lean transformation proof pending.")
        output[f"{domain}_rewrite.json"] = encoded(receipt)
        rows.append(dict(domain=domain, operations=operations, power_multiplications=90,
                         removed_operations=17, exact_degree=1910404, sha256=sha(output[name])))
    output["REVIEW.json"] = encoded(dict(status="PASS", circuits=rows,
        degree_reason="Output polynomial identical to pinned parent by the power/remap certificate; parent cancellation-aware certificate transfers.",
        fixed_binding="../split116-compact/compact54-sharp/fixed/BINDING.json"))
    output["MANIFEST.json"] = encoded({name: sha(raw) for name, raw in sorted(output.items())})
    for name, raw in output.items():
        target = DEST/name
        if args.check:
            require(target.read_bytes() == raw, f"rebuild {name}")
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
    for domain, operations in (("positive", 456), ("natural", 463)):
        audit((f"../candidates/split116-joint-powers/split_116_{domain}.json",
               9, "+" if domain == "positive" else "N", 1910404, operations))
    print(json.dumps(dict(status="PASS", files=len(output), circuits=rows), indent=2))


if __name__ == "__main__":
    main()
