#!/usr/bin/env python3
"""Independent transcription check of a direct-majorant nine-variable DAG."""
from collections import Counter
from functools import lru_cache
from pathlib import Path
import hashlib
import json
import sys
from independent_ring import Ring
from audit_laurent_majorant import add, mul, subtract, const, var, require


def fingerprints(packet):
    result = []
    for index, node in enumerate(packet["nodes"]):
        kind = node["kind"]
        if kind in ("variable", "fixed"):
            value = [kind, node["name"]]
        elif kind == "literal":
            value = [kind, node["value"]]
        else:
            require(kind in ("add", "sub", "mul"), "unknown node")
            require(0 <= node["left"] < index and 0 <= node["right"] < index, "forward dependency")
            pair = [result[node["left"]], result[node["right"]]]
            if kind in ("add", "mul"):
                pair.sort()
            value = [kind]+pair
        result.append(hashlib.sha256(json.dumps(value, separators=(",", ":")).encode()).hexdigest())
    return result


def main():
    component = Path(sys.argv[1])
    raw = (component / "equation9.json").read_bytes()
    new = json.loads(raw)
    oldraw = (component / "upstream/nine71.json").read_bytes()
    old = json.loads(oldraw)
    radical = json.loads((component / "data/radical.json").read_text())
    require(new["source_baseline_sha256"] == hashlib.sha256(oldraw).hexdigest(), "source hash")
    for key in ("variables", "domain", "coherent_tuple", "coefficient_recipes",
                "W", "Kcode", "Ecode", "base_scale_exponent", "threshold_scale_exponent",
                "threshold_B_power", "threshold_b_power", "source_sha256", "layout_sha256"):
        require(new[key] == old[key], "changed inherited metadata: " + key)
    nf, of = fingerprints(new), fingerprints(old)
    compared = []
    for name, index in new["named_nodes"].items():
        if name in old["named_nodes"]:
            require(nf[index] == of[old["named_nodes"][name]], "changed source expression: " + name)
            compared.append(name)
    nn = new["named_nodes"]
    require(new["variables"] == ["b", "g", "h", "s", "w", "C", "i", "j", "n"], "nine variables")
    variables = {node["name"]: k for k, node in enumerate(new["nodes"]) if node["kind"] == "variable"}

    # Reconstruct the actual 654-term majorant from its DAG cut, independently.
    cuts = {nn["A"]: var(0), nn["C"]: var(1), variables["i"]: var(2), nn["Z"]: var(3)}
    @lru_cache(None)
    def poly(k):
        if k in cuts:
            return cuts[k]
        n = new["nodes"][k]
        if n["kind"] == "literal":
            return const(n["value"])
        require(n["kind"] in ("add", "sub", "mul"), "unexpected majorant input")
        a, b = poly(n["left"]), poly(n["right"])
        return add(a, b) if n["kind"] == "add" else subtract(a, b) if n["kind"] == "sub" else mul(a, b)
    expected = {tuple(e): int(c) for e, c in radical["T_terms"]}
    require(poly(nn["Pstar"]) == expected, "literal majorant transcription")
    require(nn["Pstar"] == nn["direct_V1"], "unexpected correction term")

    # Verify Z and the entire finalizer using small polynomial cuts.
    def ring_cut(target, cuts):
        @lru_cache(None)
        def value(k):
            if k in cuts:
                return Ring.variable(cuts[k])
            n = new["nodes"][k]
            if n["kind"] == "literal":
                return Ring.numeral(n["value"])
            require(n["kind"] in ("add", "sub", "mul"), "unexpected finalizer input")
            a, b = value(n["left"]), value(n["right"])
            return a+b if n["kind"] == "add" else a-b if n["kind"] == "sub" else a*b
        return value(target)
    J, C, B1 = [Ring.variable(n) for n in ("j", "C", "B1")]
    require(ring_cut(nn["Z"], {variables["j"]: "j", nn["C"]: "C", nn["B1"]: "B1"})
            == B1+(J-1)*C, "Z substitution and positive-coordinate convention")
    cuts = {nn[name]: name for name in ("E0", "Omega", "V0", "a0", "a1", "Pstar", "C")}
    E0, om, v0, a0, rad, p, c = [Ring.variable(n) for n in ("E0", "Omega", "V0", "a0", "a1", "Pstar", "C")]
    sigma = 65536*c**7
    a1 = sigma*sigma*rad
    theta = E0-om*(v0+p)
    expected_final = (theta*theta-om*om*(a0+a1))**2-4*(om**4)*a0*a1
    require(ring_cut(new["output"], cuts) == expected_final, "full norm finalizer")

    live = set()
    def visit(k):
        if k in live:
            return
        live.add(k)
        n = new["nodes"][k]
        if n["kind"] in ("add", "sub", "mul"):
            visit(n["left"]); visit(n["right"])
    # A deep recursive DFS would depend on Python recursion settings, so walk backwards.
    live.add(new["output"])
    for k in range(len(new["nodes"])-1, -1, -1):
        if k not in live:
            continue
        node = new["nodes"][k]
        if node["kind"] in ("add", "sub", "mul"):
            live.update((node["left"], node["right"]))
    require(len(live) == len(new["nodes"]), "dead nodes")
    counts = Counter(n["kind"] for n in new["nodes"] if n["kind"] in ("add", "sub", "mul"))
    require(dict(counts) == new["operation_counts"] == {"mul": 923, "sub": 20, "add": 810}, "gate breakdown")
    require(sum(counts.values()) == new["total_operations"] == 1753, "gate count")
    require(new["exact_degree"] == 1158228, "declared degree matches independent certificate")
    result = {
        "status": "PASS", "equation_sha256": hashlib.sha256(raw).hexdigest(),
        "source_sha256": hashlib.sha256(oldraw).hexdigest(),
        "unchanged_named_source_expressions": compared,
        "majorant_terms_checked": len(expected), "finalizer_exact_identity": True,
        "Z_substitution_checked": True, "variables": 9, "operations": 1753,
        "operation_counts": dict(counts), "all_nodes_live": True,
        "scope": "Exact literal circuit transcription, inherited expression identities, variable domain, and operation count. Degree and positivity are checked by the separate four-variable audit."
    }
    dest = Path(sys.argv[2]) if len(sys.argv) > 2 else component / "certificates/INDEPENDENT_DAG_AUDIT.json"
    dest.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
