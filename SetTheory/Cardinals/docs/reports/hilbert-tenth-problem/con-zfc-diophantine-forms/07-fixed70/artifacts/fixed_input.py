#!/usr/bin/env python3
"""Fixed-input Diophantine circuits; Python 3 standard library only.

The coefficients must come from the stated helical compiler. Structural and
algebraic verification of these circuits does not certify arbitrary coefficients
as a compiler instance, and does not decide ZFC consistency.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from random import Random

BASE84 = [
  [
    "tau_square",
    "*",
    "tau_root",
    "tau_root"
  ],
  [
    "repunit",
    "*",
    "Bm1",
    "Jrep"
  ],
  [
    "q",
    "+",
    "repunit",
    1
  ],
  [
    "Lbig",
    "*",
    "q",
    "q"
  ],
  [
    "n2",
    "*",
    "Lbig",
    "q"
  ],
  [
    "wn2",
    "*",
    "w",
    "q"
  ],
  [
    "sn2",
    "*",
    "s",
    "n2"
  ],
  [
    "UM",
    "*",
    "wn2",
    "sn2"
  ],
  [
    "R10b",
    "+",
    "eta",
    "zeta"
  ],
  [
    "ksn2",
    "*",
    "R10b",
    "sn2"
  ],
  [
    "first_root_base",
    "*",
    "UM",
    "ksn2"
  ],
  [
    "first_next",
    "+",
    "first_root_base",
    "R10b"
  ],
  [
    "first_product",
    "*",
    "first_root_base",
    "first_next"
  ],
  [
    "norm_first",
    "-",
    "tau_square",
    "first_product"
  ],
  [
    "R10a",
    "+",
    "ksn2",
    "eta"
  ],
  [
    "R12",
    "+",
    "UM",
    "sn2"
  ],
  [
    "cam2",
    "*",
    "R10a",
    "R12"
  ],
  [
    "D1",
    "+",
    "wn2",
    "cam2"
  ],
  [
    "gamma_sum",
    "+",
    "rho",
    "sigma"
  ],
  [
    "a4",
    "*",
    4,
    "R12"
  ],
  [
    "a4m5",
    "+",
    "a4",
    3
  ],
  [
    "gam",
    "*",
    "gamma_sum",
    "a4m5"
  ],
  [
    "R14",
    "+",
    "D1",
    "gam"
  ],
  [
    "L15",
    "*",
    "R14",
    "R14"
  ],
  [
    "a_square",
    "*",
    "R12",
    "R12"
  ],
  [
    "A",
    "+",
    "a_square",
    "a4m5"
  ],
  [
    "c2",
    "*",
    "R10a",
    "R10a"
  ],
  [
    "Ac2",
    "*",
    "A",
    "c2"
  ],
  [
    "norm_main",
    "-",
    "L15",
    "Ac2"
  ],
  [
    "norm_pair",
    "*",
    "norm_first",
    "norm_main"
  ],
  [
    "q_minus_F",
    "-",
    "q",
    "F"
  ],
  [
    "q_minus_FZ",
    "-",
    "q_minus_F",
    "Z"
  ],
  [
    "C_after_alpha",
    "-",
    "q_minus_FZ",
    "alpha"
  ],
  [
    "scaled_t",
    "*",
    "twice_cell_bits",
    "x"
  ],
  [
    "marked_rhs",
    "-",
    "C_after_alpha",
    "scaled_t"
  ],
  [
    "W",
    "-",
    "marked_rhs",
    "Z"
  ],
  [
    "odd_index",
    "+",
    "scaled_t",
    "inner_bits"
  ],
  [
    "index_product",
    "*",
    "delta",
    "A"
  ],
  [
    "index_rhs",
    "+",
    "odd_index",
    "index_product"
  ],
  [
    "difference_multiple",
    "*",
    "index_rhs",
    "R12"
  ],
  [
    "exponent_partial",
    "+",
    "W",
    "difference_multiple"
  ],
  [
    "modulus_multiple",
    "*",
    "rho",
    "a4m5"
  ],
  [
    "exponent_rhs",
    "+",
    "exponent_partial",
    "modulus_multiple"
  ],
  [
    "mu2",
    "*",
    "exponent_rhs",
    "exponent_rhs"
  ],
  [
    "kappa2",
    "*",
    "index_rhs",
    "index_rhs"
  ],
  [
    "scaled_kappa2",
    "*",
    "A",
    "kappa2"
  ],
  [
    "norm_input",
    "-",
    "mu2",
    "scaled_kappa2"
  ],
  [
    "norm_triple",
    "*",
    "norm_pair",
    "norm_input"
  ],
  [
    "aux_y2",
    "*",
    "y_aux",
    "y_aux"
  ],
  [
    "hpm1",
    "*",
    "h",
    "UM"
  ],
  [
    "index_difference",
    "-",
    "R10b",
    "hpm1"
  ],
  [
    "gap_product",
    "*",
    "repunit",
    "q_minus_F"
  ],
  [
    "gap",
    "+",
    "gap_product",
    "q_minus_FZ"
  ],
  [
    "Lm1",
    "-",
    "Lbig",
    1
  ],
  [
    "rproduct",
    "*",
    "gap",
    "Lm1"
  ],
  [
    "qMF",
    "*",
    "q",
    "MF"
  ],
  [
    "mask_factor",
    "+",
    "MC",
    "qMF"
  ],
  [
    "mask",
    "*",
    "mask_factor",
    "Jrep"
  ],
  [
    "r_lhs",
    "+",
    "rproduct",
    "mask"
  ],
  [
    "norm_index",
    "-",
    "index_difference",
    "r_lhs"
  ],
  [
    "kinner",
    "+",
    "Kconstant",
    "w"
  ],
  [
    "innerC",
    "*",
    "kinner",
    "marked_rhs"
  ],
  [
    "transport_partial",
    "+",
    "innerC",
    "q_minus_F"
  ],
  [
    "local_rhs",
    "*",
    "transport_quotient",
    "repunit"
  ],
  [
    "norm_transport",
    "-",
    "transport_partial",
    "local_rhs"
  ],
  [
    "L16",
    "*",
    "f",
    "f"
  ],
  [
    "auxiliary_Tf",
    "*",
    "auxiliary_quotient",
    "f"
  ],
  [
    "auxiliary_Tf_minus_one",
    "-",
    "auxiliary_Tf",
    1
  ],
  [
    "auxiliary_c_Tf",
    "*",
    "R10a",
    "auxiliary_Tf_minus_one"
  ],
  [
    "auxiliary_R_f2",
    "*",
    "r_lhs",
    "L16"
  ],
  [
    "aux_u_rhs",
    "-",
    "auxiliary_c_Tf",
    "auxiliary_R_f2"
  ],
  [
    "H2",
    "*",
    "aux_u_rhs",
    "aux_u_rhs"
  ],
  [
    "aux_square_gap",
    "-",
    "H2",
    "aux_y2"
  ],
  [
    "aux_coefficient_root",
    "*",
    "i",
    "Ac2"
  ],
  [
    "R16",
    "*",
    "aux_coefficient_root",
    "aux_coefficient_root"
  ],
  [
    "scaled_f_square",
    "*",
    "A",
    "L16"
  ],
  [
    "norm_strong",
    "-",
    "scaled_f_square",
    "R16"
  ],
  [
    "L17",
    "*",
    "R16",
    "aux_square_gap"
  ],
  [
    "norm_aux",
    "+",
    "L17",
    "aux_y2"
  ],
  [
    "norm_four",
    "*",
    "norm_triple",
    "norm_aux"
  ],
  [
    "norm_product",
    "*",
    "norm_four",
    "norm_index"
  ],
  [
    "all_units",
    "*",
    "norm_product",
    "norm_transport"
  ],
  [
    "seven_units",
    "*",
    "all_units",
    "norm_strong"
  ],
  [
    "polynomial",
    "-",
    "seven_units",
    "A"
  ]
]
BASE_WITNESSES = ["Jrep","F","alpha","transport_quotient","f","h","i","auxiliary_quotient","s","w","tau_root","eta","zeta","y_aux","Z","delta","rho","sigma"]
PINNED_COMMIT = "cdd582bec13f908df3711fa9e05d1ddac368a5db"
PARENT_URL = "https://github.com/VladimirReshetnikov/ProveIt/blob/" + PINNED_COMMIT + "/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json"
PARENT_FILE_SHA256 = "8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf"

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

def fixed73():
    removed = {
        "gamma_sum", "C_after_alpha", "scaled_t", "marked_rhs", "W",
        "odd_index", "index_product", "index_rhs", "difference_multiple",
        "exponent_partial", "modulus_multiple", "exponent_rhs", "mu2",
        "kappa2", "scaled_kappa2", "norm_input",
    }
    aliases = {"marked_rhs": "C", "gamma_sum": "gamma", "norm_input": "norm_budget"}
    rows = []
    for name, op, x, y in BASE84:
        if name == "norm_triple":
            rows.extend([
                ["C", "+", "Z", "W0"],
                ["budget0", "-", "q_minus_F", "C"],
                ["budget", "-", "budget0", "alpha"],
                ["budget_square", "*", "budget", "budget"],
                ["norm_budget", "+", "budget_square", 1],
            ])
        if name not in removed:
            rows.append([name, op, aliases.get(x, x), aliases.get(y, y)])
    witnesses = [w for w in BASE_WITNESSES if w not in {"delta", "rho", "sigma"}] + ["gamma"]
    return {
        "name": "fixed73",
        "witness_domain": "strictly positive integers",
        "witnesses": witnesses,
        "fixed_numerals": ["Bm1", "Kconstant", "MC", "MF", "W0"],
        "source": rows,
        "output": "polynomial",
        "factor_outputs": [
            "norm_first", "norm_main", "norm_budget", "norm_aux",
            "norm_index", "norm_transport", "norm_strong",
        ],
        "factor_exact_degrees": [22, 18, 2, 60, 7, 2, 46],
        "exact_degree": 157,
        "removed_parent_rows": sorted(removed),
        "scope": (
            "Fixed raw input x=1. Coefficients retain the modified75 compiler; "
            "MF is its shifted source mask, and W0=2^b*B^2. "
            "No global minimality or formal proof-assistant verification is claimed."
        ),
    }

def transparent61():
    # A complete comparison system. q=C+F+alpha ensures both necessary bounds.
    rows = [
        ["C", "+", "Z", "W0"],
        ["q0", "+", "C", "F"],
        ["q", "+", "q0", "alpha"],
        ["rep", "*", "Bm1", "J"],
        ["qm1", "-", "q", 1],
        ["q2", "*", "q", "q"],
        ["q3", "*", "q2", "q"],
        ["X", "*", "w", "q3"],
        ["Y", "*", "s", "q3"],
        ["E", "*", "X", "Y"],
        ["k", "+", "eta", "zeta"],
        ["kY", "*", "k", "Y"],
        ["c", "+", "kY", "eta"],
        ["a", "+", "E", "Y"],
        ["ac", "*", "a", "c"],
        ["H0", "*", 4, "a"],
        ["H", "+", "H0", 3],
        ["gH", "*", "gamma", "H"],
        ["D0", "+", "X", "ac"],
        ["D", "+", "D0", "gH"],
        ["a2", "*", "a", "a"],
        ["Delta", "+", "a2", "H"],
        ["c2", "*", "c", "c"],
        ["D2", "*", "D", "D"],
        ["Dc2", "*", "Delta", "c2"],
        ["norm_main", "-", "D2", "Dc2"],
        ["L", "*", "E", "kY"],
        ["Lk", "+", "L", "k"],
        ["Lp", "*", "L", "Lk"],
        ["tau2", "*", "tau", "tau"],
        ["norm_first", "-", "tau2", "Lp"],
        ["qF", "*", "q", "F"],
        ["gap0", "-", "q2", "Z"],
        ["gap", "-", "gap0", "qF"],
        ["q2m1", "-", "q2", 1],
        ["Rp", "*", "gap", "q2m1"],
        ["qMF", "*", "q", "MF"],
        ["mask0", "+", "MC", "qMF"],
        ["mask", "*", "mask0", "J"],
        ["R", "+", "Rp", "mask"],
        ["hE", "*", "h", "E"],
        ["idx0", "-", "k", "hE"],
        ["norm_index", "-", "idx0", "R"],
        ["KX", "+", "Kconstant", "X"],
        ["transport_lhs", "*", "KX", "C"],
        ["zqm", "*", "z", "qm1"],
        ["transport_rhs", "+", "F", "zqm"],
        ["ic2", "*", "i", "c2"],
        ["ic22", "*", "ic2", "ic2"],
        ["f2", "*", "f", "f"],
        ["f2m1", "-", "f2", 1],
        ["Kaux", "*", "Delta", "f2m1"],
        ["jc", "*", "j", "c"],
        ["U", "-", "jc", "R"],
        ["of", "*", "o", "f"],
        ["V", "-", "of", "c"],
        ["V2", "*", "V", "V"],
        ["y2", "*", "y", "y"],
        ["Vgap", "-", "V2", "y2"],
        ["aux0", "*", "Kaux", "Vgap"],
        ["norm_aux", "+", "aux0", "y2"],
    ]
    comparisons = [
        ["rep", "qm1"],
        ["transport_lhs", "transport_rhs"],
        ["norm_first", 1],
        ["norm_index", 1],
        ["norm_main", 1],
        ["ic22", "Kaux"],
        ["norm_aux", 1],
        ["U", "V"],
    ]
    witnesses = [
        "J", "F", "alpha", "z", "Z", "f", "h", "i", "j", "o",
        "s", "w", "tau", "eta", "zeta", "gamma", "y",
    ]
    return {
        "name": "transparent61",
        "witness_domain": "strictly positive integers",
        "witnesses": witnesses,
        "fixed_numerals": ["Bm1", "Kconstant", "MC", "MF", "W0"],
        "source": rows,
        "comparisons": comparisons,
        "residual_degree_bounds": [1, 5, 26, 9, 22, 22, 28, 6],
        "sum_of_squares_exact_degree": 56,
        "scope": (
            "Symmetric q^3 scales, eight literal comparisons, fixed marker. "
            "Auxiliary coefficient is Delta*(f^2-1); the strong comparison "
            "makes it equal to (i*c^2)^2 at every zero."
        ),
    }

def fixed71():
    """Use a signed repunit factor and recover its sign after dyadic decoding."""
    packet = fixed73()
    replaced = {
        "repunit", "q", "q_minus_F", "q_minus_FZ", "C",
        "budget0", "budget", "budget_square", "norm_budget",
    }
    prefix = [
        ["C", "+", "Z", "W0"],
        ["q_minus_F", "+", "C", "alpha"],
        ["q", "+", "q_minus_F", "F"],
        ["q_minus_FZ", "-", "q_minus_F", "Z"],
        ["repunit", "-", "q", 1],
        ["base_multiple", "*", "Bm1", "Jrep"],
        ["norm_repunit", "-", "q", "base_multiple"],
    ]
    rows = prefix + [
        [name, op,
         "norm_repunit" if x == "norm_budget" else x,
         "norm_repunit" if y == "norm_budget" else y]
        for name, op, x, y in packet["source"] if name not in replaced
    ]
    packet.update(
        name="fixed71", source=rows, exact_degree=156,
        factor_outputs=["norm_repunit" if x == "norm_budget" else x
                        for x in packet["factor_outputs"]],
        factor_exact_degrees=[22, 18, 1, 60, 7, 2, 46],
        scope=(
            "Fixed raw input x=1 with actual modified75 compiler coefficients. "
            "The fixed marker implies q>W0>=2B^2. The factor q-(B-1)J is initially "
            "+/-1; its negative sign is excluded only after proving q is dyadic. "
            "No global minimality or formal proof-assistant verification is claimed."
        ),
    )
    return packet

def fixed70():
    """Reuse (B-1)J before its sign is known; increase the paid X scale to q^2."""
    packet = fixed71()
    rows = []
    for name, op, x, y in packet["source"]:
        if name == "repunit":
            continue
        x = "base_multiple" if x == "repunit" else x
        y = "base_multiple" if y == "repunit" else y
        if name == "wn2":
            require([op, x, y] == ["*", "w", "q"], "expected X row")
            y = "Lbig"
        rows.append([name, op, x, y])
    packet.update(
        name="fixed70", source=rows, exact_degree=169,
        factor_exact_degrees=[24, 20, 1, 64, 8, 2, 50],
        scope=(
            "Fixed raw input x=1 with actual modified75 compiler coefficients. "
            "Use X=w*q^2 and beta*J directly in packing and transport. "
            "The initially signed repunit is recovered after dyadic decoding. "
            "No global minimality or formal proof-assistant verification is claimed."
        ),
    )
    return packet

def sum_of_squares(packet):
    out = json.loads(json.dumps(packet))
    rows = out["source"]
    terms = []
    for j, (left, right) in enumerate(out.pop("comparisons")):
        residual, square = "residual_%d" % j, "square_%d" % j
        rows.extend([[residual, "-", left, right], [square, "*", residual, residual]])
        terms.append(square)
    acc = terms[0]
    for j, term in enumerate(terms[1:], 1):
        name = "sum_%d" % j
        rows.append([name, "+", acc, term])
        acc = name
    out.update(name="transparent84_sos", output=acc, exact_degree=56)
    return out

def evaluate(packet, values, positive=False):
    ports = packet["witnesses"] + packet["fixed_numerals"]
    require(set(values) == set(ports), "assignment has wrong ports")
    require(all(type(x) is int for x in values.values()), "integer values required")
    if positive:
        require(all(values[p] > 0 for p in ports), "positive values required")
    result = dict(values)
    for name, op, x, y in packet["source"]:
        a = x if type(x) is int else result[x]
        b = y if type(y) is int else result[y]
        result[name] = a + b if op == "+" else a - b if op == "-" else a * b
    return result

def structure(packet):
    ports = packet["witnesses"] + packet["fixed_numerals"]
    require(len(ports) == len(set(ports)), "duplicate ports")
    seen = set(ports)
    degrees = {p: 1 for p in packet["witnesses"]}
    degrees.update({p: 0 for p in packet["fixed_numerals"]})
    deps = {}
    multiplication = addition = 0
    for name, op, x, y in packet["source"]:
        require(type(name) is str and name not in seen, "duplicate output")
        require(op in {"+", "-", "*"}, "bad operator")
        require(all(type(t) is int or (type(t) is str and t in seen) for t in (x, y)), "forward reference")
        dx, dy = [0 if type(t) is int else degrees[t] for t in (x, y)]
        degrees[name] = dx + dy if op == "*" else max(dx, dy)
        deps[name] = {t for t in (x, y) if type(t) is str}
        seen.add(name)
        multiplication += op == "*"
        addition += op != "*"
    roots = {packet["output"]} if "output" in packet else {
        t for pair in packet["comparisons"] for t in pair if type(t) is str
    }
    live = set(roots)
    queue = list(roots)
    while queue:
        for dep in deps.get(queue.pop(), ()):
            if dep not in live:
                live.add(dep)
                queue.append(dep)
    require(set(deps) <= live, "dead arithmetic row")
    require(set(ports) <= live, "dead supplied port")
    return {
        "M": multiplication, "A": addition,
        "total": multiplication + addition,
        "witnesses": len(packet["witnesses"]),
        "comparisons": len(packet.get("comparisons", [])),
        "gate_degree_upper_bound": degrees.get(packet.get("output")),
        "source_sha256": digest(packet["source"]),
    }

def poly_add(a, b, sign, prime):
    out = [0] * max(len(a), len(b))
    for i in range(len(out)):
        out[i] = ((a[i] if i < len(a) else 0) + sign * (b[i] if i < len(b) else 0)) % prime
    while len(out) > 1 and not out[-1]:
        out.pop()
    return out

def poly_mul(a, b, prime):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] = (out[i+j] + x*y) % prime
    while len(out) > 1 and not out[-1]:
        out.pop()
    return out

def specialize(packet, seed, prime):
    rng = Random(seed)
    values = {p: [rng.randrange(1, 17), rng.randrange(1, 17)] for p in packet["witnesses"]}
    # These small coefficient choices test arithmetic only, not universality.
    values.update({p: [v] for p, v in zip(packet["fixed_numerals"], (15, 29, 2, 35, 67))})
    for name, op, x, y in packet["source"]:
        a = [x % prime] if type(x) is int else values[x]
        b = [y % prime] if type(y) is int else values[y]
        values[name] = poly_mul(a, b, prime) if op == "*" else poly_add(a, b, 1 if op == "+" else -1, prime)
    return {
        "seed": seed,
        "prime": prime,
        "degree": len(values[packet["output"]])-1,
        "factor_degrees": {p: len(values[p])-1 for p in packet.get("factor_outputs", [])},
        "coefficient_sha256": digest(values[packet["output"]]),
        "scope": "Arithmetic degree diagnostic; these coefficients are not a compiled ZFC program.",
    }

def verify():
    parent_bytes = Path(__file__).with_name("parent84_reference.json").read_bytes()
    require(hashlib.sha256(parent_bytes).hexdigest() == PARENT_FILE_SHA256, "pinned parent file hash")
    parent = json.loads(parent_bytes)
    require(parent["packet"]["source"] == BASE84, "pinned parent source")
    require(parent["packet"]["witnesses"] == BASE_WITNESSES, "pinned parent witnesses")
    p70, p71, p73, p61 = fixed70(), fixed71(), fixed73(), transparent61()
    p84 = sum_of_squares(p61)
    reports = {p["name"]: structure(p) for p in (p70, p71, p73, p61, p84)}
    require(reports["fixed70"]["total"] == 70, "fixed70 count")
    require(reports["fixed70"]["witnesses"] == 16, "fixed70 arity")
    require(reports["fixed71"]["total"] == 71, "fixed71 count")
    require(reports["fixed71"]["witnesses"] == 16, "fixed71 arity")
    require(reports["fixed73"]["total"] == 73, "fixed73 count")
    require(reports["fixed73"]["witnesses"] == 16, "fixed73 arity")
    require(reports["transparent61"]["total"] == 61, "transparent61 count")
    require(reports["transparent61"]["witnesses"] == 17, "transparent61 arity")
    require(reports["transparent84_sos"]["total"] == 84, "SOS count")
    rng = Random(215)
    for _ in range(32):
        assignment = {p: rng.randrange(-3, 5) for p in p73["witnesses"] + p73["fixed_numerals"]}
        v = evaluate(p73, assignment)
        delta, c, i, f = v["A"], v["R10a"], v["i"], v["f"]
        six = 1
        for name in p73["factor_outputs"][:-1]:
            six *= v[name]
        ordinary_strong = f*f - delta*i*i*c**4
        require(v["polynomial"] == delta*(six*ordinary_strong-1), "scaled-output identity")
        require(v["norm_budget"] == 1+(v["q"]-v["F"]-v["C"]-v["alpha"])**2, "budget identity")
        require(v["r_lhs"] == (v["q"]**2-v["Z"]-v["q"]*v["F"])*(v["q"]**2-1)+(v["MC"]+v["q"]*v["MF"])*v["Jrep"], "packing identity")
        assignment2 = {p: rng.randrange(-3, 5) for p in p61["witnesses"] + p61["fixed_numerals"]}
        u = evaluate(p61, assignment2)
        z = evaluate(p84, assignment2)
        residuals = [(a if type(a) is int else u[a])-(b if type(b) is int else u[b]) for a,b in p61["comparisons"]]
        require(z[p84["output"]] == sum(r*r for r in residuals), "sum-of-squares identity")
        assignment71 = {p: rng.randrange(-3, 5) for p in p71["witnesses"] + p71["fixed_numerals"]}
        v71 = evaluate(p71, assignment71)
        require(v71["q"] == v71["C"]+v71["F"]+v71["alpha"], "shared geometry")
        require(v71["q_minus_FZ"] == v71["q"]-v71["F"]-v71["Z"], "shared packing gap")
        require(v71["r_lhs"] == (v71["q"]**2-v71["Z"]-v71["q"]*v71["F"])*(v71["q"]**2-1)+(v71["MC"]+v71["q"]*v71["MF"])*v71["Jrep"], "linear-repunit packing")
        delta71, c71, i71, f71 = [v71[x] for x in ("A", "R10a", "i", "f")]
        six71 = 1
        for name in p71["factor_outputs"][:-1]:
            six71 *= v71[name]
        require(v71["polynomial"] == delta71*(six71*(f71*f71-delta71*i71*i71*c71**4)-1), "linear-repunit scaled identity")
        assignment70 = {p: rng.randrange(-3, 5) for p in p70["witnesses"] + p70["fixed_numerals"]}
        v70 = evaluate(p70, assignment70)
        require(v70["wn2"] == v70["w"]*v70["q"]**2, "quadratic X scale")
        require(v70["gap"] == v70["base_multiple"]*(v70["q"]-v70["F"])+(v70["q"]-v70["F"]-v70["Z"]), "reused repunit packing")
        delta70, c70, i70, f70 = [v70[x] for x in ("A", "R10a", "i", "f")]
        six70 = 1
        for name in p70["factor_outputs"][:-1]:
            six70 *= v70[name]
        require(v70["polynomial"] == delta70*(six70*(f70*f70-delta70*i70*i70*c70**4)-1), "reused-repunit scaled identity")
    diagnostics = []
    for packet in (p70, p71, p73, p84):
        for seed, prime in ((1, 1000000007), (2, 1000000009)):
            diag = specialize(packet, seed, prime)
            require(diag["degree"] == packet["exact_degree"], "specialized exact degree")
            if "factor_exact_degrees" in packet:
                require(list(diag["factor_degrees"].values()) == packet["factor_exact_degrees"], "factor exact degree")
            diagnostics.append({"packet": packet["name"], **diag})
    return {
        "status": "PASS",
        "parent": {"url": PARENT_URL, "commit": PINNED_COMMIT,
                   "file_sha256": PARENT_FILE_SHA256,
                   "embedded_source_sha256": digest(BASE84)},
        "circuits": reports,
        "exact_integer_fixture_count": 32,
        "degree_diagnostics": diagnostics,
        "proof_boundary": (
            "The report proves parametric equivalence for coefficients from the inherited compiler. "
            "This verifier authenticates emitted circuits, counts, liveness and arithmetic identities. "
            "It does not instantiate the compiler, replay inherited research suites, "
            "formally verify ZFC semantics, or search for a consistency witness."
        ),
        "packets": [p70, p71, p73, p61, p84],
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    receipt = verify()
    data = json.dumps(receipt, sort_keys=True, indent=2) + "\n"
    if args.output:
        args.output.write_text(data)
    print(json.dumps({"status": receipt["status"], "circuits": receipt["circuits"]}, indent=2))

if __name__ == "__main__":
    main()

