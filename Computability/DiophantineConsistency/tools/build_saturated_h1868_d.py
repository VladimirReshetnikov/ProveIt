#!/usr/bin/env python3
"""Exact D-register sharing for the saturated H1868 nine-positive equation.

No Lean command is invoked. All data are pinned inert arrival members. The
parent's source, ratio, Pell, majorant and norm registers are checked exactly
at algebraic cuts, then a separate normalizer proves the263-term replacement.
"""
import argparse
import ast
import collections
import copy
import gzip
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path

import build_radical_d_shared as reduction
from build_shared_products66 import normalize
from review_proposal_frontier import audit, require

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "candidates/saturated-h1868-d"
SOURCE = DEST / "source"
PARENT_SHA = "2c26978d50fc23724e9b678e06c65afc531f50946e101df2a1347ed9411ab08d"
ARCHIVE_SHA = "dd462410bc9dee18a7b71cb0e5cedd2a4c615f7722fd7fe474303b8110af80fc"
AUDITOR_SHA = "f2b841a9c2b4d4e6c24b3b121accb19ae56fbcea2ab1f96877a390b18b8ca5c8"
OPS = {"add", "sub", "mul"}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2) + "\n").encode()


def load(path):
    if path.exists():
        return json.loads(path.read_bytes())
    return json.loads(gzip.decompress(path.with_name(path.name + ".gz").read_bytes()))


def add(a, b, sign=1):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + sign*c
        if not out[m]:
            del out[m]
    return out


def expression(text, atoms):
    def go(node):
        if isinstance(node, ast.Name):
            return {(atoms[node.id],): 1}
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return {(): node.value} if node.value else {}
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return {m: -c for m, c in go(node.operand).items()}
        require(isinstance(node, ast.BinOp), "polynomial expression")
        a = go(node.left)
        if isinstance(node.op, ast.Pow):
            require(isinstance(node.right, ast.Constant) and type(node.right.value) is int and node.right.value >= 0, "fixed exponent")
            e, out = node.right.value, {(): 1}
            while e:
                if e % 2:
                    out = reduction.multiply(out, a)
                e //= 2
                if e:
                    a = reduction.multiply(a, a)
            return out
        b = go(node.right)
        if isinstance(node.op, ast.Mult):
            return reduction.multiply(a, b)
        require(isinstance(node.op, (ast.Add, ast.Sub)), "ring operation")
        return add(a, b, -1 if isinstance(node.op, ast.Sub) else 1)
    return go(ast.parse(text, mode="eval").body)


def topology(body):
    counts, live = collections.Counter(), set()
    for k, node in enumerate(body["nodes"]):
        if node["kind"] in OPS:
            require(0 <= node["left"] < k and 0 <= node["right"] < k, "acyclic topology")
            counts[node["kind"]] += 1
        else:
            require(node["kind"] in {"variable", "fixed", "literal"}, "allowed leaves")
    pending = [body["output"]]
    while pending:
        k = pending.pop()
        if k not in live:
            live.add(k)
            node = body["nodes"][k]
            if node["kind"] in OPS:
                pending.extend((node["left"], node["right"]))
    require(live == set(range(len(body["nodes"]))), "all nodes live")
    require(sum(counts.values()) == body["total_operations"] and dict(counts) == body["operation_counts"], "literal operation counts")
    require({n["name"] for n in body["nodes"] if n["kind"] == "variable"} == set(body["variables"]), "all inputs live")
    return dict(counts)


def parent_formulas(parent):
    names = dict(parent["named_nodes"])
    names.update({n["name"]: k for k, n in enumerate(parent["nodes"]) if n["kind"] in {"variable", "fixed"}})
    checked = []
    def eq(name, formula, dependencies):
        ids = [names[n] for n in dependencies]
        require(len(ids) == len(set(ids)) and all(k < names[name] for k in ids), "earlier distinct formula cuts: " + name)
        actual, _ = normalize(parent["nodes"], names[name], {k: j for j, k in enumerate(ids)})
        require(actual == expression(formula, {n: j for j, n in enumerate(dependencies)}), "exact literal register " + name)
        checked.append(name)
    eq("B", "base_scale*b**2", ["base_scale", "b"])
    kernels = load(SOURCE / "data/kernels.json")
    for layer, leading in zip(kernels["kernels"], (-6, 2, 1)):
        top = max(layer["terms"], key=lambda r: r["exponent"])
        require(top["coefficient"] == [{"powers": [0,0,0,0], "coefficient": leading}], "literal kernel leading coefficient")
    recipe_names = {json.dumps(v, sort_keys=True): k for k, v in parent["coefficient_recipes"].items()}
    for layer in kernels["kernels"]:
        terms, fixed = [], set()
        for record in layer["terms"]:
            rec = record["coefficient"]
            if len(rec) == 1 and not any(rec[0]["powers"]):
                coeff = str(rec[0]["coefficient"])
            else:
                coeff = recipe_names[json.dumps(rec, sort_keys=True)]
                fixed.add(coeff)
            terms.append("(" + coeff + ")*B**" + str(record["exponent"]))
        eq("Dcode" + str(layer["degree"]), "+".join(terms), ["B"] + sorted(fixed))
    code = load(SOURCE / "data/code.json")
    eq("ell", "+".join("B**" + str(e) for e in code["weights"]), ["B"])
    eq("targets", "+".join("B**" + str(e) for e in code["targets_by_row"]), ["B"])
    eq("N0", "B**117", ["B"])
    eq("Usource", "ell+g", ["ell", "g"])
    eq("Gsource", "(Dcode2*Usource+Dcode1)*Usource+Dcode0", ["Dcode2", "Dcode1", "Dcode0", "Usource"])
    eq("mask", "N0-1-(b-1)*ell", ["N0", "b", "ell"])
    eq("Tcode", "mask+(B-2)*targets*N0", ["mask", "B", "targets", "N0"])
    eq("Jcode", "2*Gsource+targets", ["Gsource", "targets"])
    eq("Scode", "g+N0*Jcode", ["g", "N0", "Jcode"])
    eq("L", "2*b*B**1986", ["b", "B"])
    eq("N", "threshold_scale*B**1055", ["threshold_scale", "B"])
    eq("Rplus1", "L*(Scode+Tcode+1)-Scode", ["L", "Scode", "Tcode"])
    eq("R", "Rplus1-1", ["Rplus1"])
    eq("capbase", "b*B**116", ["b", "B"])
    formulas = [
        ("U", "N**2*w", ["N", "w"]), ("Y", "N**2*s", ["N", "s"]),
        ("M", "R*Y", ["R", "Y"]), ("MU", "M*U", ["M", "U"]),
        ("P", "2*M*MU", ["M", "MU"]), ("K", "Rplus1+h*(P-1)", ["Rplus1", "h", "P"]),
        ("A", "M+MU", ["M", "MU"]), ("B1", "2*R+1", ["R"]),
        ("W1", "b*w", ["b", "w"]), ("J", "4*A-5", ["A"]),
        ("Q", "3*W1*C-2*(W1**2-1)", ["W1", "C"]),
        ("V0", "P*K", ["P", "K"]), ("a0", "V0**2-K**2+1", ["V0", "K"]),
        ("margin", "K**2*(4*capbase-g)-16*capbase*(C-K*Y)**2", ["K", "capbase", "g", "C", "Y"]),
        ("Omega", "J*margin", ["J", "margin"]), ("E0", "J*(n+W1**2)+Q", ["J", "n", "W1", "Q"]),
        ("D", "(A**2-1)*C**2+1", ["A", "C"]),
        ("F", "(A**2-1)*D*(i*J*C**2)**2+1", ["A", "D", "i", "J", "C"]),
        ("G", "A+F*(C*D+1-A)", ["A", "F", "C", "D"]),
        ("Z", "B1+(j-1)*C", ["B1", "j", "C"]), ("H", "C+F*Z", ["C", "F", "Z"]),
        ("I", "(G**2-1)*H**2+1", ["G", "H"]), ("raw_a1", "D*F*I", ["D", "F", "I"]),
        ("scale", "1024*C**5*i", ["C", "i"]), ("a1", "scale**2*raw_a1", ["scale", "raw_a1"]),
        ("Theta", "E0-Omega*(V0+V1)", ["E0", "Omega", "V0", "V1"]),
        ("inner", "Theta**2-Omega**2*(a0+a1)", ["Theta", "Omega", "a0", "a1"]),
        ("F9", "inner**2-4*Omega**4*a0*a1", ["inner", "Omega", "a0", "a1"]),
    ]
    for item in formulas:
        eq(*item)
    cuts = [names[n] for n in ("A", "C", "i", "Z")]
    actual, _ = normalize(parent["nodes"], names["V1"], {k: j for j, k in enumerate(cuts)})
    expected = {}
    for record in load(SOURCE / "data/saturated_corrected_P.json")["terms"]:
        monomial = tuple(j for j, e in enumerate(record["powers"]) for _ in range(e))
        require(monomial not in expected, "distinct majorant terms")
        expected[monomial] = record["coefficient"]
    require(actual == expected and parent["output"] == names["F9"], "complete original333-term majorant and norm output")
    return dict(exact_registers=checked, radical_terms=len(expected), whole_output_bound=True)


def fixed_check(parent):
    binding = load(SOURCE / "data/COEFFICIENT_BINDING.json")
    ports, port_records = [], []
    for name in ("beta", "K", "MC", "MF_source"):
        record = next(r for r in binding["files"] if r["port"] == name)
        compressed = (SOURCE / "data" / (name + ".bin.gz")).read_bytes()
        raw = gzip.decompress(compressed)
        require(sha(compressed) == record["gzip_sha256"] and sha(raw) == record["sha256"], "coherent native port bytes")
        value = int.from_bytes(raw, "little")
        require(value.bit_length() == record["bit_length"] and len(raw) == record["raw_bytes"], "native port dimensions")
        ports.append(value)
        port_records.append(dict(port=name, raw_bytes=len(raw), sha256=sha(raw)))
    require([v.bit_length() for v in ports] == [1064921,1070004,1064921,1064922], "same original31 bit bounds")
    values = {}
    for name, recipe in parent["coefficient_recipes"].items():
        value = 0
        for term in recipe:
            c = term["coefficient"]
            for port, e in zip(ports, term["powers"]):
                c *= port ** e
            value += c
        values[name] = value
        require(abs(value) < 2**2134927, "actual coefficient height")
    values.update(base_scale=2**2134939, threshold_scale=2**16012032)
    fixed = load(DEST / "fixed/h1868/BINDING.json")
    require(set(values) == {r["name"] for r in fixed["records"]}, "complete12-leaf set")
    require({n["name"] for n in parent["nodes"] if n["kind"] == "fixed"} == set(values), "all fixed names")
    leaves = []
    for r in fixed["records"]:
        compressed = (DEST / r["path"]).read_bytes()
        raw = gzip.decompress(compressed)
        value = values[r["name"]]
        require(sha(compressed) == r["gzip_sha256"] and sha(raw) == r["raw_sha256"], "full fixed leaf hashes")
        require((value > 0) - (value < 0) == r["sign"] and abs(value).bit_length() == r["bits"], "fixed sign and bit length")
        require(abs(value).to_bytes(len(raw), "little") == raw, "all fixed bytes from whole tuple")
        leaves.append(dict(name=r["name"], bytes=len(raw), sha256=sha(raw)))
    return dict(native_ports=port_records, fixed_leaves=leaves,
                port_raw_bytes=sum(r["raw_bytes"] for r in port_records),
                fixed_raw_bytes=sum(r["bytes"] for r in leaves))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    pins = load(DEST / "PINS.json")
    require(pins["archive_sha256"] == ARCHIVE_SHA, "raw arrival archive")
    for name, record in pins["files"].items():
        stored = (DEST / name).read_bytes()
        require(sha(stored) == record["stored_sha256"], "stored raw arrival member")
        raw = gzip.decompress(stored) if record["encoding"] == "gzip-json" else stored
        require(sha(raw) == record["original_sha256"], "full raw archival bytes")
    require(sha((SOURCE / "archive_audit.py").read_bytes()) == AUDITOR_SHA, "inspected source/radical auditor")
    spec = importlib.util.spec_from_file_location("saturated_h1868_audit", SOURCE / "archive_audit.py")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    checker.load = load  # only gzip storage is adapted
    source_audit = checker.source_check(SOURCE)
    radical_audit = checker.radical_check(SOURCE, source_audit)
    kappa = 2134939
    population = dict(left_constant=2125*kappa-21, right_constant=2*16012032+2110*kappa,
                      left_k_coefficient=2*2125+1-31, right_k_coefficient=2*2110)
    require(population["left_constant"] == population["right_constant"] and
            population["left_k_coefficient"] == population["right_k_coefficient"] == 4220,
            "symbolic population identity for every k, with corrected4220 coefficient")
    raw = (SOURCE / "equations/h1868_complete.json").read_bytes()
    require(sha(raw) == PARENT_SHA, "literal1086-operation parent")
    parent = json.loads(raw)
    topology(parent)
    formula_audit = parent_formulas(parent)
    fixed = fixed_check(parent)
    terms = [(r["powers"], r["coefficient"]) for r in load(SOURCE / "data/saturated_corrected_P.json")["terms"]]
    table = reduction.reduce_table(terms)
    require(len(table) == 263, "collected saturated polynomial size")
    compatible = copy.deepcopy(parent)
    compatible["named_nodes"]["Pstar"] = parent["named_nodes"]["V1"]
    compatible["source_sha256"] = sha((SOURCE / "data/source.json").read_bytes())
    compatible["layout_sha256"] = sha((SOURCE / "data/code.json").read_bytes())
    choices, best = [], None
    for order in itertools.permutations(range(5)):
        reduction.ORDER = order
        candidate, certificate = reduction.transform(compatible, table)
        choices.append(dict(order=list(order), operations=candidate["total_operations"]))
        if best is None or candidate["total_operations"] < best[0]:
            best = candidate["total_operations"], candidate, certificate
    _, child, certificate = best
    child["named_nodes"].pop("Pstar", None)
    child.update(majorant_encoding="263-term saturated D-reduced Horner polynomial",
                 majorant_variables=["A","C","D","i","Z"],
                 fixed_binding="fixed/h1868/BINDING.json")
    identity = reduction.verify(compatible, child, certificate)
    require(child["named_nodes"] == {k: int(certificate["retained_remap"][str(v)]) for k, v in parent["named_nodes"].items() if str(v) in certificate["retained_remap"]}, "every retained named value")
    require(child["total_operations"] == 954 and child["exact_degree"] == 999518, "new concrete metrics")
    cutmap = [int(certificate["retained_remap"][str(v)]) for v in certificate["cutset"]]
    require(len(set(cutmap)) == 5 and all(v < certificate["new_majorant"] for v in cutmap), "distinct earlier replacement atoms")
    topology(child)
    # Syntactic degree metadata is recomputed for the new topology; the exact
    # polynomial degree is inherited by the verified equality.
    degree = []
    for n in child["nodes"]:
        k = n["kind"]
        degree.append(1 if k == "variable" else 0 if k in {"fixed","literal"} else
                      degree[n["left"]]+degree[n["right"]] if k == "mul" else
                      max(degree[n["left"]],degree[n["right"]]))
    child["raw_degree_bound"] = degree[child["output"]]
    child["named_degree_bounds"] = {k: degree[v] for k, v in child["named_nodes"].items()}
    broken = copy.deepcopy(child)
    broken["nodes"][certificate["new_majorant"]]["kind"] = "mul" if child["nodes"][certificate["new_majorant"]]["kind"] != "mul" else "add"
    try:
        reduction.verify(compatible, broken, certificate)
    except ValueError:
        pass
    else:
        raise ValueError("majorant corruption escaped exact identity check")
    certificate.update(identity=identity, parent_sha256=PARENT_SHA, child_sha256=sha(encoded(child)))
    review = dict(status="PASS", variables=9, domain="strictly positive integers",
                  operations=954, parent_operations=1086, removed_operations=132, exact_degree=999518,
                  operation_counts=child["operation_counts"], local_identity=identity,
                  source_audit=source_audit, radical_audit=radical_audit,
                  exact_parent_transcription=formula_audit, complete_fixed_tuple=fixed,
                  symbolic_population_identity=population,
                  source_archive_sha256=ARCHIVE_SHA, corruption_rejected=True,
                  threshold_correction="Both printed4210 coefficients should read4220; all delivered threshold parameters and exact equality are unchanged.",
                  scope="Identical ring polynomial to pinned1086-operation parent. Complete finite source/parent/D-rewrite checks and ordinary proof review; inherited native/refutation/internal-ZFC boundary, no Lean work.")
    files = {"equation9.json": encoded(child), "rewrite.json": encoded(certificate),
             "reduced_table.json": encoded([[list(e), c] for e, c in sorted(table.items())]),
             "HORNER_CHOICES.json": encoded(choices), "REVIEW.json": encoded(review)}
    files["MANIFEST.json"] = encoded({name: sha(value) for name, value in sorted(files.items())})
    for name, value in files.items():
        path = DEST / name
        if args.check:
            require(path.read_bytes() == value, "deterministic candidate " + name)
        else:
            path.write_bytes(value)
    audit(("../candidates/saturated-h1868-d/equation9.json",9,"+",999518,954))
    print(json.dumps({k:review[k] for k in ("status","variables","domain","operations","parent_operations","removed_operations","exact_degree","local_identity")}, indent=2))


if __name__ == "__main__":
    main()
