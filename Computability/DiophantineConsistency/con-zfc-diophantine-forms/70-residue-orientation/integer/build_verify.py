#!/usr/bin/env python3
"""Build and exactly audit residue-oriented 40/34/29 integer equations.

Python standard library only. The mathematical equivalence is proved in
PROOF.md; finite checks certify the literal algebra and supplied constants.
No acceptance condition uses an assert statement.
"""
from pathlib import Path
import ast
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")


class Polynomial:
    """Independent sparse integer polynomial evaluator for inert ASTs."""
    def __init__(self, names):
        self.names = list(names)
        self.indices = {name: i for i, name in enumerate(names)}
        self.zero = (0,) * len(names)

    def add(self, left, right, factor=1):
        result = dict(left)
        for exponents, coefficient in right.items():
            result[exponents] = result.get(exponents, 0) + factor * coefficient
            if result[exponents] == 0:
                del result[exponents]
        return result

    def multiply(self, left, right):
        result = {}
        for a, ca in left.items():
            for b, cb in right.items():
                key = tuple(x + y for x, y in zip(a, b))
                result[key] = result.get(key, 0) + ca * cb
                if result[key] == 0:
                    del result[key]
        return result

    def parse(self, formula):
        def visit(node):
            if isinstance(node, ast.Constant) and type(node.value) is int:
                return {self.zero: node.value} if node.value else {}
            if isinstance(node, ast.Name):
                key = list(self.zero)
                key[self.indices[node.id]] = 1
                return {tuple(key): 1}
            if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
                return {k: -v for k, v in visit(node.operand).items()}
            if isinstance(node, ast.BinOp):
                if isinstance(node.op, ast.Add):
                    return self.add(visit(node.left), visit(node.right))
                if isinstance(node.op, ast.Sub):
                    return self.add(visit(node.left), visit(node.right), -1)
                if isinstance(node.op, ast.Mult):
                    return self.multiply(visit(node.left), visit(node.right))
                if isinstance(node.op, ast.Pow):
                    require(isinstance(node.right, ast.Constant)
                            and type(node.right.value) is int
                            and 0 <= node.right.value <= 8,
                            "only fixed nonnegative powers are allowed")
                    value = {self.zero: 1}
                    base = visit(node.left)
                    for _ in range(node.right.value):
                        value = self.multiply(value, base)
                    return value
            raise ValueError("Unsupported polynomial syntax: " + ast.dump(node))
        return visit(ast.parse(formula, mode="eval").body)


def substitute(formula, mapping):
    """Simultaneous substitution: replacement strings use final coordinates."""
    class Replace(ast.NodeTransformer):
        def visit_Name(self, node):
            if node.id in mapping:
                return ast.parse(mapping[node.id], mode="eval").body
            return node
    return ast.unparse(ast.fix_missing_locations(
        Replace().visit(ast.parse(formula, mode="eval"))))


def source_integrity():
    pins = json.loads((ROOT / "SOURCE_PINS.json").read_text())
    for record in pins:
        raw = (ROOT / record["file"]).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode()
                            + b"\0" + raw).hexdigest()
        require(sha256(raw) == record["sha256"], "source SHA256: " + record["file"])
        require(blob == record["git_blob"], "source Git blob: " + record["file"])
    return len(pins)


def rebuild_coefficients():
    """Exact source34 native recipe, independently matching all supplied bytes.

    Formula provenance: retained source34 COEFFICIENT_PROOF.md and
    source64 integer41/build_verify44.py. No consistency-dependent input.
    """
    tiles = json.loads((ROOT / "upstream/wang943_tiles.json").read_text())
    require(len(tiles) == 943, "943 literal tiles")
    b, width, d = 121, 8801, 1064921
    require(b * width == d and d % 2 == 1, "odd native radix exponent")
    B, rho = 1 << d, 1 << b
    weights = [1 << (10 + 2 * j) for j in range(44)]
    native = {}
    for j, tile in enumerate(tiles):
        require(len(tile) == 4 and all(0 <= x < 512 for x in tile), "tile alphabet")
        value = 1 + sum(weights[40:44])
        for t, label in enumerate(tile):
            value += sum(weights[10*t+k] for k in range(10)
                         if ((label + 512) >> k) & 1)
        native[j] = value
    for t, offset in enumerate([1020, 1000, 980, 960]):
        for j in range(10):
            native[offset + 2*j] = weights[10*t+j]
    for exponent, j in zip([1095, 1096, 2195, 3296], range(40, 44)):
        native[exponent] = weights[j]
    native[1063] = native[1064] = 0
    require(len(native) == 989, "native basis size")
    DC = sum(1 << (b*e) for e in [40, 41, 1100, 2200])
    for exponent, value in native.items():
        DC += value * ((1 << (b*(4393-exponent)))
                       + (1 << (b*(5495-exponent))))
    beta = B-1
    MC = beta - sum(1 << (b*e) for e in native if e != 1) - (2 << (b*1063))
    mu = 1022 + sum(weights)
    high = ((1 << 119)-1) * sum(1 << (b*e) for e in range(8792, 8799))
    high += ((1 << 27)-1) << (b*8799)
    MF_native = 4 + mu*((1 << (b*4393)) + (1 << (b*5495)))
    MF_native += sum((1 << (b*(1000+2*j))) + (1 << (b*(1021+2*j)))
                     for j in range(10))
    MF_native += (1 << (b*2195)) + (1 << (b*3296)) + high
    values = {"beta": beta, "K": DC+B*rho, "MC": MC,
              "MF_source": MF_native+beta}
    manifest = json.loads((ROOT / "upstream/PAYLOAD_BINDING.json").read_text())
    records = {}
    for name, value in values.items():
        expected = manifest["payloads"][name]
        raw = value.to_bytes((value.bit_length()+7)//8, "little")
        supplied = gzip.decompress((ROOT / "coefficients" / (name+".bin.gz")).read_bytes())
        require(raw == supplied, "actual supplied numeral: " + name)
        require(value.bit_length() == expected["bits"], "numeral bit count")
        require(len(raw) == expected["bytes"], "numeral byte count")
        require(sha256(raw) == expected["sha256"], "numeral source digest")
        records[name] = {"bits": value.bit_length(), "bytes": len(raw),
                         "sha256": sha256(raw), "mod3": value % 3}
    require(beta % 3 == 1, "new residue-orientation coefficient hypothesis")
    require(0 < MC < beta < values["MF_source"] < 2*beta, "native mask bounds")
    require(values["K"] >= 0, "transport coefficient sign")
    require(MC % 4 == 2 and MF_native % 8 == 4, "native parity")
    require(MC.bit_count()+MF_native.bit_count() == d, "native population")
    write_json(ROOT / "certificates/COEFFICIENT_CHECKS.json", records)
    return records


def binding():
    return {"backend": "whole source34 mixed-parity-unrounded-1064921 tuple",
            "format": "gzip of minimal unsigned little-endian integer bytes",
            "ports": {"beta": "coefficients/beta.bin.gz", "K0": "coefficients/K.bin.gz",
                      "MC": "coefficients/MC.bin.gz", "MF": "coefficients/MF_source.bin.gz"},
            "mask_convention": "MF already includes the shift beta",
            "source_manifest": "upstream/PAYLOAD_BINDING.json"}


def build_quartic():
    raw = (ROOT / "upstream/quartic41.json").read_bytes()
    source = json.loads(raw)
    require(source["variable_count"] == 41 and len(source["residuals"]) == 26,
            "authentic parent dimensions")
    require(source["residuals"][22] == "X-2*u**2", "the deleted square guard")
    mapping = {"J": "3*J3+1", "w_scale": "3*w3+1"}
    variables = [{"J": "J3", "w_scale": "w3"}.get(x, x)
                 for x in source["variables"] if x != "u"]
    rows = [substitute(row, mapping) for j, row in enumerate(source["residuals"])
            if j != 22]
    packet = {"name": "quartic40_residue_orientation", "domain": "unrestricted integers",
              "variables": variables, "variable_count": 40, "equation_count": 25,
              "residuals": rows, "fixed_numerals": source["fixed_numerals"],
              "single_polynomial": "sum of squares of the 25 listed residuals",
              "exact_degree": 4, "degree_certificate": {"monomial": {"tau": 4}, "coefficient": 1},
              "coefficient_binding": binding(), "parent": "upstream/quartic41.json",
              "parent_sha256": sha256(raw), "affine_source_coordinates": mapping,
              "deleted_source_row_zero_based": 22, "deleted_source_variable": "u",
              "proof": "PROOF.md", "source_pin": "9cca523d9f27ad39d52993f4065cbd7e58f8bdd4"}
    write_json(ROOT / "quartic40.json", packet)
    return packet


def build_direct_quartic():
    """The smaller displayed quartic: orient X itself by X=3X3-1."""
    raw = (ROOT / "upstream/quartic41.json").read_bytes()
    source = json.loads(raw)
    mapping = {"X": "3*X3-1"}
    variables = [("X3" if x == "X" else x) for x in source["variables"] if x != "u"]
    rows = [substitute(row, mapping) for j, row in enumerate(source["residuals"])
            if j != 22]
    packet = {"name": "quartic40_direct_orientation", "domain": "unrestricted integers",
              "variables": variables, "variable_count": 40, "equation_count": 25,
              "residuals": rows, "fixed_numerals": source["fixed_numerals"],
              "single_polynomial": "sum of squares of the 25 listed residuals",
              "exact_degree": 4, "degree_certificate": {"monomial": {"tau": 4}, "coefficient": 1},
              "coefficient_binding": binding(), "parent": "upstream/quartic41.json",
              "parent_sha256": sha256(raw), "affine_source_coordinates": mapping,
              "deleted_source_row_zero_based": 22, "deleted_source_variable": "u",
              "proof": "PROOF.md, section 9", "source_pin": "9cca523d9f27ad39d52993f4065cbd7e58f8bdd4"}
    write_json(ROOT / "quartic40_direct.json", packet)
    return packet


def build_projection(source, name, replacements, removed, degree, certificate):
    variables = [x for x in source["variables"] if x not in replacements]
    if "tau" in replacements:
        variables.insert(source["variables"].index("tau"), "tau_tail")
    algebra = Polynomial(variables + source["fixed_numerals"])
    rows = []
    for j, row in enumerate(source["residuals"]):
        changed = substitute(row, replacements)
        if j in removed:
            require(algebra.parse(changed) == {}, name+": exact deleted definition "+str(j))
        else:
            rows.append(changed)
    packet = {"name": name, "domain": "unrestricted integers", "variables": variables,
              "variable_count": len(variables), "equation_count": len(rows), "residuals": rows,
              "fixed_numerals": source["fixed_numerals"], "coefficient_binding": binding(),
              "single_polynomial": "sum of squares of the listed residuals",
              "exact_degree": degree, "degree_certificate": certificate,
              "restoration_to_quartic40": replacements,
              "deleted_quartic40_rows_zero_based": sorted(removed), "parent": "quartic40.json",
              "parent_sha256": sha256((ROOT / "quartic40.json").read_bytes()),
              "proof": "PROOF.md"}
    write_json(ROOT / (name+".json"), packet)
    return packet


def audit(packet):
    n = len(packet["variables"])
    require(n == packet["variable_count"], "declared variable count")
    require(len(packet["residuals"]) == packet["equation_count"], "declared row count")
    algebra = Polynomial(packet["variables"] + packet["fixed_numerals"])
    rows = [algebra.parse(row) for row in packet["residuals"]]
    degrees = [max(sum(k[:n]) for k in row) for row in rows]
    require(max(degrees)*2 == packet["exact_degree"], "residual degree bound")
    live = {packet["variables"][j] for row in rows for key in row for j in range(n) if key[j]}
    require(live == set(packet["variables"]), "every named unknown is live")
    squared = {}
    for row in rows:
        squared = algebra.add(squared, algebra.multiply(row, row))
    require(max(sum(k[:n]) for k in squared) == packet["exact_degree"], "exact degree")
    key = list(algebra.zero)
    for name, exponent in packet["degree_certificate"]["monomial"].items():
        key[algebra.indices[name]] = exponent
    require(squared.get(tuple(key), 0) == packet["degree_certificate"]["coefficient"],
            "nonzero coefficient certificate on every fixed-port specialization")
    expansion = [{"powers": {algebra.names[j]: exponent for j, exponent in enumerate(key) if exponent},
                  "coefficient": coefficient} for key, coefficient in sorted(squared.items())]
    write_json(ROOT / (packet["name"]+"_expanded.json"), expansion)
    result = {"variables": n, "equations": len(rows), "residual_degrees": degrees,
              "exact_degree": packet["exact_degree"], "degree_certificate": packet["degree_certificate"],
              "symbolic_monomials": len(squared), "all_variables_live": True,
              "all_checks_exact": True}
    write_json(ROOT / "certificates" / (packet["name"]+"_CHECKS.json"), result)
    return result


def algebraic_certificates():
    algebra = Polynomial(["U", "Z", "R", "Q"])
    left = "(2*(U-1)*Z-5)**2-(U-3)*(4*U*Z**2+2)"
    right = "4*(U+1)*Z**2-20*(U-1)*Z+31-2*U"
    require(algebra.parse(left) == algebra.parse(right), "uniform signed ratio identity")
    shifted = substitute(right, {"U": "64+U", "Z": "6+Z"})
    require(all(c > 0 for c in algebra.parse(shifted).values()),
            "ratio margin has positive coefficients after U=64+u, Z=6+z")
    Bmargin = substitute("(4*Q-1)*Q**3-2-Q**4", {"Q": "16+Q"})
    require(all(c > 0 for c in algebra.parse(Bmargin).values()), "B exceeds R upper bound")
    Hmargin = substitute("4*(U-1)*Z-3-(U*Z+1)", {"U": "64+U", "Z": "6+Z"})
    require(all(c > 0 for c in algebra.parse(Hmargin).values()), "reciprocal margin")
    direct = substitute("4*(U-1)*Z-3-(U+Z)", {"U": "64+U", "Z": "6+Z"})
    require(all(c > 0 for c in algebra.parse(direct).values()), "direct residue margin")
    return {"ratio_identity_exact": True, "positive_coefficient_margin_certificates": 4,
            "note": "These polynomial identities supplement the universal proof in PROOF.md."}


def typeset_residual_check(packet):
    """Cross-check the compact displayed residual table against literal rows."""
    forms = [
        "L-q**2+1", "N-q*(L+1)", "X-q*W", "a-E-(2*v_scale+1)*N",
        "E*(X+1)-X*a", "c-eta+(E-a)*k", "P-k-E*(c-eta)",
        "tau**2-P**2+P*k-1", "D-X-a*c-gamma*(4*a+3)",
        "Delta-a**2-4*a-3", "C2-c**2", "D**2-C2*Delta-1",
        "k-1-h*E-Rlift", "(K0+W)*C-z*(q-1)-F", "F2-f**2", "V+c-f*o",
        "V-j*c+k-1-h*E", "V**2+g-y**2", "I-(2*r+1)*C2", "Baux-I**2",
        "Baux-Delta*(F2-1)", "y**2-1-Baux*g",
        "F*alpha-(1+FA_pos1**2+FA_pos2**2+FA_pos3*(FA_pos3+1))",
        "F*C-(1+FC_pos1**2+FC_pos2**2+FC_pos3*(FC_pos3+1))",
        "eta*zeta-(1+eta_zeta_pos1**2+eta_zeta_pos2**2+eta_zeta_pos3*(eta_zeta_pos3+1))"
    ]
    definitions = {
        "Rlift": "(q-F)*(N-q)-C*L+(MC+q*MF)*J0",
        "C": "q-F-alpha", "k": "eta+zeta", "q": "beta*J0+1",
        "J0": "3*J3+1", "W": "4*(3*w3+1)"}
    algebra = Polynomial(packet["variables"]+packet["fixed_numerals"])
    for i, (display, literal) in enumerate(zip(forms, packet["residuals"])):
        expanded = display
        for _ in range(4):
            expanded = substitute(expanded, definitions)
        require(algebra.parse(expanded) == algebra.parse(literal),
                "displayed table row matches literal packet: "+str(i+1))
    write_json(ROOT / "typeset_residuals.json", {"definitions": definitions, "residuals": forms,
               "notation": {"Baux": "B_0", "v_scale": "v", "Rlift": "mathcal R"},
               "checked_against": "quartic40.json"})
    result = {"rows": 25, "all_displayed_compact_forms_equal_literal_rows": True}
    write_json(ROOT / "certificates/TYPESET_RESIDUAL_CHECK.json", result)
    return result


def main():
    source_count = source_integrity()
    coefficients = rebuild_coefficients()
    q = "(beta*(3*J3+1)+1)"
    W = "(4*(3*w3+1))"
    quartic = build_quartic()
    sextic_mapping = {"N": q+"*(L+1)", "X": W+"*"+q, "C2": "c**2",
                      "F2": "f**2", "g": "y**2-V**2", "P": "eta+zeta+E*(c-eta)",
                      "tau": "tau_tail+E*(c-eta)"}
    sextic = build_projection(quartic, "sextic34", sextic_mapping, {1,2,6,10,14,17}, 6,
                             {"monomial": {"r": 2, "c": 4}, "coefficient": 4})
    k = "(1-V+j*c+h*E)"
    octic_mapping = {"L": q+"**2-1", "N": q+"**3", "X": W+"*"+q,
                    "C2": "c**2", "F2": "f**2", "g": "y**2-V**2", "Baux": "I**2",
                    "D": W+"*"+q+"+a*c+gamma*(4*a+3)", "Delta": "a**2+4*a+3",
                    "zeta": k+"-eta", "P": k+"+E*(c-eta)"}
    octic = build_projection(quartic, "octic29", octic_mapping,
                            {0,1,2,6,8,9,10,14,16,17,19}, 8,
                            {"monomial": {"a": 4, "f": 4}, "coefficient": 1})
    require(sextic["variable_count"] == 34 and sextic["equation_count"] == 19, "sextic dimensions")
    require(octic["variable_count"] == 29 and octic["equation_count"] == 14, "octic dimensions")
    direct = build_direct_quartic()
    results = {packet["name"]: audit(packet) for packet in [quartic, sextic, octic, direct]}
    results["source_files_authenticated"] = source_count
    results["coefficient_bytes"] = sum(x["bytes"] for x in coefficients.values())
    results["proof_algebra"] = algebraic_certificates()
    results["typeset_residuals"] = typeset_residual_check(quartic)
    write_json(ROOT / "certificates/VERIFIED.json", results)
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
