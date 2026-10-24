#!/usr/bin/env python3
"""Independent exact SymPy review of the shared-certificate coordinate family.

No delivered module is imported or executed.  Run using Python with SymPy:
  python coordinate-family-peer.py --directory PATH --output RECEIPT.json
"""
from __future__ import annotations

import argparse
import ast
from collections import defaultdict
import gzip
from hashlib import sha256
import io
import json
from pathlib import Path
import subprocess
import zipfile

from sympy import __version__ as sympy_version
from sympy.polys.domains import ZZ
from sympy.polys.rings import ring


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--directory", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    root = args.directory.resolve()
    names = ["incoming_joint25.json", "equations/octic25.json"] + [
        "equations/coordinate21_degree16.json",
        "equations/coordinate20_degree18.json",
        "equations/coordinate19_degree40.json",
    ]
    packets = [json.loads((root / name).read_text()) for name in names]
    ports = packets[1]["fixed_ports"]
    symbols = sorted(set(ports).union(*(set(p["variables"]) for p in packets)))
    R, *gens = ring(",".join(symbols), ZZ)
    env = dict(zip(symbols, gens))
    indices = {name: i for i, name in enumerate(symbols)}

    def parse(text, aliases=None):
        local = dict(env)
        if aliases:
            local.update(aliases)

        def visit(node):
            if isinstance(node, ast.Constant):
                require(type(node.value) is int, "noninteger constant")
                return R(node.value)
            if isinstance(node, ast.Name):
                require(node.id in local, "unbound name: " + node.id)
                return local[node.id]
            if isinstance(node, ast.UnaryOp):
                require(isinstance(node.op, (ast.USub, ast.UAdd)), "unary op")
                return -visit(node.operand) if isinstance(node.op, ast.USub) else visit(node.operand)
            require(isinstance(node, ast.BinOp), "nonarithmetic syntax")
            if isinstance(node.op, (ast.Add, ast.Sub)):
                pending = [(node, 1)]
                out = R.zero
                while pending:
                    term, sign = pending.pop()
                    if isinstance(term, ast.BinOp) and isinstance(term.op, (ast.Add, ast.Sub)):
                        pending.append((term.left, sign))
                        pending.append((term.right, -sign if isinstance(term.op, ast.Sub) else sign))
                    else:
                        out += sign*visit(term)
                return out
            if isinstance(node.op, ast.Mult):
                return visit(node.left) * visit(node.right)
            require(isinstance(node.op, ast.Pow), "nonpolynomial operation")
            require(isinstance(node.right, ast.Constant) and type(node.right.value) is int
                    and node.right.value >= 0, "nonliteral natural exponent")
            return visit(node.left) ** node.right.value

        return visit(ast.parse(text, mode="eval").body)

    def compose(p, substitution):
        return p.compose([(env[k], v) for k, v in substitution.items()])

    rows = [[parse(s) for s in p["residuals"]] for p in packets]
    incoming, baseline, row21, row20, row19 = rows
    q = parse("beta*(3*J3+1)+1")
    order = [0, 1, 2, 3, 4, 5, 6, 7, 11, 8, 9, 10, 12]
    multipliers = {2: parse("E-a"), 3: parse("-E*(c-eta)"), 5: R.one}
    require(len(baseline) == len(incoming) == 13, "baseline row count")
    for i, row in enumerate(baseline):
        require(row == incoming[order[i]] + multipliers.get(i, R.zero) * incoming[11],
                "complete incoming row bridge " + str(i))

    forward = {
        "C": q - env["F"] - env["alpha"], "Y": parse("a-E"),
        "k": parse("eta+zeta"), "tau_gap": parse("tau-E*(c-eta)"),
    }
    inverse = {
        "alpha": q - env["F"] - env["C"], "a": parse("E+Y"),
        "zeta": parse("k-eta"), "tau": parse("tau_gap+E*(c-eta)"),
    }
    for name, p in inverse.items():
        require(compose(p, forward) == env[name], "triangular inverse " + name)
    for name, p in forward.items():
        require(compose(p, inverse) == env[name], "triangular forward " + name)

    definitions = {
        "F": "(K0+4*(3*w3+1))*C-z*(beta*(3*J3+1))",
        "E": "4*(3*w3+1)*(beta*(3*J3+1)+1)*Y",
        "eta": "c-Y*k", "V": "f*o-c",
    }
    restoration21 = {k: parse(v) for k, v in definitions.items()}
    restoration21.update({
        "alpha": q-restoration21["F"]-env["C"],
        "a": restoration21["E"]+env["Y"],
        "zeta": env["k"]-restoration21["eta"],
        "tau": env["tau_gap"]+restoration21["E"]*env["Y"]*env["k"],
    })
    stages = [
        (baseline, row21, restoration21, {1, 2, 6, 7}),
        (row21, row20, {"I": parse("(2*r+1)*c**2"), "y": parse("f*o+y_gap")}, {5}),
        (row20, row19, {"Y": parse("(2*v_scale+1)")*q**3}, {0}),
    ]
    deleted_count = 0
    retained_count = 0
    for before, after, restoration, deleted in stages:
        image = []
        for i, row in enumerate(before):
            transformed = compose(row, restoration)
            if i in deleted:
                require(not transformed, "nonzero deleted monic row")
                deleted_count += 1
            else:
                image.append(transformed)
                retained_count += 1
        require(image == after, "complete row restoration")
    for name, p in forward.items():
        require(compose(p, restoration21) == env[name], "restoration/projection inverse " + name)
    require(parse("(f*o+y_gap)**2-(f*o-c)**2") ==
            parse("(c+y_gap)*(2*f*o+y_gap-c)"), "root-translation identity")

    # Expand the display separately and compare every row to the literal packet.
    compact = packets[2]["compact_specification"]
    aliases = {}
    for name, expression in compact["definitions"].items():
        aliases[name] = parse(expression, aliases)
    require([parse(s, aliases) for s in compact["residuals"]] == row21,
            "21-coordinate printed display")

    def sos_coefficient(polys, variables, wanted):
        positions = [indices[v] for v in variables]
        target = tuple(wanted.get(v, 0) for v in variables)
        result = R.zero
        for p in polys:
            groups = defaultdict(lambda: R.zero)
            for mon, coefficient in p.items():
                key = tuple(mon[i] for i in positions)
                if any(a > b for a, b in zip(key, target)):
                    continue
                port_mon = list(mon)
                for i in positions:
                    port_mon[i] = 0
                groups[key] += R.from_dict({tuple(port_mon): coefficient})
            for key, coefficient in groups.items():
                complement = tuple(b-a for a, b in zip(key, target))
                result += coefficient * groups.get(complement, R.zero)
        return result

    results = []
    targets = [({"Y": 8, "k": 8}, "1"),
               ({"r": 4, "c": 10, "f": 2, "o": 2}, "64"),
               ({"v_scale": 8, "J3": 24, "k": 8}, "2**8*3**24*beta**24")]
    for packet, polys, (target, expected) in zip(packets[2:], rows[2:], targets):
        variables = packet["variables"]
        require(packet["domain"] == "unrestricted integers", "domain")
        require(len(set(variables)) == len(variables) == packet["variable_count"], "count")
        active = set()
        degrees = []
        for p in polys:
            degrees.append(max(sum(mon[indices[v]] for v in variables) for mon in p))
            active.update(symbols[i] for mon in p for i, e in enumerate(mon) if e)
        require(set(variables) <= active <= set(variables+ports), "closedness/liveness")
        require(degrees == packet["residual_degrees"], "residual degree census")
        require(sos_coefficient(polys, variables, target) == parse(expected), "SOS coefficient")
        require(2*max(degrees) == sum(target.values()) == packet["exact_degree"], "degree")
        results.append({"variables": len(variables), "residuals": len(polys),
                        "residual_degrees": degrees, "exact_degree": packet["exact_degree"],
                        "nonzero_coefficient": expected, "monomial": target,
                        "expanded_residual_terms": sum(len(p) for p in polys)})

    # Authenticate the complete incoming ZIP, each retained member, and the old input.
    repo = Path(__file__).resolve().parents[3]
    archive_path = "docs/incoming/ConZFC_Shared_Certificates_2026-10-24.zip"
    raw = subprocess.check_output(["git", "show", "751bc067e2:"+archive_path], cwd=repo)
    expected_archive = "61582dab90e880049e61ff1a5c49386747cd063de15e18411a20f327b9559ba1"
    require(sha256(raw).hexdigest() == expected_archive, "incoming archive digest")
    matched = 0
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        for item in archive.infolist():
            marker = "/coordinate_family/"
            if not item.is_dir() and marker in item.filename:
                relative = item.filename.split(marker, 1)[1]
                require((root/relative).read_bytes() == archive.read(item), "archive member: "+relative)
                matched += 1
    pin = json.loads((root/"INCOMING_PINS.json").read_text())["literal_baseline"]
    old_raw = subprocess.check_output(["git", "show", "08200eb10fde2db408c69dffd840d6920a569b1f:docs/incoming/"+pin["archive"]], cwd=repo)
    require(sha256(old_raw).hexdigest() == pin["archive_sha256"], "original joint archive")
    with zipfile.ZipFile(io.BytesIO(old_raw)) as archive:
        old_member = archive.read(pin["member"])
    require(old_member == (root/pin["local_path"]).read_bytes(), "old literal baseline")
    require(sha256(old_member).hexdigest() == pin["sha256"], "old baseline digest")
    source_pins = json.loads((root/"SOURCE_PINS.json").read_text())
    for spec in source_pins["files"]:
        path = spec["repo_path"]
        if not path.startswith("Computability/"):
            path = source_pins["default_prefix"]+path
        original = subprocess.check_output(
            ["git", "show", source_pins["commit"]+":"+path], cwd=repo)
        require(original == (root/spec["local_path"]).read_bytes(),
                "original repository source: "+path)

    binding = json.loads((root/"COEFFICIENT_BINDING.json").read_text())
    fixed = {}
    raw_bytes = 0
    for name, spec in binding["payloads"].items():
        data = gzip.decompress((root/spec["path"]).read_bytes())
        require(sha256(data).hexdigest() == spec["raw_sha256"], "port: "+name)
        require(len(data) == spec["raw_bytes"], "port bytes: "+name)
        value = int.from_bytes(data, "little")
        require(value.bit_length() == spec["bits"], "port bits: "+name)
        fixed[name] = value
        raw_bytes += len(data)
    require(fixed["beta"] == 2**1064921-1 and fixed["cone_A"] == 2**1113
            and fixed["cone_B"] == 2**666104, "literal fixed powers")
    require(0 < fixed["MC"] < fixed["beta"] < fixed["MF"] < 2*fixed["beta"], "native mask conventions")
    require(raw_bytes == 615883 == binding["raw_bytes"], "whole tuple bytes")

    result = {"status": "PASS", "sympy_version": sympy_version,
              "optimized": not __debug__, "incoming_archive_sha256": expected_archive,
              "archive_members_matched": matched,
              "retained_sources_matched_to_original_commit": len(source_pins["files"]),
              "independent_engine": "SymPy polynomial rings over ZZ; delivered modules not imported",
              "incoming_unimodular_bridge": "13 exact rows; pivot unchanged",
              "triangular_inverse_identities": 8, "restoration_projection_identities": 4,
              "deleted_monic_rows": deleted_count, "retained_restoration_rows": retained_count,
              "complete_fixed_tuple_raw_bytes": raw_bytes, "MF_shifted_once": True,
              "results": results, "new_semantic_calibration_proved": False,
              "file_sha256": {name: sha256((root/name).read_bytes()).hexdigest() for name in names}}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
