#!/usr/bin/env python3
"""Build/check the complete scaled_clause2953 source page and four integer ports."""
import argparse
from collections import Counter
import gzip
import hashlib
import importlib.util
import json
import re
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / "candidates/one-page-block-mask2963"
CERT = ROOT / "research/scaled-clause-independent"
VERIFIER_SHA = "bebbdc8e5fb70a41e84df0b7378fec09094ff5a571929ab8b113831e8c971e05"
CERTIFICATE_SHA = "957faf013a17c2e8e04c03be166d903263d2aadaccac604d31f0791e005776ed"
PARENT_TEX_SHA = "fb2d1400771754a95e5aaf886917d342989138a228fe13dd20e0c633d46dcc61"
PARENT_DAG_SHA = "8837fbf8d705af33304c8a61c2238c7889950df7347fca289c45ac68f4636380"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def record(raw):
    return {"bytes": len(raw), "sha256": digest(raw)}


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def page_text():
    raw = (PARENT / "equation.tex").read_bytes()
    require(digest(raw) == PARENT_TEX_SHA, "Pinned complete parent page changed")
    text = raw.decode()
    replacements = ((r"B=\rho^{2963}", r"B=\rho^{2953}"),
                    (r"\Lambda=\rho^{1956}", r"\Lambda=\rho^{1945}"),
                    (r"(2^{44}-2)\Lambda", r"(2^{45}-4)\Lambda"),
                    (r"\rho^{2972}", r"\rho^{2962}"),
                    (r"+\Lambda\Phi(1/\rho)", r"+2\Lambda\Phi(1/\rho)"))
    for old, new in replacements:
        require(text.count(old) == 1, "Exact whole parent scalar recipe occurs once")
        text = text.replace(old, new)
    require(len(text.encode()) == 4971, "Complete scaled2953 source byte count")
    return text.encode()


def printed_scale(text):
    start = text.index(r"K={}")
    end = text.index(r"\end{align*}", start)
    block = text[start:end]
    expected = r"""K={}&\rho^{18}+\rho^{1005}+\rho^{2962}\\
&+2\Lambda\Phi(1/\rho),
"""
    require(block == expected, "Entire printed scaled K recipe")
    return 2


INLINE_PHI = r"""\Phi(x)={}&\sum_{i=0}^{941}[1+2^{10}(1+w_i+2^8n_i\\
&+2^{17}p_i+2^{25}s_i)]x^i\\
&+2^{10}x^{969}(x^9+2^{17})G_8(2x)\\
&+2^{18}x^{942}(x^{18}+2^{17})G_9(2x).
"""


PRINTED_TABLE = r"""\begin{array}{c|l}
\text{index }i&\text{tile }t_i=(w_i,n_i,p_i,s_i)\\\hline
0&(2,435,3,1)\\
j+1\ (j=2q+b<430)&((1-d_j)r_{0,u_j},h(q,b),d_jr_{1,u_j},v_j)\\
433-2a+b\ (a,b=0,1)&(0,432a+b,0,432a+b)\\
\substack{423+2r_{d,q}+b\\q\in\mathcal S_d,\ d,b=0,1}&(dr_{d,q},b,(1-d)r_{d,q},h(q,b))\\
923+2a+b\ (a,b=0,1)&(0,432a+b,0,438)\\
927&(2,434,2,0)\\
928&(3,436,4,4)\\
929&(4,436,4,0)\\
496+t\ (t=434,435,436)&(1,438,1,t)\\
933+3a+b\ (a,b=0,1,2)&(a^2,437,b,437)
\end{array}"""


def printed_tiles(text, actions):
    """Transcribe every exact new printed row, independently of the g map."""
    start = text.index(r"\begin{array}{c|l}")
    end = text.index(r"\end{array}", start) + len(r"\end{array}")
    require(text[start:end] == PRINTED_TABLE, "Entire printed942 tile table")
    states = [{u for u, v, d in actions if d == direction} for direction in (0, 1)]
    rank = {(d, q): 205 - 199 * d + sum(v < q for v in states[d])
            for d in (0, 1) for q in states[d]}
    table = {}

    def insert(index, tile):
        require(index not in table, "Unique index in printed942 table")
        table[index] = tile

    insert(0, (2, 435, 3, 1))
    for j, (u, v, direction) in enumerate(actions):
        insert(j + 1, ((1 - direction) * rank.get((0, u), 0), j + 2,
                       direction * rank.get((1, u), 0), v))
    for a in (0, 1):
        for b in (0, 1):
            insert(433 - 2 * a + b, (0, 432 * a + b, 0, 432 * a + b))
            insert(923 + 2 * a + b, (0, 432 * a + b, 0, 438))
    for direction in (0, 1):
        for q in sorted(states[direction]):
            rr = rank[direction, q]
            for b in (0, 1):
                insert(423 + 2 * rr + b, (direction * rr, b, (1 - direction) * rr, 2 * q + b + 2))
    for index, tile in ((927, (2, 434, 2, 0)), (928, (3, 436, 4, 4)), (929, (4, 436, 4, 0))):
        insert(index, tile)
    for t in (434, 435, 436):
        insert(496 + t, (1, 438, 1, t))
    for a in range(3):
        for b in range(3):
            insert(933 + 3 * a + b, (a * a, 437, b, 437))
    require(set(table) == set(range(942)), "Every printed tile index0..941 covered once")
    ordered = [table[j] for j in range(942)]
    require(len(set(ordered)) == 942 and ordered[928] == (3, 436, 4, 4),
            "All942 tiles distinct and exact initializer928")
    return ordered


def printed_coefficients(text, tiles):
    """Expand the complete exact inline Phi block independently of physical MC."""
    start = text.index(r"\Phi(x)")
    end = text.index(r"\end{split}", start)
    require(text[start:end] == INLINE_PHI, "Entire printed inline Phi recipe")
    c = [0] * 3297
    for j, (w, n, east, south) in enumerate(tiles):
        c[j] = 1 + 1024 * (1 + w + 256 * n + 131072 * east + 33554432 * south)
    for j in range(8):
        c[978 + j] += 1 << (10 + j)
        c[969 + j] += 1 << (27 + j)
    for j in range(9):
        c[960 + j] += 1 << (18 + j)
        c[942 + j] += 1 << (35 + j)
    return c


def printed_physical(text):
    """Read every subtractand in the actual MC block's narrow geometric grammar."""
    start = text.index(r"M_C={}")
    end = text.index(r"M_F={}", start)
    block = text[start:end].replace("&", "").replace("\\\\", "").replace("\n", "")
    prefix = r"M_C={}\beta"
    require(block.startswith(prefix) and block.endswith(","), "Complete printed MC boundaries")
    remaining = block[len(prefix):-1]
    term = re.compile(r"-(?:\\rho\^\{([0-9]+)\})?(?:G_(?:\{([0-9]+)\}|([0-9]+))\(\\rho\))?")
    physical = [0] * 3297
    while remaining:
        match = term.match(remaining)
        require(match is not None and any(v is not None for v in match.groups()),
                "Every actual MC subtractand has the supported geometric grammar")
        exponent = int(match.group(1) or 0)
        count = int(match.group(2) or match.group(3) or 1)
        require(count > 0 and exponent + count <= len(physical), "Complete MC index range")
        for e in range(exponent, exponent + count):
            physical[e] += 1
        remaining = remaining[match.end():]
    require(all(v in (0, 1) for v in physical), "MC physical subtractands are disjoint")
    return physical


def validate_printed(text, tiles, c, support):
    printed_c = printed_coefficients(text, tiles)
    physical = printed_physical(text)
    scale = printed_scale(text)
    require([scale * value for value in printed_c] == c,
            "All3297 doubled weights from the actual base Phi and printed factor2")
    require({e for e, v in enumerate(physical) if v} == support,
            "Entire physical support, including zero-weight marker and dummy")
    return printed_c, physical


def materialize():
    source_raw = (CERT / "certify.py").read_bytes()
    certificate_raw = (CERT / "certificate.json").read_bytes()
    require(digest(source_raw) == VERIFIER_SHA, "Reviewed finite verifier changed")
    require(digest(certificate_raw) == CERTIFICATE_SHA, "Reviewed finite certificate changed")
    command = [sys.executable, "-B"]
    if sys.flags.optimize:
        command.append("-O" if sys.flags.optimize == 1 else "-OO")
    command.append(str(CERT / "certify.py"))
    completed = subprocess.run(command, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(not completed.stderr, "Finite verifier reported a diagnostic")
    report = json.loads(completed.stdout)
    require(report["status"] == "PASS" and report["certificate_sha256"] == CERTIFICATE_SHA,
            "Finite verifier did not authenticate the expected certificate")
    certificate = json.loads(certificate_raw)
    require(certificate["script_sha256"] == VERIFIER_SHA, "Certificate verifier binding")
    proof_raw = (CERT / "PROOF.md").read_bytes()
    require(digest(proof_raw) == certificate["proof_sha256"], "Whole ordinary proof binding")

    spec = importlib.util.spec_from_file_location("reviewed_scaled_clause2953", CERT / "certify.py")
    require(spec is not None and spec.loader is not None, "Reviewed verifier module")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    _, seed, actions, tiles, c, support = module.model()
    canonical, _ = module.constants(c, support)
    require(len(seed) == 436 and len(actions) == 430 and len(tiles) == 942,
            "Whole finite language dimensions")

    page = page_text()
    require(printed_tiles(page.decode(), actions) == tiles,
            "Every printed reindexed tile equals the complete admissible g-map")
    printed_c, physical = validate_printed(page.decode(), tiles, c, support)
    require(len(c) == 3297 and c[1005] == 0 and c[977] == 0,
            "Zero-weight physical flag and sole dummy coefficient")
    require(all(value == 0 for value in c[986:]), "Complete weighted zero tail")
    require(sum(physical) == 978 and physical[977] == physical[1005] == 1,
            "Complete physical blocks retain both zero-weight positions")
    require(len(support) == 978, "Whole physical support size")

    controls = {}
    corrupted_table = page.decode().replace("928&(3,436,4,4)", "929&(3,436,4,4)")
    try:
        printed_tiles(corrupted_table, actions)
    except ValueError as error:
        controls["actual_TeX_initializer_reindexing_rejected"] = str(error) == "Entire printed942 tile table"
    else:
        controls["actual_TeX_initializer_reindexing_rejected"] = False
    variants = {
        "marker": page.decode().replace(r"-\rho^{1005},\\", r",\\", 1),
        "dummy": page.decode().replace(r"\rho^{960}G_{26}(\rho)",
                  r"\rho^{960}G_{17}(\rho)-\rho^{978}G_8(\rho)", 1),
    }
    for name, position in (("marker", 1005), ("dummy", 977)):
        corrupted = variants[name]
        require(corrupted != page.decode(), "Actual printed MC mutation took effect")
        corrupt_c = printed_coefficients(corrupted, tiles)
        corrupt_physical = printed_physical(corrupted)
        expected = physical.copy()
        expected[position] = 0
        require([2 * value for value in corrupt_c] == c and corrupt_physical == expected,
                "Actual MC mutation removes exactly its physical position while Phi stays equal")
        try:
            validate_printed(corrupted, tiles, c, support)
        except ValueError as error:
            controls["actual_TeX_" + name + "_deletion_rejected"] = str(error) == "Entire physical support, including zero-weight marker and dummy"
        else:
            controls["actual_TeX_" + name + "_deletion_rejected"] = False
    corrupt_weight = page.decode().replace(r"+2^{18}x^{942}", r"+2^{17}x^{942}", 1)
    try:
        printed_coefficients(corrupt_weight, tiles)
    except ValueError as error:
        controls["actual_TeX_inline_weight_corruption_rejected"] = str(error) == "Entire printed inline Phi recipe"
    else:
        controls["actual_TeX_inline_weight_corruption_rejected"] = False
    corrupt_scale = page.decode().replace(r"+2\Lambda\Phi(1/\rho)", r"+\Lambda\Phi(1/\rho)", 1)
    require(corrupt_scale != page.decode(), "Actual printed factor2 mutation took effect")
    try:
        validate_printed(corrupt_scale, tiles, c, support)
    except ValueError as error:
        controls["actual_TeX_missing_scale_rejected"] = str(error) == "Entire printed scaled K recipe"
    else:
        controls["actual_TeX_missing_scale_rejected"] = False
    require(all(controls.values()), "Changed actual source recipes were not rejected")

    power = lambda e: 1 << (47 * e)
    B, beta = power(2953), power(2953) - 1
    MC = beta - sum(value * power(e) for e, value in enumerate(physical) if value)
    for name, position in (("marker", 1005), ("dummy", 977)):
        corrupt_MC = beta - sum(v * power(e) for e, v in enumerate(printed_physical(variants[name])) if v)
        require(corrupt_MC == MC + power(position)
                and corrupt_MC.bit_count() == MC.bit_count() + 1
                and power(position) & (MC + 1) == 0
                and power(position) & (corrupt_MC + 1) != 0,
                "Whole actual corrupted printed mask forbids the omitted bit")
    K = sum(power(e) for e in (18, 1005, 2962))
    K += printed_scale(page.decode()) * sum(value * power(1945 - e)
             for e, value in enumerate(printed_c) if value)
    MF = beta + 4 * sum(power(e) for e in range(917)) + ((1 << 45) - 4) * power(1945)
    MF += sum(power(e) for e in range(960, 969))
    MF += sum(power(e) for e in range(987, 995)) + power(1005)
    printed = {"beta": beta, "K": K, "MC": MC, "MF_source": MF}
    require(printed == canonical, "All four printed constants equal certify.constants")

    files, ports = {}, {}
    for name, key in (("beta", "beta"), ("K0", "K"), ("MC", "MC"), ("MF", "MF_source")):
        value = printed[key]
        require(value > 0, "Positive fixed integer")
        raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
        expected = certificate["constant_ports"][key]
        require(record(raw) == {"bytes": expected["bytes"], "sha256": expected["sha256"]}
                and value.bit_length() == expected["bits"], "Whole constant mismatch: " + name)
        packed = gzip.compress(raw, mtime=0)
        filename = key + ".bin.gz"
        files["coefficients/" + filename] = packed
        ports[name] = {"file": filename, "bits": value.bit_length(), "raw_bytes": len(raw),
                       "raw_sha256": digest(raw), "gzip_sha256": digest(packed)}
    raw_bytes = sum(port["raw_bytes"] for port in ports.values())
    require(raw_bytes == 69449 == certificate["raw_bytes"], "Whole coherent byte count")

    parent_raw = (PARENT / "polynomial.json").read_bytes()
    require(digest(parent_raw) == PARENT_DAG_SHA, "Pinned complete66-gate parent changed")
    polynomial = json.loads(parent_raw)
    rows = polynomial["source"]
    counts = dict(Counter(row[1] for row in rows))
    require(len(rows) == 66 and counts == {"*": 38, "+": 15, "-": 13}, "Exact operation ledger")
    require(polynomial["witnesses"] == ["J", "F", "alpha", "z", "f", "h", "i", "T", "s", "w",
                                        "tau", "eta", "zeta", "y", "gamma"]
            and polynomial["fixed_numerals"] == ["beta", "K0", "MC", "MF"], "All15+4 input leaves")
    known = set(polynomial["witnesses"]) | set(polynomial["fixed_numerals"])
    dependencies = {}
    for name, op, left, right in rows:
        require(name not in known and op in {"+", "-", "*"}, "Unique typed wire")
        require(all(type(x) is int or x in known for x in (left, right)), "Backward wire reference")
        dependencies[name] = {x for x in (left, right) if isinstance(x, str)}
        known.add(name)
    live, pending = set(), [polynomial["output"]]
    while pending:
        name = pending.pop()
        if name not in live:
            live.add(name)
            pending.extend(dependencies.get(name, ()))
    require(live == known, "Every operation and every input must be live")
    polynomial["name"] = "scaled_clause2953_p66_degree157"
    polynomial["proof"] = "README.md"
    polynomial["proof_boundary"] = "Complete doubled-clause2953 native/P66 ordinary proof plus discharged Pcsc; retained K215/refutation calibration, no new formal-kernel replay."
    polynomial["coefficient_binding"] = {
        "schema": "scaled_clause2953_materialized_v1", "path": "coefficients/",
        "ports": ports, "raw_bytes": raw_bytes,
        "certificate": "../../research/scaled-clause-independent/certificate.json",
        "certificate_sha256": CERTIFICATE_SHA,
        "ordinary_proof": "../../research/scaled-clause-independent/PROOF.md",
        "ordinary_proof_sha256": certificate["proof_sha256"],
    }
    files["polynomial.json"] = encoded(polynomial)
    files["equation.tex"] = page_text()
    files["BUILD_AUDIT.json"] = encoded({
        "schema": "scaled_clause2953_printed_recipe_audit_v1",
        "all3297_scaled_weights_equal_twice_printed_base_Phi": True, "nonzero_Phi_coefficients": 976,
        "all942_printed_tiles_equal_admissible_bijection": True,
        "initializer_index": 928, "physical_positions_all_allowed": True,
        "physical_blocks": [[0, 950], [960, 985], [1005, 1005]], "physical_support_positions": 978,
        "flag_coefficient": {"1005": 0}, "physical_flag_present": True,
        "zero_tail": [986, 3296], "negative_controls": controls,
        "all_four_printed_integers_equal_canonical": True, "raw_bytes": raw_bytes,
        "operations": 66, "operation_counts": counts, "all15_variables_and4_ports_live": True,
        "exact_degree": 157, "degree_basis": "Identical full free-port66 DAG; retained nonzero leading coefficient8*beta^92.",
        "certificate_sha256": CERTIFICATE_SHA, "verifier_sha256": VERIFIER_SHA,
        "ordinary_proof_sha256": certificate["proof_sha256"],
        "parent_page_sha256": PARENT_TEX_SHA, "parent_polynomial_sha256": PARENT_DAG_SHA,
        "base_Phi_unchanged": True, "printed_K_weight_scale": 2, "identical_specialized_polynomial": False,
        "scope": "Complete source-page reconstruction and whole constants; no PDF, native compiler or formal-kernel execution.",
    })
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="Write generated source and integer ports")
    args = parser.parse_args()
    files = materialize()
    closure = dict(files)
    closure["README.md"] = (HERE / "README.md").read_bytes()
    closure["build.py"] = Path(__file__).read_bytes()
    files["SOURCE_MANIFEST.json"] = encoded({
        "schema": "scaled_clause2953_source_bundle_v1",
        "files": {name: record(raw) for name, raw in sorted(closure.items())},
        "finite_certificate": "research/scaled-clause-independent/certificate.json",
        "finite_certificate_sha256": CERTIFICATE_SHA,
        "ordinary_proof": "research/scaled-clause-independent/PROOF.md",
        "ordinary_proof_sha256": json.loads((CERT / "certificate.json").read_bytes())["proof_sha256"],
        "scope": "Complete deterministic source/ports bundle. PDF and visual receipts belong to a separate rendering manifest.",
    })
    for relative, raw in files.items():
        target = HERE / relative
        if args.build:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
        else:
            require(target.read_bytes() == raw, "Generated artifact differs: " + relative)
    print(json.dumps({"status": "PASS", "files": {name: digest(raw) for name, raw in files.items()},
                      "integer_leaf_operations": 66, "raw_constant_bytes": 69449,
                      "all3297_Phi_coefficients": True, "all978_support_positions": True}, sort_keys=True))


if __name__ == "__main__":
    main()
