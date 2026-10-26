#!/usr/bin/env python3
"""Build/check the complete block_mask2963 source page and four integer ports."""
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
PARENT = ROOT / "candidates/one-page-low-padding2963"
CERT = ROOT / "research/low-padding-independent"
VERIFIER_SHA = "86dae914161f5f030cd1c575e6448e029542a18718cadf732c2d5a673adc3cc7"
CERTIFICATE_SHA = "d165186ba400ebc2074716d2e1a142505b93c6d150b3f1fc44e574e9664ca039"
PARENT_TEX_SHA = "7c9cc96b35c33d0d8de643caa816148d252c7eb3cc64ac4d925714788d263397"
PARENT_DAG_SHA = "a9a752b912689d1f2418ce1dcc149670a1a3e80843f9ca635131fb8f43693c61"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def record(raw):
    return {"bytes": len(raw), "sha256": digest(raw)}


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


IDENTITY = ROOT / "research/block-mask-recipe/CERTIFICATE.json"
IDENTITY_SHA = "16d501fe425b40780843a0f628271f9e1c8c27e94351e70cc4976ad311e383d7"


def page_text():
    raw = (PARENT / "equation.tex").read_bytes()
    require(digest(raw) == PARENT_TEX_SHA, "Pinned complete parent page changed")
    identity_raw = IDENTITY.read_bytes()
    require(digest(identity_raw) == IDENTITY_SHA, "Reviewed formal recipe identity changed")
    identity = json.loads(identity_raw)
    text = raw.decode()
    before = identity["exact_tex_blocks"]["before"]
    after = identity["exact_tex_blocks"]["inline"]
    before_mc, before_phi = before.split(r"\Phi(x)", 1)
    after_mc, after_phi = after.split(r"\Phi(x)", 1)
    for old, new in ((before_mc, after_mc), (r"\Phi(x)" + before_phi, r"\Phi(x)" + after_phi)):
        require(text.count(old) == 1, "Exact whole parent recipe block occurs once")
        text = text.replace(old, new)
    result = text.encode()
    require(digest(result) == identity["projected_full_page"]["sha256"]
            and len(result) == 4970 and r"\Psi" not in text,
            "Entire projected identity source, with no remaining Psi helper")
    return result


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
    require(printed_c == c, "All3297 weighted Phi coefficients")
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

    spec = importlib.util.spec_from_file_location("reviewed_block_mask2963", CERT / "certify.py")
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
        require(corrupt_c == c and corrupt_physical == expected,
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
    require(all(controls.values()), "Changed actual source recipes were not rejected")

    power = lambda e: 1 << (47 * e)
    B, beta = power(2963), power(2963) - 1
    MC = beta - sum(value * power(e) for e, value in enumerate(physical) if value)
    for name, position in (("marker", 1005), ("dummy", 977)):
        corrupt_MC = beta - sum(v * power(e) for e, v in enumerate(printed_physical(variants[name])) if v)
        require(corrupt_MC == MC + power(position)
                and corrupt_MC.bit_count() == MC.bit_count() + 1
                and power(position) & (MC + 1) == 0
                and power(position) & (corrupt_MC + 1) != 0,
                "Whole actual corrupted printed mask forbids the omitted bit")
    K = sum(power(e) for e in (18, 1005, 2972))
    K += sum(value * power(1956 - e)
             for e, value in enumerate(printed_c) if value)
    MF = beta + 4 * sum(power(e) for e in range(917)) + ((1 << 44) - 2) * power(1956)
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
    require(raw_bytes == 69685 == certificate["raw_bytes"], "Whole coherent byte count")

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
    polynomial["name"] = "block_mask2963_p66_degree157"
    polynomial["proof"] = "README.md"
    polynomial["proof_boundary"] = "Exact block-mask identity at the complete Low-padding2963 native/P66 ordinary proof plus discharged Pclp; retained K215/refutation calibration, no new formal-kernel replay."
    polynomial["coefficient_binding"] = {
        "schema": "block_mask2963_materialized_v1", "path": "coefficients/",
        "ports": ports, "raw_bytes": raw_bytes,
        "certificate": "../../research/low-padding-independent/certificate.json",
        "certificate_sha256": CERTIFICATE_SHA,
        "ordinary_proof": "../../research/low-padding-independent/PROOF.md",
        "ordinary_proof_sha256": certificate["proof_sha256"],
    }
    files["polynomial.json"] = encoded(polynomial)
    files["equation.tex"] = page_text()
    files["BUILD_AUDIT.json"] = encoded({
        "schema": "block_mask2963_printed_recipe_audit_v1",
        "all3297_Phi_coefficients_equal": True, "nonzero_Phi_coefficients": 976,
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
        "exact_recipe_identity_sha256": IDENTITY_SHA, "identical_specialized_polynomial": True,
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
        "schema": "block_mask2963_source_bundle_v1",
        "files": {name: record(raw) for name, raw in sorted(closure.items())},
        "exact_recipe_identity": "research/block-mask-recipe/CERTIFICATE.json",
        "exact_recipe_identity_sha256": IDENTITY_SHA,
        "finite_certificate": "research/low-padding-independent/certificate.json",
        "finite_certificate_sha256": CERTIFICATE_SHA,
        "ordinary_proof": "research/low-padding-independent/PROOF.md",
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
                      "integer_leaf_operations": 66, "raw_constant_bytes": 69685,
                      "all3297_Phi_coefficients": True, "all978_support_positions": True}, sort_keys=True))


if __name__ == "__main__":
    main()
