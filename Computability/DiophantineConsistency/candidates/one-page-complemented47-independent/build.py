#!/usr/bin/env python3
"""Materialize/check the complemented47 page's integer ports and unchanged DAG."""
import argparse
from collections import Counter
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / "candidates/one-page-compact66-radix55"
CERT = ROOT / "research/complemented47-controller-independent"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def page_text():
    raw = (PARENT / "equation.tex").read_bytes()
    require(digest(raw) == "440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff",
            "Pinned parent page changed")
    text = raw.decode()
    changes = [
        (r"\rho=2^{55}", r"\rho=2^{47}"),
        (r"(2^{51}-2)\Lambda", r"(2^{46}-2)\Lambda"),
        (r"\rho^{1013}G_{10}(\rho)+\rho^{1065}G_9(\rho)",
         r"\rho^{1013}G_9(\rho)+\rho^{1065}G_8(\rho)"),
        (r"-\rho^{8792}+(2^{41}-4)\rho^{7691}",
         r"-\rho^{8792}+2^{26}\rho^{7694}-\rho^{7691}"),
        ("The ordinary state/color-conjugacy, native and Pell arguments give",
         "The ordinary complemented-color, native and Pell arguments give"),
    ]
    for before, after in changes:
        require(text.count(before) == 1, "Unexpected parent formula multiplicity")
        text = text.replace(before, after)
    start, end = text.index(r"\Phi(x)={}"), text.index(r"\end{split}")
    phi = r"""\Phi(x)={}&\sum_{i=0}^{942}[1+2^{10}(1+w_i+2^8n_i\\
&+2^{17}p_i+2^{25}s_i)]x^i\\
&+2^{10}x^{1003}(x^{20}+2^{17})G_8(2x)\\
&+2^{18}x^{983}(x^{30}+2^{17})G_9(2x)\\
&+2^{44}x^{1095}(1+x^{1100}+x^{2201}).
"""
    return (text[:start] + phi + text[end:]).encode()


def materialize():
    source = CERT / "certify.py"
    require(digest(source.read_bytes()) ==
            "318665c36d7600a99dbddbacca11ef9a2d30f65e04a761efe25d1f3653e662ed",
            "Reviewed finite verifier changed")
    completed = subprocess.run([sys.executable, "-B", str(source)], check=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(not completed.stderr, "Finite verifier reported a diagnostic")
    certificate = json.loads((CERT / "certificate.json").read_text())
    spec = importlib.util.spec_from_file_location("reviewed_complemented47", source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    _, _, tiles = module.decode_tiles()
    c = module.coefficients(tiles)

    # This materializer uses printed MC's nonzero indicator and signed MF,
    # independently of the verifier's support-based MC and positive padding.
    power = lambda e: 1 << (47 * e)
    B = power(8807)
    beta = B - 1
    MC = beta + power(1) - (power(1) + 3) * power(1063)
    MC -= sum(power(e) for e, value in enumerate(c) if value != 0)
    K = sum(power(e) for e in (30, 62, 1100, 2201, 8849))
    K += sum(value * (power(4393 - e) + power(5495 - e))
             for e, value in enumerate(c) if value)
    MF = 2 * B + 3 + ((1 << 46) - 2) * (power(4393) + power(5495))
    MF += sum(power(e) for e in range(1013, 1022))
    MF += sum(power(e) for e in range(1065, 1073))
    MF += power(2195) + power(3296) - power(8792) + (1 << 26) * power(7694) - power(7691)
    ports, files = {}, {}
    for name, record_name, value in (("beta", "beta", beta), ("K0", "K", K),
                                     ("MC", "MC", MC), ("MF", "MF_source", MF)):
        raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
        record = certificate["constants"][record_name]
        require(digest(raw) == record["sha256_big_endian"] and len(raw) == record["bytes"],
                "Independent full constant reconstruction disagrees: " + name)
        packed = gzip.compress(raw, mtime=0)
        filename = record_name + ".bin.gz"
        files["coefficients/" + filename] = packed
        ports[name] = {"file": filename, "bits": value.bit_length(), "raw_bytes": len(raw),
                       "raw_sha256": digest(raw), "gzip_sha256": digest(packed)}

    parent_raw = (PARENT / "polynomial.json").read_bytes()
    require(digest(parent_raw) == "058c48168f242f3b9aae8fd86cbe6d2b0f6fb1f336ae8082567a5edb24528066",
            "Pinned 66-gate parent changed")
    polynomial = json.loads(parent_raw)
    rows = polynomial["source"]
    require(len(rows) == 66 and dict(Counter(row[1] for row in rows)) == {"*": 38, "+": 15, "-": 13},
            "Operation ledger changed")
    known = set(polynomial["witnesses"]) | set(polynomial["fixed_numerals"])
    dependencies = {}
    for name, op, left, right in rows:
        require(name not in known, "Duplicate wire")
        require(all(isinstance(x, int) or x in known for x in (left, right)), "Undefined wire")
        dependencies[name] = {x for x in (left, right) if isinstance(x, str)}
        known.add(name)
    live, pending = set(), [polynomial["output"]]
    while pending:
        name = pending.pop()
        if name not in live:
            live.add(name)
            pending.extend(dependencies.get(name, ()))
    require(live == known, "A gate, variable or port is unused")
    polynomial["name"] = "complemented_three_anchor47_p66_degree157"
    polynomial["proof"] = "README.md"
    polynomial["proof_boundary"] = "Complete conditional native/P66 proof plus independently discharged Pc3; retained ordinary K215/refutation calibration, no new formal replay."
    polynomial["coefficient_binding"] = {
        "schema": "complemented_three_anchor47_materialized_v1", "path": "coefficients/",
        "ports": ports, "raw_bytes": 207214,
        "certificate": "../../research/complemented47-controller-independent/certificate.json",
        "certificate_sha256": digest((CERT / "certificate.json").read_bytes()),
    }
    files["polynomial.json"] = (json.dumps(polynomial, indent=2, sort_keys=True) + "\n").encode()
    files["equation.tex"] = page_text()
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="Write generated source and integer ports")
    args = parser.parse_args()
    files = materialize()
    for relative, raw in files.items():
        target = HERE / relative
        if args.build:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
        else:
            require(target.read_bytes() == raw, "Generated artifact differs: " + relative)
    print(json.dumps({"status": "PASS", "files": {name: digest(raw) for name, raw in files.items()},
                      "integer_leaf_operations": 66, "raw_constant_bytes": 207214}, sort_keys=True))


if __name__ == "__main__":
    main()
