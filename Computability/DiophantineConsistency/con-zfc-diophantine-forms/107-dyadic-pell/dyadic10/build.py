#!/usr/bin/env python3
"""Emit and check the literal ten-positive circuit p10_dyadic_degree706.json.

    python build.py            write the JSON
    python build.py --check    regenerate in memory and compare byte for byte

Both modes verify the coefficient binding (gzip and raw SHA-256, bit lengths,
B = beta+1 = 2^590069 and the mask inequalities used by the proof), the
topology (no forward reference, no dead row, every input live), the operation
counts and the syntactic degrees. The exact degree 706 is proved in PROOF.md
Section 3 and checked by audit.py. Standard library only.

The ports are read from the canonical binding next to this package. The
environment variable P10_COEFF_DIR may point to another copy of that
directory; the hashes above are checked either way.
"""
import gzip
import hashlib
import json
import os
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))      # also works under python -I
sys.dont_write_bytecode = True

import circuit  # noqa: E402

OUT = HERE / "p10_dyadic_degree706.json"
COEFF = Path(os.environ.get("P10_COEFF_DIR") or
             HERE / "coefficients")
COEFF_REL = "Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients"

# The whole compact44 tuple, as bound by package 70 (eleven/coefficients/ACTIVE_BINDING.json).
BINDING = {
    "beta": ("beta.bin.gz", 590069,
             "466796f146d60db9929fa0f0f62d70d5e6afbcea9940342764571f1ca6bea87c",
             "0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d"),
    "K0": ("K.bin.gz", 592884,
           "b70752bb38570b1e93d480469c63ace9ed4b4552f94eb89d96bc600b1e2a4b6a",
           "c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e"),
    "MC": ("MC.bin.gz", 590069,
           "271fabccdd555bda2c54c4c3a7379cc02eeba4893c07178bfd557a7683b74d5e",
           "6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4"),
    "MF": ("MF_source.bin.gz", 590070,
           "935cd87f8b23f24a20fd742c48d2a9cbca6afd494b6b074445df72c98b0c6e3b",
           "48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737"),
}


def require(cond, msg):
    if not cond:
        raise SystemExit("CHECK FAILED: " + msg)


def load_ports():
    ports = {}
    for name, (fn, bits, gz_sha, raw_sha) in BINDING.items():
        blob = (COEFF / fn).read_bytes()
        require(hashlib.sha256(blob).hexdigest() == gz_sha, f"gzip SHA-256 of {fn}")
        raw = gzip.decompress(blob)
        require(hashlib.sha256(raw).hexdigest() == raw_sha, f"raw SHA-256 of {fn}")
        value = int.from_bytes(raw, "little")
        require(value.bit_length() == bits, f"bit length of {name}")
        require(len(raw) == (bits + 7) // 8, f"minimal encoding of {name}")
        ports[name] = value
    beta, K0, MC, MF = (ports[x] for x in ("beta", "K0", "MC", "MF"))
    require(beta + 1 == 1 << 590069, "B = beta + 1 = 2^590069")
    require(beta % 2 == 1, "beta odd (so q is even when J is odd)")
    require(0 < MC < beta, "0 < MC < beta")
    require(beta < MF < 2 * beta, "beta < MF < 2 beta (MF already shifted)")
    require(K0 > 0, "K0 > 0")
    return ports


def check_topology(source):
    available = set(circuit.WITNESSES + circuit.FIXED)
    for name, op, x, y in source:
        require(name not in available, "duplicate register " + name)
        require(op in ("+", "-", "*"), "unknown operation " + op)
        for arg in (x, y):
            require(isinstance(arg, int) or arg in available, f"forward reference {arg} in {name}")
        available.add(name)
    needed = {circuit.OUTPUT}
    for name, op, x, y in reversed(source):
        if name in needed:
            needed.update(a for a in (x, y) if isinstance(a, str))
    require(all(r[0] in needed for r in source), "dead row")
    require(set(circuit.WITNESSES + circuit.FIXED) <= needed, "dead input")
    require(source[-1][0] == circuit.OUTPUT, "output is the last row")


REGISTERS = ("q", "X", "c", "a", "mu", "Am1", "Hp", "Dp", "V0", "Dtau", "R", "I", "Df", "Q",
             "V", "Dnum", "Dmain", "L", "LBt", "Mtot", "Znum", "fs", "fa", "fb", "fc", "fd", "N")


def packet():
    source = circuit.rows()
    check_topology(source)
    counts = Counter(r[1] for r in source)
    require(len(source) == 133, "133 operations")
    require(dict(counts) == {"*": 79, "+": 33, "-": 21}, "operation breakdown")
    deg = circuit.syntactic_degrees(source)
    require(deg["N"] == 832 and deg["fs"] == deg["fc"] == 104, "syntactic degree 832")
    require(max(deg[x] for x in ("fa", "fb", "fd")) == 76, "other arguments of degree at most 76")
    return {
        "name": "p10_dyadic_degree706",
        "domain": "strictly positive integers",
        "witnesses": circuit.WITNESSES,
        "fixed_numerals": circuit.FIXED,
        "source": [[n, o, x, y] for n, o, x, y in source],
        "output": circuit.OUTPUT,
        "operations": len(source),
        "operation_breakdown": {"*": counts["*"], "+": counts["+"], "-": counts["-"]},
        "exact_degree": 706,
        "syntactic_degree": deg["N"],
        "register_degrees": {k: deg[k] for k in REGISTERS},
        "coefficient_binding": {
            "path": COEFF_REL,
            "ports": {k: {"file": v[0], "bits": v[1], "gzip_sha256": v[2], "raw_sha256": v[3]}
                      for k, v in BINDING.items()},
            "note": "whole compact44 tuple; MF is already shifted and must not be shifted again",
        },
        "proof_status": "ordinary existence proof (PROOF.md); inherits package 61's "
                        "compiler/calibration interface; not an end-to-end formal certificate",
    }


def render(p):
    """Indented JSON with one circuit row per line."""
    lines = ["{"]
    keys = list(p)
    for idx, key in enumerate(keys):
        tail = "," if idx + 1 < len(keys) else ""
        if key == "source":
            lines.append(' "source": [')
            src = p["source"]
            for r, row in enumerate(src):
                lines.append("  " + json.dumps(row) + ("," if r + 1 < len(src) else ""))
            lines.append(" ]" + tail)
        else:
            body = json.dumps(p[key], indent=1, ensure_ascii=True).replace("\n", "\n ")
            lines.append(" " + json.dumps(key) + ": " + body + tail)
    lines.append("}")
    return "\n".join(lines) + "\n"


def main():
    load_ports()
    text = render(packet())
    if "--check" in sys.argv[1:]:
        require(OUT.read_text(encoding="utf-8") == text, OUT.name + " is stale")
        print("build --check: OK (133 operations, syntactic degree 832, ports bound)")
    else:
        OUT.write_text(text, encoding="utf-8", newline="\n")
        print("wrote", OUT.name)


if __name__ == "__main__":
    main()
