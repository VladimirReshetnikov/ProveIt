#!/usr/bin/env python3
"""Check an exact weighted-only Psi refactor of all four admissible942 ports."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / "research/admissible942-independent/certify.py"
PARENT_SHA = "cdd9020f6134870063b1cf5feb1e57d85406afe18070f3cf1d56f32711c49262"
PROOF = ROOT / "research/admissible942-independent/PROOF.md"
PROOF_SHA = "c181f726f07ed1803d4128f8dc739c78af2c5220acba0e0779d4bf33ecb2ded2"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    require(sha(PARENT.read_bytes()) == PARENT_SHA, "Exact frozen complete admissible942 verifier")
    require(sha(PROOF.read_bytes()) == PROOF_SHA, "Exact frozen complete admissible942 proof")
    spec = importlib.util.spec_from_file_location("weighted_psi_frozen_parent", PARENT)
    require(spec is not None and spec.loader is not None, "Parent import specification")
    parent = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parent)
    _, seed, actions, tiles, old_c, support = parent.model()
    old_whole, old_dc = parent.constants(old_c, support)
    cfg, length = parent.SPEC, parent.L
    require(length == 4027 and cfg["anchor"] == 1005 and cfg["dummy"] == 977,
            "Exact intended recipe interface")
    power = lambda e: 1 << (47 * e)
    marker, dummy = power(cfg["anchor"]), power(cfg["dummy"])
    rho, B = power(1), power(length)
    old_arrays, weighted_arrays = {}, {}
    for t in (1, 2):
        labels = [0] * len(old_c)
        for j in range(8):
            labels[cfg["east"] + j] = t ** j
            labels[cfg["west"] + j] = t ** (17 + j)
        for j in range(9):
            labels[cfg["north"] + j] = t ** (8 + j)
            labels[cfg["south"] + j] = t ** (25 + j)
        old = labels.copy()
        old[cfg["anchor"]] += 2 - t
        require(sum(bool(v) for v in labels) == 34 and labels[cfg["anchor"]] == 0,
                "Exactly34 weighted label positions; marker remains separate")
        require(old == [value + ((2 - t) if e == cfg["anchor"] else 0)
                        for e, value in enumerate(labels)], "Entire old/new polynomial array identity")
        old_arrays[t], weighted_arrays[t] = old, labels
    require(old_arrays[2] == weighted_arrays[2], "Complete weighted specialization is identical")
    require(sum(old_arrays[1]) == 35 and sum(weighted_arrays[1]) == 34,
            "Exact support-specialization population change")
    c = [0] * len(old_c)
    for j, (w, n, east, south) in enumerate(tiles):
        c[j] = 1 + 1024 * (1 + w + 256 * n + 131072 * east + 33554432 * south)
    c = [value + 1024 * weight for value, weight in zip(c, weighted_arrays[2])]
    require(c == old_c, "Every coefficient of the full3297-slot Phi is unchanged")
    physical = set(range(942)) | {e for e, value in enumerate(weighted_arrays[1]) if value}
    physical |= {cfg["dummy"], cfg["anchor"]}
    require(physical == support and len(physical) == 978,
            "Full physical support retains the zero-weight marker explicitly")
    weighted_one = sum(value * power(e) for e, value in enumerate(weighted_arrays[1]))
    selector_block = sum(power(e) for e in range(942))
    MC = B - 1 - dummy - marker - selector_block - weighted_one
    dc = sum(value * (power(cfg["centers"][0] - e) + power(cfg["centers"][1] - e))
             for e, value in enumerate(c) if value)
    dc += power(18) + marker
    K = dc + power(length + 9)
    core = sum(power(cfg["north"] + j) for j in range(9))
    core += sum(power(cfg["west"] + 18 + j) for j in range(8)) + marker
    clause = sum(power(e) for e in cfg["centers"])
    MF = B + 3 + ((1 << 44) - 2) * clause + core
    MF += (1 << 27) * power(cfg["padding"] + 18) - power(cfg["padding"])
    whole = {"beta": B - 1, "K": K, "MC": MC, "MF_source": MF}
    require(whole == old_whole and dc == old_dc,
            "Exact whole equality of beta,K,MC,MF_source and DC")
    native = MF - (B - 1)
    require(MC.bit_count() == 47 * length - 978 and native.bit_count() == 978,
            "Unchanged complete complementary populations")
    # Dropping the marker from Psi without its explicit MC term is not valid.
    bad_MC = MC + marker
    require(bad_MC != MC and bad_MC.bit_count() == 47 * length - 977,
            "Actual MC-marker deletion changes the whole mask population")
    require(marker & (MC + 1) == 0 and marker & (bad_MC + 1) != 0,
            "Physical marker accepted before deletion and forbidden after deletion")
    before = r"""M_C={}&\beta-\rho^{977}\\
&-G_{942}(\rho)-\Psi(\rho,1),\\
\Psi(x,t)={}&x^{969}(x^9+t^{17})G_8(tx)\\
&+t^8x^{942}(x^{18}+t^{17})G_9(tx)\\
&+(2-t)x^{1005}.
"""
    after = r"""M_C={}&\beta-\rho^{977}-\rho^{1005}\\
&-G_{942}(\rho)-\Psi(\rho,1),\\
\Psi(x,t)={}&x^{969}(x^9+t^{17})G_8(tx)\\
&+t^8x^{942}(x^{18}+t^{17})G_9(tx).
"""
    ports = {}
    for name, value in whole.items():
        raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
        ports[name] = {"bits": value.bit_length(), "bytes": len(raw), "sha256": sha(raw)}
    data = {
        "schema": "weighted_only_Psi_exact_port_identity_v1",
        "script_sha256": sha(Path(__file__).read_bytes()), "parent_verifier_sha256": PARENT_SHA,
        "parent_proof_sha256": PROOF_SHA,
        "identity": "Psi_old(x,t)=Psi_weighted(x,t)+(2-t)*x^1005; t=1,2",
        "specializations": {str(t): {"old_sha256": sha(encoded(old_arrays[t])),
                                       "weighted_sha256": sha(encoded(weighted_arrays[t]))} for t in (1, 2)},
        "all3297_coefficients_sha256": sha(encoded(c)), "physical_positions": len(physical),
        "marker_position": cfg["anchor"], "weighted_label_positions": 34,
        "whole_ports": ports, "raw_bytes": sum(row["bytes"] for row in ports.values()),
        "actual_marker_deletion_negative": {"MC_population": bad_MC.bit_count(),
                                             "required_MC_population": 47 * length - 978,
                                             "physical_marker_forbidden": True},
        "exact_tex_blocks": {"before": before, "after": after,
                             "before_bytes": len(before.encode()), "after_bytes": len(after.encode()),
                             "saved_bytes": len(before.encode()) - len(after.encode()),
                             "scope": "Complete MC and Psi literal blocks including their line breaks; no full-page length claim."},
        "scope": "Exact identity of the complete fixed tuple and hence the specialized P66 polynomial. No new native witness map or lower raw-byte record."
    }
    require(data["raw_bytes"] == 94689 and data["exact_tex_blocks"]["saved_bytes"] > 0,
            "Exact unchanged raw size and shorter displayed recipe blocks")
    raw = encoded(data)
    path = HERE / "CERTIFICATE.json"
    if args.write:
        path.write_bytes(raw)
    else:
        require(path.read_bytes() == raw, "Deterministic identity certificate")
    print(json.dumps({"status": "PASS", "raw_bytes": data["raw_bytes"],
                      "tex_block_bytes_saved": data["exact_tex_blocks"]["saved_bytes"],
                      "script_sha256": data["script_sha256"], "certificate_sha256": sha(raw)}, sort_keys=True))


if __name__ == "__main__":
    main()
