#!/usr/bin/env python3
"""Check exact block-support and inline-Phi recipes at the full2963 tuple."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / "research/low-padding-independent/certify.py"
PARENT_SHA = "86dae914161f5f030cd1c575e6448e029542a18718cadf732c2d5a673adc3cc7"
PROOF = ROOT / "research/low-padding-independent/PROOF.md"
PROOF_SHA = "ad952c6f1717a69e6b489e8c7af0bb52ce09414b78cc994b892b6e7f996d06f6"
PAGE = ROOT / "candidates/one-page-low-padding2963/equation.tex"
PAGE_SHA = "7c9cc96b35c33d0d8de643caa816148d252c7eb3cc64ac4d925714788d263397"


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
    require(sha(PARENT.read_bytes()) == PARENT_SHA, "Exact frozen complete2963 verifier")
    require(sha(PROOF.read_bytes()) == PROOF_SHA, "Exact frozen complete2963 proof")
    module_spec = importlib.util.spec_from_file_location("frozen_low_padding", PARENT)
    require(module_spec is not None and module_spec.loader is not None, "Parent import specification")
    parent = importlib.util.module_from_spec(module_spec)
    module_spec.loader.exec_module(parent)
    _, seed, actions, tiles, old_c, support = parent.model()
    old_whole, old_dc = parent.constants(old_c, support)
    require(parent.L == 2963 and parent.SPEC["centers"] == [1956], "Exact complete intended tuple")

    # Formal coefficient arrays, not merely a numerical evaluation at rho.
    old_psi_one, old_psi_two = [0] * 3297, [0] * 3297
    for t, array in ((1, old_psi_one), (2, old_psi_two)):
        for j in range(8):
            array[978 + j] += t ** j
            array[969 + j] += t ** (17 + j)
        for j in range(9):
            array[960 + j] += t ** (8 + j)
            array[942 + j] += t ** (25 + j)
        array[1005] += 2 - t
    weighted = [0] * 3297
    # x969(x9+2^17)G8(2x)+2^8*x942(x18+2^17)G9(2x).
    for j in range(8):
        weighted[969 + 9 + j] += 1 << j
        weighted[969 + j] += 1 << (17 + j)
    for j in range(9):
        weighted[942 + 18 + j] += 1 << (8 + j)
        weighted[942 + j] += 1 << (25 + j)
    require(weighted == old_psi_two and weighted[1005] == 0,
            "Entire univariate weighted polynomial equals Psi(x,2)")
    c = [0] * 3297
    for j, (west, north, east, south) in enumerate(tiles):
        c[j] = 1 + 1024 * (1 + west + 256 * north + 131072 * east + 33554432 * south)
    for e, coefficient in enumerate(weighted):
        c[e] += 1024 * coefficient
    require(c == old_c, "Every one of3297 inline-Phi coefficients equals the complete parent")

    physical_array = [0] * 3297
    for e in range(951):
        physical_array[e] += 1
    for e in range(960, 986):
        physical_array[e] += 1
    physical_array[1005] += 1
    old_physical = old_psi_one.copy()
    for e in range(942):
        old_physical[e] += 1
    old_physical[977] += 1
    require(physical_array == old_physical and sum(physical_array) == 978
            and all(v in (0, 1) for v in physical_array),
            "Entire polynomial support identity G942+Psi(x,1)+x977=G951+x960G26+x1005")
    require({e for e, value in enumerate(physical_array) if value} == support,
            "Complete physical support includes both zero-weight positions")
    require(c[977] == c[1005] == 0 and physical_array[977] == physical_array[1005] == 1,
            "Zero weighted coefficients never erase the physical dummy or marker")

    power = lambda e: 1 << (47 * e)
    G = lambda count: sum(power(e) for e in range(count))
    B, beta = power(2963), power(2963) - 1
    MC = beta - G(951) - power(960) * G(26) - power(1005)
    dc = power(18) + power(1005) + sum(value * power(1956 - e) for e, value in enumerate(c) if value)
    K = dc + power(2963 + 9)
    core = power(960) * G(9) + power(987) * G(8) + power(1005)
    MF = beta + 4 * G(917) + ((1 << 44) - 2) * power(1956) + core
    whole = {"beta": beta, "K": K, "MC": MC, "MF_source": MF}
    require(whole == old_whole and dc == old_dc,
            "All four complete fixed integers and DC agree exactly")
    require(MC.bit_count() == 139261 - 978 and (MF - beta).bit_count() == 978,
            "Whole actual complementary populations")

    bad_printed_values = {
        "marker": beta - G(951) - power(960) * G(26),
        "dummy": beta - G(951) - power(960) * G(17) - power(978) * G(8) - power(1005)}
    bad_printed_tex = {
        "marker": r"M_C=\beta-G_{951}(\rho)-\rho^{960}G_{26}(\rho)",
        "dummy": r"M_C=\beta-G_{951}(\rho)-\rho^{960}G_{17}(\rho)-\rho^{978}G_8(\rho)-\rho^{1005}"}
    negatives = {}
    for name, position in (("marker", 1005), ("dummy", 977)):
        bad_MC = bad_printed_values[name]
        require(bad_MC == MC + power(position), "Actual corrupted printed MC omits exactly its named physical bit")
        require(bad_MC != MC and bad_MC.bit_count() == 139261 - 977
                and power(position) & (MC + 1) == 0
                and power(position) & (bad_MC + 1) != 0,
                "Deleting a zero-weight physical position changes the whole mask")
        negatives[name] = {"position": position, "bad_MC_population": bad_MC.bit_count(),
                           "physical_bit_forbidden": True, "actual_corrupt_printed_MC": bad_printed_tex[name], "Phi_unchanged": c == old_c}
    # Exact parent page blocks; retain its p_i name for the east color.
    before_mc = r"""M_C={}&\beta-\rho^{977}\\
&-G_{942}(\rho)-\Psi(\rho,1),\\
"""
    before_phi = r"""\Phi(x)={}&\sum_{i=0}^{941}[1+2^{10}(1+w_i+2^8n_i\\
&+2^{17}p_i+2^{25}s_i)]x^i+2^{10}\Psi(x,2),\\
\Psi(x,t)={}&x^{969}(x^9+t^{17})G_8(tx)\\
&+t^8x^{942}(x^{18}+t^{17})G_9(tx)\\
&+(2-t)x^{1005}.
"""
    after_mc = r"""M_C={}&\beta-G_{951}(\rho)\\
&-\rho^{960}G_{26}(\rho)-\rho^{1005},\\
"""
    univariate_phi = r"""\Phi(x)={}&\sum_{i=0}^{941}[1+2^{10}(1+w_i+2^8n_i\\
&+2^{17}p_i+2^{25}s_i)]x^i+2^{10}\Psi(x),\\
\Psi(x)={}&x^{969}(x^9+2^{17})G_8(2x)\\
&+2^8x^{942}(x^{18}+2^{17})G_9(2x).
"""
    inline_phi = r"""\Phi(x)={}&\sum_{i=0}^{941}[1+2^{10}(1+w_i+2^8n_i\\
&+2^{17}p_i+2^{25}s_i)]x^i\\
&+2^{10}x^{969}(x^9+2^{17})G_8(2x)\\
&+2^{18}x^{942}(x^{18}+2^{17})G_9(2x).
"""
    before, univariate, inline = before_mc + before_phi, after_mc + univariate_phi, after_mc + inline_phi
    page_raw = PAGE.read_bytes()
    require(sha(page_raw) == PAGE_SHA, "Exact complete parent2963 printed page")
    page = page_raw.decode()
    require(page.count(before_mc) == page.count(before_phi) == 1,
            "Both exact changed blocks occur once in the complete printed page")
    projected_page = page.replace(before_mc, after_mc).replace(before_phi, inline_phi)
    require(r"\Psi" not in projected_page, "The helper is completely removed from the projected page")
    ports = {}
    for name, value in whole.items():
        raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
        ports[name] = {"bits": value.bit_length(), "bytes": len(raw), "sha256": sha(raw)}
    data = {
        "schema": "block_mask_inline_Phi_exact_port_identity_v1",
        "script_sha256": sha(Path(__file__).read_bytes()), "parent_verifier_sha256": PARENT_SHA,
        "parent_proof_sha256": PROOF_SHA, "parent_page_sha256": PAGE_SHA,
        "projected_full_page": {"before_bytes": len(page_raw), "after_bytes": len(projected_page.encode()),
                                "saved_bytes": len(page_raw) - len(projected_page.encode()),
                                "sha256": sha(projected_page.encode()),
                                "scope": "Exact source obtained by the two stated literal replacements only; no rendered-PDF size claim."},
        "formal_polynomial_identities": [
            "G942(x)+Psi_old(x,1)+x977=G951(x)+x960*G26(x)+x1005",
            "Psi_old(x,2)=x969*(x9+2^17)*G8(2x)+2^8*x942*(x18+2^17)*G9(2x)"],
        "all3297_coefficients_sha256": sha(encoded(c)),
        "all3297_physical_coefficients_sha256": sha(encoded(physical_array)),
        "weighted_univariate_coefficients_sha256": sha(encoded(weighted)),
        "physical_positions": 978, "physical_intervals": [[0, 950], [960, 985], [1005, 1005]],
        "whole_ports": ports, "raw_bytes": sum(row["bytes"] for row in ports.values()),
        "zero_weight_physical_deletion_negatives": negatives,
        "exact_tex_blocks": {
            "before": before, "univariate": univariate, "inline": inline,
            "before_bytes": len(before.encode()), "univariate_bytes": len(univariate.encode()),
            "inline_bytes": len(inline.encode()),
            "univariate_saved_bytes": len(before.encode()) - len(univariate.encode()),
            "inline_saved_bytes": len(before.encode()) - len(inline.encode()),
            "scope": "Exact parent-page MC/Psi/Phi blocks including line breaks; projected complete-source size recorded separately."},
        "scope": "Exact equality of all fixed ports and the specialized P66 polynomial, with identical positive zero set; no new native theorem or raw-byte reduction."
    }
    require(data["raw_bytes"] == 69685 and data["exact_tex_blocks"]["inline_saved_bytes"] > 0,
            "Unchanged whole-port metric and smaller exact inline recipe blocks")
    require(data["projected_full_page"]["saved_bytes"] == data["exact_tex_blocks"]["inline_saved_bytes"],
            "Whole-source savings equal the exact changed-block savings")
    raw = encoded(data)
    path = HERE / "CERTIFICATE.json"
    if args.write:
        path.write_bytes(raw)
        (HERE / "inline-equation.tex").write_text(projected_page)
    else:
        require(path.read_bytes() == raw, "Deterministic exact identity receipt")
        require((HERE / "inline-equation.tex").read_text() == projected_page, "Exact deterministic projected complete source")
    print(json.dumps({"status": "PASS", "raw_bytes": data["raw_bytes"],
                      "inline_block_bytes_saved": data["exact_tex_blocks"]["inline_saved_bytes"],
                      "script_sha256": data["script_sha256"], "certificate_sha256": sha(raw)}, sort_keys=True))


if __name__ == "__main__":
    main()
