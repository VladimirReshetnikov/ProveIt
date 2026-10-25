#!/usr/bin/env python3
"""Exact control/support identities and complete-page reproduction, stdlib only."""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / "candidates/one-page-complemented47-independent/equation.tex"


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def replace_once(text, old, new):
    need(text.count(old) == 1, "Expected one exact formula block")
    return text.replace(old, new)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="materialize source and evidence; default is read-only")
    args = parser.parse_args()
    source = PARENT.read_text(encoding="utf-8")
    old_mask = r"&-\sum_{e=0}^{3296}\fl{(D_\rho(\Phi(\rho),e)+\rho-1)/\rho}\rho^e,\\"
    new_mask = r"&-G_{943}(\rho)-\Psi(\rho,1),\\"
    old_control = r"""&+2^{17}p_i+2^{25}s_i)]x^i\\
&+2^{10}x^{1003}(x^{20}+2^{17})G_8(2x)\\
&+2^{18}x^{983}(x^{30}+2^{17})G_9(2x)\\
&+2^{44}x^{1095}(1+x^{1100}+x^{2201})."""
    new_control = r"""&+2^{17}p_i+2^{25}s_i)]x^i+2^{10}\Psi(x,2),\\
\Psi(x,t)={}&x^{1003}(x^{20}+t^{17})G_8(tx)\\
&+t^8x^{983}(x^{30}+t^{17})G_9(tx)\\
&+t^{34}x^{1095}(1+x^{1100}+x^{2201})."""
    shared = replace_once(replace_once(source, old_mask, new_mask), old_control, new_control)
    old_bare = r"K={}&\rho^{30}+\rho^{62}+\rho^{1100}+\rho^{2201}+\rho^{8849}\\"
    new_bare = r"K={}&\rho^{30}(1+\rho^{32})+\rho^{1100}(1+\rho^{1101})+\rho^{8849}\\"
    factored = replace_once(shared, old_bare, new_bare)
    # Factoring reduces repeated exponentiation but is not assumed to reduce
    # complete source length; choose the shorter of these exact spellings.
    candidate = min((shared, factored), key=lambda text: len(text.encode("utf-8")))

    # Sparse bivariate Psi: key=(x exponent,t exponent), value=coefficient.
    psi = {}
    for j in range(8):
        psi[1023 + j, j] = 1
        psi[1003 + j, 17 + j] = 1
    for j in range(9):
        psi[1013 + j, 8 + j] = 1
        psi[983 + j, 25 + j] = 1
    for e in (1095, 2195, 3296):
        psi[e, 34] = 1
    at_one, at_two = {}, {}
    for (e, a), coefficient in psi.items():
        at_one[e] = at_one.get(e, 0) + coefficient
        at_two[e] = at_two.get(e, 0) + coefficient * 2 ** a
    expected = {}
    for e in range(983, 992):
        expected[e] = 2 ** (e - 948)
    for e in range(1003, 1011):
        expected[e] = 2 ** (e - 976)
    for e in range(1013, 1022):
        expected[e] = 2 ** (e - 995)
    for e in range(1023, 1031):
        expected[e] = 2 ** (e - 1013)
    expected.update({1095: 2 ** 44, 2195: 2 ** 44, 3296: 2 ** 44})
    need({e: 1024 * value for e, value in at_two.items()} == expected, "Complete control coefficient identity failed")
    need(len(at_one) == 37 and set(at_one.values()) == {1}, "Control support is not squarefree")
    support = set(range(943)) | set(at_one)
    need(len(support) == 980 and not ({1063, 1064} & support), "Whole coefficient support mismatch")
    rho = 1 << 47
    # Same MC by direct disjoint support and by the shared polynomial.
    beta = (1 << (47 * 8807)) - 1
    original = beta + rho - (rho + 3) * (rho ** 1063) - sum(rho ** e for e in support)
    replacement = beta + rho - (rho + 3) * (rho ** 1063)
    replacement -= (rho ** 943 - 1) // (rho - 1) + sum(coefficient * rho ** e for e, coefficient in at_one.items())
    need(original == replacement, "Full MC integer identity failed")
    mc_raw = replacement.to_bytes((replacement.bit_length() + 7) // 8, "big")
    need(hashlib.sha256(mc_raw).hexdigest() == "f9d3e993386834f3e57b964481c32bb0928645524f089dda517c64fb5fcfcd3f", "MC differs from independently certified complete integer")
    bare = {30: 1, 62: 1, 1100: 1, 2201: 1, 8849: 1}
    factored_bare = {30: 1, 30 + 32: 1, 1100: 1, 1100 + 1101: 1, 8849: 1}
    need(bare == factored_bare, "Factored bare-kernel identity failed")

    # All table, decoder, alphabet, seed and semantic-boundary text is literal.
    marker = r"\textbf{The 943 indexed fixed tiles.}"
    need(source.split(marker, 1)[1] == candidate.split(marker, 1)[1], "Fixed finite language or footer changed")
    prefix = r"\textbf{The four fixed integers.}"
    need(source.split(prefix, 1)[0] == candidate.split(prefix, 1)[0], "Equation or typography prefix changed")
    proof = {
        "schema": "complemented47_shared_control_polynomial_v1",
        "parent": {"path": str(PARENT.relative_to(ROOT)), **digest(source.encode("utf-8"))},
        "auditor": digest(Path(__file__).read_bytes()),
        "candidate": digest(candidate.encode("utf-8")),
        "complete_tex_bytes": {"parent": len(source.encode("utf-8")),
                               "shared_control": len(shared.encode("utf-8")),
                               "shared_plus_factored_kernel": len(factored.encode("utf-8"))},
        "tex_bytes_saved": len(source.encode("utf-8")) - len(candidate.encode("utf-8")),
        "controls": len(psi), "nonzero_Phi_coefficients": len(support),
        "whole_MC_identity": True, "whole_Phi_identity": True,
        "MC_big_endian": digest(mc_raw),
        "four_integer_tuple_unchanged": True, "raw_coefficient_bytes_unchanged": 207214,
        "table_decoder_seed_and_footer_literal": True,
        "limits": "Representation identity only; no changed tuple, operation count, native semantics, or formalization.",
    }
    outputs = {"equation.tex": candidate.encode("utf-8"),
               "AUDIT.json": (json.dumps(proof, indent=2, sort_keys=True) + "\n").encode("utf-8")}
    for name, raw in outputs.items():
        path = HERE / name
        if args.write:
            path.write_bytes(raw)
        else:
            need(path.read_bytes() == raw, "Saved output differs: " + name)
    print(json.dumps({"tex_bytes_saved": proof["tex_bytes_saved"], "four_integer_tuple_unchanged": True}, sort_keys=True))


if __name__ == "__main__":
    main()
