#!/usr/bin/env python3
"""Bind the closed Hilbert fusion theorem to the exact canonical emitter AST.

The emitter contract and certificate are data. No emitter, compiler, or proof
generator is imported. The independent Hilbert checker is called first.
"""
import argparse
import hashlib
import json
from pathlib import Path
from check_fusion_certificate import check


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("emitter_contract", type=Path)
    parser.add_argument("--certificate", type=Path,
                        default=Path(__file__).with_name("rel_helper_fusion_certificate.json"))
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("rel_fusion_emitter_binding.json"))
    a = parser.parse_args()
    cert_bytes = a.certificate.read_bytes()
    emitter_bytes = a.emitter_contract.read_bytes()
    certificate, emitter = json.loads(cert_bytes), json.loads(emitter_bytes)
    proof = check(certificate)
    if certificate.get("equality_binder") != "kappa":
        raise ValueError("certificate does not have the independent helper binder")
    terms = certificate["terms"]
    def label(x):
        if x == "k":
            return "c"
        if x == "kappa":
            return ["R", "a", "b"]
        return x
    def formula(n):
        t = terms[n]
        if t[0] == "F":
            return 1
        if t[0] == "meta":
            if t[1] != "m":
                raise ValueError("unexpected opaque matrix")
            return "c"
        if t[0] == "I":
            return ["I", formula(t[1]), formula(t[2])]
        if t[0] == "Q":
            return ["Q", label(t[1]), formula(t[2])]
        if t[0] in ("Rel", "Eq"):
            return ["R" if t[0] == "Rel" else "E", label(t[1]), label(t[2])]
        raise ValueError("unknown certificate constructor")
    replacements = 0
    def original_with_helper(t):
        nonlocal replacements
        if t == ["Q", "c", ["E", "a", "b"]]:
            replacements += 1
            return ["Q", ["R", "a", "b"], ["E", "a", "b"]]
        if isinstance(t, list):
            return [original_with_helper(x) for x in t]
        return t
    expected_old = original_with_helper(emitter["original_expression"])
    if replacements != 1:
        raise ValueError("expected exactly one old equality-vacuity binder")
    if formula(certificate["old_bundle"]) != expected_old:
        raise ValueError("old canonical-helper bundle does not match")
    if formula(certificate["fused_bundle"]) != emitter["canonical_expression"]:
        raise ValueError("certified fused endpoint differs from exact emitter expression")
    if emitter["gate"] != "if c=a or c=b then 0 else canonical_expression":
        raise ValueError("unexpected gate contract")
    result = {
        "status": "PASS_CERTIFIED_FUSION_MATCHES_EXACT_EMITTER",
        "proof_nodes": proof["proof_nodes"],
        "formula_dag_nodes": proof["formula_dag_nodes"],
        "private_and_opaque_matrix": "k=m=c",
        "equality_helper_binder": "kappa=R(a,b)=4*P(a,b)+1",
        "old_equality_binder_replacements": replacements,
        "source_gate": emitter["gate"],
        "certificate_sha256": hashlib.sha256(cert_bytes).hexdigest(),
        "emitter_contract_sha256": hashlib.sha256(emitter_bytes).hexdigest(),
        "scope": "Exact symbolic arithmetic formula binding for all natural parameters, including coincident roles and code0. Closed Hilbert equivalence uses only the retained derived K/S/Peirce basis, literal rho2/rho6, MP, and GEN. Equiconsistency of the restricted equality helper is proved separately."
    }
    a.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
