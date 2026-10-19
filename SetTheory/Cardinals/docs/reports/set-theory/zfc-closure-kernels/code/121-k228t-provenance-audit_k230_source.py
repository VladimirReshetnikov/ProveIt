#!/usr/bin/env python3
"""Read-only source/provenance audit of the pinned K230 release.

This is deliberately not a Rocq compiler or kernel-assumption audit.
The release's manifest is treated as pinned data, not an executable oracle.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

PIN = "3142e4dd980f0be12f4abb636c4ae2528afc17eb"
MACHINE_SHA = "e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8"
SITES_SHA = "400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def uncomment(text):
    """Remove nested Rocq comments while keeping quoted strings intact."""
    out, depth, i, quoted = [], 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == "(*":
                depth += 1
                i += 2
            elif pair == "*)":
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == '"':
                if i+1 < len(text) and text[i+1] == '"':
                    out.append('"')
                    i += 1
                else:
                    quoted = False
            i += 1
        elif pair == "(*":
            depth = 1
            out.append(" ")
            i += 2
        else:
            out.append(text[i])
            quoted = text[i] == '"'
            i += 1
    require(depth == 0 and not quoted, "unclosed comment/string")
    return "".join(out)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent / "k230-rocq")
    p.add_argument("--out", type=Path, default=Path(__file__).resolve().parent / "k230_source_audit.json")
    a = p.parse_args()
    repo = a.repo
    commit = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"],text=True).strip()
    require(commit == PIN, "K230 release revision differs")
    manifest = json.loads((repo / "manifest.json").read_text())
    files = manifest["local_files"]
    hashes, suspicious, skip_tokens = {}, [], []
    definitions = theorems = 0
    for rel, expected in files.items():
        data = (repo / rel).read_bytes()
        actual = hashlib.sha256(data).hexdigest()
        require(actual == expected, f"manifest hash mismatch: {rel}")
        hashes[rel] = actual
        code = uncomment(data.decode("utf-8"))
        for match in re.finditer(r"\b(?:Axioms?|Admitted|admit|Conjecture|Parameters?|(?:vm|native)_cast_no_check)\b",code):
            suspicious.append({"file": rel,"line":code[:match.start()].count("\n")+1,"token":match.group()})
        for match in re.finditer(r"\bskip\b",code):
            skip_tokens.append({"file":rel,"line":code[:match.start()].count("\n")+1,
                                "role":"declared and applied ordinary lemma skip, not the upstream admit tactic"})
        definitions += len(re.findall(r"\b(?:Definition|Fixpoint|Inductive|Record)\b",code))
        theorems += len(re.findall(r"\b(?:Lemma|Theorem|Corollary)\b",code))
    machine_hash = hashlib.sha256((repo / "machine/k230.tm").read_bytes()).hexdigest()
    sites_hash = hashlib.sha256((repo / "machine/sites230.json").read_bytes()).hexdigest()
    require(machine_hash == MACHINE_SHA == manifest["machine_sha256"], "machine hash mismatch")
    require(sites_hash == SITES_SHA == manifest["sites_sha256"], "sites hash mismatch")
    # This records declaration identity and direct composition, not proof checking.
    expected_names = {
        "coq/tm/Correct230.v": ["tm230_halts_iff_ZFC_inconsistent", "tm230_nonhalting_iff_ZFC_consistent"],
        "coq/tm/Sim230Main.v": ["tm230_rm"],
        "coq/prog/Main230.v": ["prog230"],
        "coq/logic/Seed230.v": ["seed230_iff_thm"],
        "coq/logic/Consistency230.v": ["thm230_iff_standardZFC"],
        "coq/logic/Bridge230.v": ["thm230_iff_KPrimeOrdIR"],
        "coq/settheory/KUpperConsistency.v": ["KPrimeOrdIR_standardZFC_equiconsistent", "KPrimeOrd_standardZFC_equiconsistent"],
        "coq/settheory/KQuotZFC.v": ["KPrimeOrd_standardZFC_inconsistent"],
    }
    endpoints = []
    for rel,names in expected_names.items():
        code = uncomment((repo / rel).read_text())
        for name in names:
            m = re.search(r"\b(?:Theorem|Lemma|Corollary)\s+"+re.escape(name)+r"\b",code)
            require(m is not None, f"missing declaration {name}")
            endpoints.append({"name":name,"file":rel,"line":code[:m.start()].count("\n")+1,
                              "url":f"https://github.com/elliotglazer/k230-rocq/blob/{PIN}/{rel}"})
    result = {
        "status":"PASSED_PINNED_SOURCE_IDENTITY_AUDIT",
        "scope":"Read-only source hashes, declaration presence, and lexical local-source scan; no Rocq compilation or kernel check",
        "revision":commit,
        "manifest_sha256":hashlib.sha256((repo / "manifest.json").read_bytes()).hexdigest(),
        "machine_sha256":machine_hash,"sites_sha256":sites_hash,
        "local_hashed_files":len(files),"local_proof_sources":len([f for f in files if f.endswith(".v")]),
        "local_coq_directory_sources":len([f for f in files if f.startswith("coq/")]),
        "compatibility_files":len([f for f in files if f.startswith("compat/")]),
        "checked_local_sha256":hashes,
        "local_definitions_fixpoints_inductives_records":definitions,
        "local_lemmas_theorems_corollaries":theorems,
        "local_assumption_admission_or_unchecked_cast_tokens":suspicious,
        "reviewed_skip_identifier_occurrences":skip_tokens,
        "theorem_declarations":endpoints,
        "ordinary_theory":"KPrimeOrd; numerical falsity calibration uses KPrimeOrdIR",
        "falsity_code":1,"falsity_alias":"wel 0 0",
        "truth_code":0,
        "bootstrap":{"steps":408419,"entry_state":84,"left_nonblank_bits":[1],"gap_zero_cells":181,
                     "register_values_first_nine":[0,0,0,3,0,0,3,0,0],"spare_register_blocks":167,"spare_value":1},
        "internal_PA_derivation_in_release":False,
        "release_reported_toolchain":{"rocq":"9.1.0","rocq-stdlib":"9.0.0","ocaml":"4.14.2"},
        "new_kernel_build_performed":False,
        "upstream_reference_revision":manifest["reference"]["commit"],
    }
    a.out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "checked_local_sha256"},indent=2))


if __name__ == "__main__":
    main()
