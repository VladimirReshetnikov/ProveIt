#!/usr/bin/env python3
"""Generate the K225F proof sources for the literal 225-state table (Source 124's K225).

Adapted from regenerate.py (Source 123's K226F generator): same runtime forks of the pinned K230
sources, the same offset-aware source bisimulation checker, and the same dense-table template.
Only the inputs differ: the 225's sparse table in K230 labels (deleted labels 79, 140, 175, 208,
229), its dense table (= the public canonical table), its source, and the offset certificate
produced by gen_cert.py. Untrusted generator: every emitted claim is checked by Rocq.
Usage: regenerate225.py [--reference vendor/k230-rocq] [--output coq/225]"""
from pathlib import Path
import argparse
import json
import re
import shutil

from source_data import sha, parse, table_text, program_text, RUNTIME

ROOT = Path(__file__).resolve().parent
V = 225
DELETED = [79, 140, 175, 208, 229]
BOOT_STEPS = 409835


def expansion(deleted):
    """Dense index -> sparse K230 label, as nested successors (deleted labels sorted)."""
    lines, thresholds = ["Definition expand (q : nat) :="], [d - k for k, d in enumerate(deleted)]
    for k, t in enumerate(thresholds):
        lines.append(f"  if Nat.ltb q {t} then {'S (' * k}q{')' * k} else")
    k = len(deleted)
    lines[-1] += f" {'S (' * k}q{')' * k}."
    return "\n".join(lines)


def regenerate(reference, output):
    manifest = json.loads((ROOT / "manifest.json").read_text())
    ref = reference.resolve()
    assert sha(ref / "manifest.json") == manifest["reference_manifest_sha256"]
    rm = json.loads((ref / "manifest.json").read_text())
    inp = {"dense": ROOT / "inputs/225/table.tm", "sparse": ROOT / "inputs/225/table_k230labels.tm",
           "sites": ROOT / "inputs/225/sites.json", "certificate": ROOT / "inputs/225/Cert225Offsets.v"}
    sparse, dense, old = parse(inp["sparse"]), parse(inp["dense"]), parse(ref / "machine/k230.tm")
    deleted = set(DELETED)
    kept = [q for q in range(231) if q not in deleted]
    renumber = {q: i for i, q in enumerate(kept)}
    assert set(sparse) == {(q, b) for q in range(230) if q not in deleted for b in (0, 1)}
    assert dense == {(renumber[q], b): (w, d, renumber[n]) for (q, b), (w, d, n) in sparse.items()}
    program, stats = program_text(json.loads(inp["sites"].read_text()))
    assert stats["depth"] <= 40, stats
    output.mkdir(parents=True, exist_ok=True)

    def rename(s):
        return (s.replace("K227F", "K225F").replace("Prog227", "Prog225")
                .replace("p227", "p225").replace("Cert227Offsets", "Cert225Offsets")
                .replace("Source227", "Source225").replace("Correct227", "Correct225")
                .replace("tm227_", "tm225_").replace("227-state", "225-state"))

    def imports(match):
        names = match.group(1).split()
        original = [n for n in names if n not in RUNTIME]
        fork = [n for n in names if n in RUNTIME]
        return "\n".join((["From K230 Require Import " + " ".join(original) + "."] if original else [])
                         + (["From K225F Require Import " + " ".join(fork) + "."] if fork else []))

    disabled = " || ".join(f"Nat.eqb q {q}" for q in sorted(deleted))
    for name in RUNTIME:
        relative = f"coq/tm/{name}.v"
        source = ref / relative
        assert sha(source) == rm["local_files"][relative]
        body = re.sub(r"From K230 Require Import ([^.]+)\.", imports, source.read_text())
        if name == "Table230":
            table = dict(sparse)
            table.update({(q, b): old[q, b] for q in deleted for b in (0, 1)})
            body = table_text(table, 230, "table230", inp["sparse"])
        if name == "TM230":
            body = body.replace("  match nth_error table230 q with",
                                f"  if ({disabled})%bool then None else\n  match nth_error table230 q with", 1)
            body = body.replace("{ unfold tmn in H. destruct (nth_error table230 q) eqn:E; [|discriminate].",
                                "{ unfold tmn in H. destruct (" + disabled + ")%bool eqn:D; [discriminate|].\n"
                                "    destruct (nth_error table230 q) eqn:E; [|discriminate].")
            assert disabled in body
        if name == "Boot230":
            assert "408419" in body
            body = body.replace("408419", str(BOOT_STEPS))
        if name in ("Interpreter230Check", "Sim230", "Sim230Main"):
            body = "From K225F Require Import Prog225.\n" + body
            body = re.sub(r"\bp230\b", "p225", body)
            body = re.sub(r"\bp230_wf\b", "p225_wf", body)
        body = (f"(** Runtime-only fork of {relative}; original SHA256 {sha(source)}.\n"
                f"    Sparse labels {sorted(deleted)} are disabled. Original source immutable. *)\n") + body
        (output / f"{name}.v").write_text(body, newline="\n")

    (output / "Prog225.v").write_text(f"(** Source sites SHA256 {sha(inp['sites'])}. *)\n" + rename(program), newline="\n")
    (output / "Table225.v").write_text(table_text(dense, V, "table225", inp["dense"]), newline="\n")
    shutil.copyfile(ROOT / "templates/OffsetBisim230.v", output / "OffsetBisim230.v")
    shutil.copyfile(inp["certificate"], output / "Cert225Offsets.v")
    bridge = """(** Kernel-checked source equivalence for every natural-valued register file. *)
From Coq Require Import List.
From K230 Require Import RM Prog230.
From K230P Require Import Bisim230.
From K225F Require Import Prog225 OffsetBisim230 Cert225Offsets.
Import ListNotations.
Lemma certificate_forward : ocheck (ptree p225) (ptree p230) cert225_offsets = true.
Proof. Time vm_compute. reflexivity. Qed.
Lemma certificate_backward : ocheck (ptree p230) (ptree p225) (omirror cert225_offsets) = true.
Proof. Time vm_compute. reflexivity. Qed.
Theorem p225_p230 R : rm_halts p225 ([],R) <-> rm_halts p230 ([],R).
Proof. exact (ocheck_iff p225 p230 cert225_offsets certificate_forward certificate_backward R). Qed.
Print Assumptions p225_p230.
"""
    (output / "Source225.v").write_text(bridge, newline="\n")
    (output / "Correct225.v").write_text(rename((ROOT / "templates/Correct227.v").read_text()), newline="\n")
    dense_proof = (ROOT / "templates/Dense229.v").read_text().replace("229", "225").replace("K230F", "K225F")
    assert "do 230 (" in dense_proof
    dense_proof = dense_proof.replace("do 230 (", f"do {V + 1} (")
    dense_proof = dense_proof.replace("0..228 work", f"0..{V - 1} work").replace("checks all 230 states", f"checks all {V + 1} states")
    old_expand = "Definition expand (q : nat) := if Nat.leb 140 q then S q else q."
    assert old_expand in dense_proof
    dense_proof = dense_proof.replace(old_expand, expansion(DELETED))
    (output / "Dense225.v").write_text(dense_proof, newline="\n")
    (output / "CorrectDense225.v").write_text(
        (ROOT / "templates/CorrectDense229.v").read_text().replace("229", "225").replace("K230F", "K225F"), newline="\n")
    receipt = {"status": "GENERATED", "states": V, "deleted_sparse_labels": DELETED,
               "reference_manifest_sha256": sha(ref / "manifest.json"), "source_stats": stats,
               "inputs_sha256": {k: sha(p) for k, p in inp.items()},
               "generated_source_sha256": {p.name: sha(p) for p in sorted(output.glob("*.v"))}}
    (output.parent / "regeneration225.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, default=ROOT.parent / "vendor/k230-rocq")
    parser.add_argument("--output", type=Path, default=ROOT / "coq/225")
    args = parser.parse_args()
    r = regenerate(args.reference, args.output)
    print(r["status"], r["source_stats"])


if __name__ == "__main__":
    main()
