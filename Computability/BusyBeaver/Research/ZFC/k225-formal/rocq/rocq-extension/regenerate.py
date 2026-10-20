#!/usr/bin/env python3
"""Regenerate the exact K226F proof sources from pinned inputs and templates.

This is an untrusted source generator. The independent build compiles the
resulting proof terms and checks the dense literal machine in Rocq.
"""
from pathlib import Path
import argparse
import json
import re
import shutil

from source_data import sha, parse, table_text, program_text, RUNTIME

ROOT = Path(__file__).resolve().parent


def regenerate(reference, output):
    manifest = json.loads((ROOT / "manifest.json").read_text())
    spec = manifest["variants"]["226"]
    ref = reference.resolve()
    assert sha(ref / "manifest.json") == manifest["reference_manifest_sha256"]
    rm = json.loads((ref / "manifest.json").read_text())
    inp = {k: ROOT / p for k, p in spec["inputs"].items()}
    sparse, dense, old = parse(inp["sparse"]), parse(inp["dense"]), parse(ref / "machine/k230.tm")
    deleted = set(spec["deleted_sparse_labels"])
    kept = [q for q in range(231) if q not in deleted]
    renumber = {q: i for i, q in enumerate(kept)}
    assert set(sparse) == {(q, b) for q in range(230) if q not in deleted for b in (0, 1)}
    assert dense == {(renumber[q], b): (w, d, renumber[n])
                     for (q, b), (w, d, n) in sparse.items()}
    program, stats = program_text(json.loads(inp["sites"].read_text()))
    assert stats["depth"] == 41
    output.mkdir(parents=True, exist_ok=True)

    def rename(s):
        return (s.replace("K227F", "K226F").replace("Prog227", "Prog226")
                .replace("p227", "p226").replace("Cert227Offsets", "Cert226Offsets")
                .replace("Source227", "Source226").replace("Correct227", "Correct226")
                .replace("tm227_", "tm226_").replace("227-state", "226-state"))

    def imports(match):
        names = match.group(1).split()
        original = [n for n in names if n not in RUNTIME]
        fork = [n for n in names if n in RUNTIME]
        return "\n".join((["From K230 Require Import " + " ".join(original) + "."] if original else [])
                         + (["From K226F Require Import " + " ".join(fork) + "."] if fork else []))

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
        if name == "Boot230":
            body = body.replace("408419", str(spec["boot_steps"]))
        if name in ("Interpreter230Check", "Sim230", "Sim230Main"):
            body = "From K226F Require Import Prog226.\n" + body
            body = re.sub(r"\bp230\b", "p226", body)
            body = re.sub(r"\bp230_wf\b", "p226_wf", body)
            if name in ("Interpreter230Check", "Sim230"):
                body = re.sub(r"\b40\b", "41", body)
        body = (f"(** Runtime-only fork of {relative}; original SHA256 {sha(source)}.\n"
                f"    Sparse labels {sorted(deleted)} are disabled. Original source immutable. *)\n") + body
        (output / f"{name}.v").write_text(body)

    (output / "Prog226.v").write_text(f"(** Source sites SHA256 {sha(inp['sites'])}. *)\n" + rename(program))
    (output / "Table226.v").write_text(table_text(dense, 226, "table226", inp["dense"]))
    shutil.copyfile(ROOT / "templates/OffsetBisim230.v", output / "OffsetBisim230.v")
    shutil.copyfile(inp["certificate"], output / "Cert226Offsets.v")
    bridge = """(** Kernel-checked source equivalence for every natural-valued register file. *)
From Coq Require Import List.
From K230 Require Import RM Prog230.
From K230P Require Import Bisim230.
From K226F Require Import Prog226 OffsetBisim230 Cert226Offsets.
Import ListNotations.
Lemma certificate_forward : ocheck (ptree p226) (ptree p230) cert226_offsets = true.
Proof. Time vm_compute. reflexivity. Qed.
Lemma certificate_backward : ocheck (ptree p230) (ptree p226) (omirror cert226_offsets) = true.
Proof. Time vm_compute. reflexivity. Qed.
Theorem p226_p230 R : rm_halts p226 ([],R) <-> rm_halts p230 ([],R).
Proof. exact (ocheck_iff p226 p230 cert226_offsets certificate_forward certificate_backward R). Qed.
Print Assumptions p226_p230.
"""
    (output / "Source226.v").write_text(bridge)
    (output / "Correct226.v").write_text(rename((ROOT / "templates/Correct227.v").read_text()))
    dense_proof = (ROOT / "templates/Dense229.v").read_text().replace("229", "226").replace("K230F", "K226F")
    dense_proof = dense_proof.replace("do 230 (", "do 227 (")
    dense_proof = dense_proof.replace("0..228 work", "0..225 work").replace("checks all 230 states", "checks all 227 states")
    expansion = """Definition expand (q : nat) :=
  if Nat.ltb q 65 then q else
  if Nat.ltb q 78 then S (q) else
  if Nat.ltb q 138 then S (S (q)) else
  if Nat.ltb q 172 then S (S (S (q))) else S (S (S (S (q))))."""
    dense_proof = dense_proof.replace("Definition expand (q : nat) := if Nat.leb 140 q then S q else q.", expansion)
    (output / "Dense226.v").write_text(dense_proof)
    (output / "CorrectDense226.v").write_text(
        (ROOT / "templates/CorrectDense229.v").read_text().replace("229", "226").replace("K230F", "K226F"))
    expected = {p.name: sha(p) for p in (ROOT / "coq/226").glob("*.v")}
    actual = {p.name: sha(p) for p in output.glob("*.v")}
    assert actual == expected, {n: (expected.get(n), actual.get(n)) for n in expected.keys() | actual.keys()
                                if expected.get(n) != actual.get(n)}
    receipt = {"status": "PASS_EXACT_REGENERATION", "states": 226,
               "reference_manifest_sha256": sha(ref / "manifest.json"),
               "source_stats": stats, "generated_source_sha256": actual}
    (output / "regeneration.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, default=ROOT.parent / "vendor/k230-rocq")
    parser.add_argument("--output", type=Path, default=ROOT / ".build/regenerated226")
    args = parser.parse_args()
    result = regenerate(args.reference, args.output)
    print(result["status"])


if __name__ == "__main__":
    main()
