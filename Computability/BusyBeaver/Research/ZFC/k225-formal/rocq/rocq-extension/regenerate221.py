#!/usr/bin/env python3
"""Generate the K221F proof sources for the literal 221-state table (Source 132's K221).

The TM side is the same runtime fork as regenerate225.py (K230's runtime with the deleted sparse
labels disabled, boot 409,835 steps). What differs:

- the calculus: the 221 runs the seed-K 222's register program, so its source is related, by an
  offset bisimulation (Cert221Offsets, from ../../gen_cert.py), to dag222 (K230's Dag230 with the
  AX node rebuilt), not to K230's p230; dag222 halts from the boot registers iff StandardZFC is
  inconsistent by ../../rocq224 (Main222.dag222_iff_standardZFC). Those files are copied here
  under this variant's namespace;
- the dense table is the public canonical table, whose numbering is not the order-preserving
  compaction of the K230 labels, so the dense-to-sparse map is an explicit list, checked
  state by state in Rocq.

Untrusted generator: every emitted claim is checked by Rocq.
Usage: regenerate221.py [--reference vendor/k230-rocq] [--output coq/221]"""
from pathlib import Path
import argparse
import json
import re
import shutil

from source_data import sha, parse, table_text, program_text, RUNTIME

ROOT = Path(__file__).resolve().parent
V = 221
DELETED = [79, 140, 175, 191, 192, 208, 219, 226, 229]
BOOT_STEPS = 409835
NS = "K221F"
CALCULUS = ["Codes222", "Thm222", "CD222", "Prop222", "G222", "L224Def", "L224Prop", "L224Meta",
            "L224E", "Interp222", "Enum222", "L1_Sound222", "L1_Comp222", "L1_222", "Seed222",
            "Sound222", "Complete222", "Dag222", "ProgLib222", "L2Root222", "Main222"]
CALC_DIR = ROOT.parent.parent / "rocq224" / "src"


def dense_labels(dense, sparse):
    """The isomorphism dense index -> sparse K230 label, by a joint walk from the start state."""
    m = {0: 0}
    todo = [0]
    while todo:
        q = todo.pop()
        for b in (0, 1):
            w, d, n = dense[q, b]
            w2, d2, n2 = sparse[m[q], b]
            assert (w, d) == (w2, d2), (q, b)
            if n == V:
                assert n2 == 230, (q, b, n2)
                continue
            if n in m:
                assert m[n] == n2, (q, b)
            else:
                m[n] = n2
                todo.append(n)
    assert sorted(m) == list(range(V)) and len(set(m.values())) == V
    return [m[i] for i in range(V)] + [230]


def regenerate(reference, output):
    manifest = json.loads((ROOT / "manifest.json").read_text(encoding="utf-8"))
    ref = reference.resolve()
    assert sha(ref / "manifest.json") == manifest["reference_manifest_sha256"]
    rm = json.loads((ref / "manifest.json").read_text(encoding="utf-8"))
    inp = {"dense": ROOT / "inputs/221/table.tm", "sparse": ROOT / "inputs/221/table_k230labels.tm",
           "sites": ROOT / "inputs/221/sites.json", "certificate": ROOT / "inputs/221/Cert221Offsets.v"}
    sparse, dense, old = parse(inp["sparse"]), parse(inp["dense"]), parse(ref / "machine/k230.tm")
    deleted = set(DELETED)
    assert set(sparse) == {(q, b) for q in range(230) if q not in deleted for b in (0, 1)}
    labels = dense_labels(dense, sparse)
    program, stats = program_text(json.loads(inp["sites"].read_text(encoding="utf-8")))
    assert stats["depth"] <= 40, stats
    output.mkdir(parents=True, exist_ok=True)

    # the calculus and the dag222 program layer, under this namespace
    for name in CALCULUS:
        src = CALC_DIR / f"{name}.v"
        body = src.read_text(encoding="utf-8")
        body = re.sub(r"From K224 Require", f"From {NS} Require", body)
        assert "K224" not in re.sub(r"\(\*.*?\*\)", "", body, flags=re.S), name
        body = (f"(** Copy of rocq224/src/{name}.v (SHA256 {sha(src)}) under namespace {NS}. *)\n") + body
        (output / f"{name}.v").write_text(body, encoding="utf-8", newline="\n")

    def imports(match):
        names = match.group(1).split()
        original = [n for n in names if n not in RUNTIME]
        fork = [n for n in names if n in RUNTIME]
        return "\n".join((["From K230 Require Import " + " ".join(original) + "."] if original else [])
                         + ([f"From {NS} Require Import " + " ".join(fork) + "."] if fork else []))

    disabled = " || ".join(f"Nat.eqb q {q}" for q in sorted(deleted))
    for name in RUNTIME:
        relative = f"coq/tm/{name}.v"
        source = ref / relative
        assert sha(source) == rm["local_files"][relative]
        body = re.sub(r"From K230 Require Import ([^.]+)\.", imports, source.read_text(encoding="utf-8"))
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
            body = f"From {NS} Require Import Prog221.\n" + body
            body = re.sub(r"\bp230\b", "p221", body)
            body = re.sub(r"\bp230_wf\b", "p221_wf", body)
        body = (f"(** Runtime-only fork of {relative}; original SHA256 {sha(source)}.\n"
                f"    Sparse labels {sorted(deleted)} are disabled. Original source immutable. *)\n") + body
        (output / f"{name}.v").write_text(body, encoding="utf-8", newline="\n")

    prog = program.replace("p227", "p221")
    (output / "Prog221.v").write_text(f"(** Source sites SHA256 {sha(inp['sites'])}. *)\n" + prog, encoding="utf-8", newline="\n")
    (output / "Table221.v").write_text(table_text(dense, V, "table221", inp["dense"]), encoding="utf-8", newline="\n")
    shutil.copyfile(ROOT / "templates/OffsetBisim230.v", output / "OffsetBisim230.v")
    cert = inp["certificate"].read_text(encoding="utf-8")
    assert "Definition Cert221 :" in cert
    shutil.copyfile(inp["certificate"], output / "Cert221Offsets.v")
    bridge = f"""(** Kernel-checked equivalence of the 221's rotated source with dag222, for every
    natural-valued register file. *)
From Coq Require Import List.
From K230 Require Import RM Prog230.
From K230P Require Import Bisim230.
From {NS} Require Import Prog221 OffsetBisim230 Cert221Offsets Dag222.
Import ListNotations.
Lemma certificate_forward : ocheck (ptree p221) (ptree dag222) Cert221 = true.
Proof. Time vm_compute. reflexivity. Qed.
Lemma certificate_backward : ocheck (ptree dag222) (ptree p221) (omirror Cert221) = true.
Proof. Time vm_compute. reflexivity. Qed.
Theorem p221_dag222 R : rm_halts p221 ([],R) <-> rm_halts dag222 ([],R).
Proof. exact (ocheck_iff p221 dag222 Cert221 certificate_forward certificate_backward R). Qed.
Print Assumptions p221_dag222.
"""
    (output / "Source221.v").write_text(bridge, encoding="utf-8", newline="\n")
    correct = f"""(** Closed endpoint for the sparse-label 221-state runtime. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From {NS} Require TM230 Sim230Main.
From {NS} Require Import Source221 Main222.
From K230S Require Import KQuotZFC.

Theorem tm221_sparse_halts_iff_ZFC_inconsistent :
  {NS}.TM230.TM230.halts {NS}.TM230.tm {NS}.TM230.TM230.c0
  <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite {NS}.Sim230Main.tm230_rm, p221_dag222.
  exact dag222_iff_standardZFC.
Qed.
Corollary tm221_sparse_nonhalting_iff_ZFC_consistent :
  (~ {NS}.TM230.TM230.halts {NS}.TM230.tm {NS}.TM230.TM230.c0)
  <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm221_sparse_halts_iff_ZFC_inconsistent. reflexivity. Qed.
Print Assumptions tm221_sparse_halts_iff_ZFC_inconsistent.
Print Assumptions tm221_sparse_nonhalting_iff_ZFC_consistent.
"""
    (output / "Correct221.v").write_text(correct, encoding="utf-8", newline="\n")
    dense_proof = (ROOT / "templates/Dense229.v").read_text(encoding="utf-8").replace("229", "221").replace("K230F", NS)
    assert "do 230 (" in dense_proof
    dense_proof = dense_proof.replace("do 230 (", f"do {V + 1} (")
    dense_proof = dense_proof.replace("0..228 work", f"0..{V - 1} work").replace(
        "checks all 230 states", f"checks all {V + 1} states")
    dense_proof = dense_proof.replace("Exact compaction of the verified sparse-label runtime",
                                      "Exact relabelling of the verified sparse-label runtime")
    old_expand = "Definition expand (q : nat) := if Nat.leb 140 q then S q else q."
    assert old_expand in dense_proof
    lst = "; ".join(map(str, labels))
    dense_proof = dense_proof.replace(
        old_expand,
        "(** canonical dense index -> K230 label (the public canonical numbering is a BFS order) *)\n"
        f"Definition dense_labels : list nat := [{lst}].\n"
        "Definition expand (q : nat) := nth q dense_labels 230.")
    (output / "Dense221.v").write_text(dense_proof, encoding="utf-8", newline="\n")
    (output / "CorrectDense221.v").write_text(
        (ROOT / "templates/CorrectDense229.v").read_text(encoding="utf-8").replace("229", "221").replace("K230F", NS), encoding="utf-8", newline="\n")
    receipt = {"status": "GENERATED", "states": V, "deleted_sparse_labels": DELETED,
               "dense_labels": labels,
               "reference_manifest_sha256": sha(ref / "manifest.json"), "source_stats": stats,
               "inputs_sha256": {k: sha(p) for k, p in inp.items()},
               "calculus_sources_sha256": {n: sha(CALC_DIR / f"{n}.v") for n in CALCULUS},
               "generated_source_sha256": {p.name: sha(p) for p in sorted(output.glob("*.v"))}}
    (output.parent / "regeneration221.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, default=ROOT.parent / "vendor/k230-rocq")
    parser.add_argument("--output", type=Path, default=ROOT / "coq/221")
    args = parser.parse_args()
    r = regenerate(args.reference, args.output)
    print(r["status"], r["source_stats"])


if __name__ == "__main__":
    main()
