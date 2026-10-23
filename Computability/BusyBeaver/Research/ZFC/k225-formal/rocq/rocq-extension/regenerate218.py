#!/usr/bin/env python3
"""Generate the K218F proof sources for the literal 218-state table (Source 144's K218).

The 218 runs the seed-K 222 calculus, like the 221, but its register program contains Source
140's equality routine. So:

- the program layer is dag219 (k225-formal/lean219/dag219_nodes.json, written by make_dag219.py):
  dag222 with node 123, the equality test, replaced by the new routine on nodes 461-466. Dag219.v
  is generated from those nodes; ProgLib219.v is rocq224's ProgLib222.v with the equality test's
  three lemmas (loop124, if123_eq, if123_neq) replaced by proofs about the new routine with the
  same two statements if123_eq / if123_neq; L2Root219.v and Main219.v are ProgLib222's companions
  renamed. The calculus files are copied from rocq224/src as for the 221;
- the 218's source is related to dag219 by an offset bisimulation (Cert218Offsets);
- the TM side is K230's runtime with the labels the 218 does not use disabled, and the 218's
  startup: 312,909 steps, a gap of 144 cells and 130 spare blocks (K230: 408,419, 181, 167);
- the table is in K230 labels with the two states native 301, 302 renamed into the freed labels
  102, 120 (k225-formal/lean218/), and the dense map is an explicit list.

Untrusted generator: every emitted claim is checked by Rocq.
Usage: regenerate218.py [--reference vendor/k230-rocq] [--output coq/218]"""
from pathlib import Path
import argparse
import json
import re
import shutil

from source_data import sha, parse, table_text, program_text, RUNTIME
from regenerate221 import dense_labels as _dense_labels_221

ROOT = Path(__file__).resolve().parent
V = 218
BOOT_STEPS = 312909
NS = "K218F"
KF = ROOT.parent.parent
CALC_DIR = KF / "rocq224" / "src"
CALCULUS = ["Codes222", "Thm222", "DominatedCore", "CD222", "Prop222", "G222", "L224Def", "L224Prop", "L224Meta",
            "L224E", "Interp222", "Enum222", "L1_Sound222", "L1_Comp222", "L1_222", "Seed222",
            "Sound222", "Complete222"]
PROGRAM = ["Dag219", "ProgLib219", "L2Root219", "Main219"]
DAG219 = KF / "lean219" / "dag219_nodes.json"


def dense_labels(dense, sparse):
    import regenerate221
    regenerate221.V = V
    return _dense_labels_221(dense, sparse)


NEW_EQ = r"""(** ** if_eq(scratch1, param2, body): runs body iff scratch1 = param2; both are zeroed.
    Source 140's routine: P = (D6, C2) [461], U = (P, B) [462], A = (D5, U) [463],
    L = (A, D6) [464], Z = (D5, C1) [465], R = (Z, U) [466], E = (L, R) [123]; D6 decrements
    scratch1, D5 param2.  A cancels the counters, L breaks exactly on equality, R clears both and
    breaks. *)
Definition clr (m : St) : St := set (set m 6 0) 5 0.

Lemma u462_pos m v : get m 6 = S v -> sem (ENode 462) m (XContinue 1) (set m 6 v).
Proof.
  intros H. eapply sem_car_continue with (k := 0); [reflexivity|].
  eapply sem_cdr_continueS with (k := 0); [reflexivity | apply sem_decnz_pos; [lia | exact H] | apply sem_cont].
Qed.

Lemma u462_zero m : get m 6 = 0 -> sem (ENode 462) m (XBreak 1) m.
Proof.
  intros H. eapply sem_cdr_break with (k := 0); [reflexivity | | apply sem_breakS].
  eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; exact H].
Qed.

Lemma loop463 a : forall m, get m 5 = a ->
  (a <= get m 6 -> sem (ENode 463) m XNormal (set (set m 5 0) 6 (get m 6 - a))) /\
  (get m 6 < a -> sem (ENode 463) m (XBreak 1) (set (set m 5 (a - get m 6 - 1)) 6 0)).
Proof.
  induction a as [|a IH]; intros m Ha; split; intros Hle.
  - eapply sem_conseq; [eapply sem_car_break1; [reflexivity | apply sem_decnz_zero; exact Ha]|].
    destruct m; nrm; subst; f_equal; lia.
  - lia.
  - destruct (get m 6) as [|b] eqn:Hb; [lia|].
    eapply sem_cdr_continue1; [reflexivity | apply sem_decnz_pos; [lia | exact Ha] | |].
    + apply u462_pos with (v := b). destruct m; nrm; exact Hb.
    + eapply sem_conseq;
        [apply (proj1 (IH (set (set m 5 a) 6 b) ltac:(destruct m; reflexivity))); destruct m; nrm; lia|].
      destruct m; nrm; subst; f_equal; lia.
  - destruct (get m 6) as [|b] eqn:Hb.
    + eapply sem_conseq.
      * eapply sem_cdr_break with (k := 0); [reflexivity | apply sem_decnz_pos; [lia | exact Ha] |].
        apply u462_zero. destruct m; nrm; exact Hb.
      * destruct m; nrm; subst; f_equal; lia.
    + eapply sem_cdr_continue1; [reflexivity | apply sem_decnz_pos; [lia | exact Ha] | |].
      * apply u462_pos with (v := b). destruct m; nrm; exact Hb.
      * eapply sem_conseq;
          [apply (proj2 (IH (set (set m 5 a) 6 b) ltac:(destruct m; reflexivity))); destruct m; nrm; lia|].
        destruct m; nrm; subst; f_equal; lia.
Qed.

Lemma l464_eq m : get m 6 = get m 5 -> sem (ENode 464) m (XBreak 1) (clr m).
Proof.
  intros H. destruct (loop463 (get m 5) m eq_refl) as [H1 _].
  eapply sem_conseq.
  - eapply sem_cdr_break with (k := 0); [reflexivity | apply H1; lia |].
    apply sem_decnz_zero. destruct m; nrm; lia.
  - unfold clr; destruct m; nrm; f_equal; lia.
Qed.

Lemma l464_neq m : get m 6 <> get m 5 ->
  exists x y, sem (ENode 464) m XNormal (set (set m 5 x) 6 y).
Proof.
  intros H. destruct (loop463 (get m 5) m eq_refl) as [H1 H2].
  destruct (Nat.lt_ge_cases (get m 6) (get m 5)) as [Hlt | Hge].
  - exists (get m 5 - get m 6 - 1), 0. eapply sem_car_break1; [reflexivity | apply H2, Hlt].
  - exists 0, (get m 6 - get m 5 - 1).
    eapply sem_cdr_normal; [reflexivity | apply H1, Hge |].
    eapply sem_conseq; [apply sem_decnz_pos with (v := get m 6 - get m 5 - 1); [lia | destruct m; nrm; lia]|].
    destruct m; nrm; f_equal; lia.
Qed.

Lemma z465 a : forall m, get m 5 = a -> sem (ENode 465) m XNormal (set m 5 0).
Proof.
  intros m _. revert m.
  while_tac (fun m : St => m) (fun m : St => set m 5 0).
Qed.

Lemma r466 b : forall m, get m 6 = b -> sem (ENode 466) m (XBreak 1) (clr m).
Proof.
  induction b as [|b IH]; intros m Hb.
  - eapply sem_conseq.
    + eapply sem_cdr_break with (k := 0); [reflexivity | apply (z465 (get m 5) m eq_refl) |].
      apply u462_zero. destruct m; nrm; exact Hb.
    + unfold clr; destruct m; nrm; subst; reflexivity.
  - eapply sem_cdr_continue1; [reflexivity | apply (z465 (get m 5) m eq_refl) | |].
    + apply u462_pos with (v := b). destruct m; nrm; exact Hb.
    + eapply sem_conseq; [apply (IH (set (set m 5 0) 6 b)); destruct m; reflexivity|].
      unfold clr; destruct m; reflexivity.
Qed.

Lemma if123_eq m : get m 6 = get m 5 -> sem (ENode 123) m XNormal (clr m).
Proof. intros H. eapply sem_car_break1; [reflexivity | apply l464_eq, H]. Qed.

Lemma if123_neq m : get m 6 <> get m 5 -> sem (ENode 123) m (XBreak 1) (clr m).
Proof.
  intros H. destruct (l464_neq m H) as (x & y & Hl).
  eapply sem_conseq.
  - eapply sem_cdr_break with (k := 0); [reflexivity | exact Hl |].
    apply (r466 y). destruct m; reflexivity.
  - unfold clr; destruct m; reflexivity.
Qed.

"""


def program_files(output):
    """Dag219, ProgLib219, L2Root219, Main219 under NS."""
    d = json.load(open(DAG219))
    nn = d["nnodes"]
    nodes = {int(k): v for k, v in d["nodes"].items()}
    assert sorted(nodes) == list(range(nn)) and nn == 467
    name = {"N": "ENode", "EInc": "EInc", "EDecnz": "EDecnz", "EBreak": "EBreak", "EContinue": "EContinue"}

    def edge(e):
        op, a = e
        return "EHalt" if op == "EHalt" else f"{name[op]} {a}"

    rows = "\n".join(f"  | {n} => ({edge(nodes[n][0])}, {edge(nodes[n][1])})" for n in range(nn))
    dag = (f"(** dag219: rocq224's dag222 with node 123, the equality test, replaced by Source 140's\n"
           f"    routine on nodes 461-466 (k225-formal/make_dag219.py; nodes SHA256 {sha(DAG219)}). *)\n"
           "From K230 Require Import RM.\nDefinition dag_nodes (n : nat) : edge * edge :=\n  match n with\n"
           f"{rows}\n  | _ => (EHalt, EHalt)\n  end.\nDefinition dag219 : prog := mkProg dag_nodes 0 {nn}.\n")
    (output / "Dag219.v").write_text(dag, encoding="utf-8", newline="\n")

    def ren(t):
        t = re.sub(r"From K224 Require", f"From {NS} Require", t)
        for a, b in [("Dag222", "Dag219"), ("ProgLib222", "ProgLib219"), ("L2Root222", "L2Root219"),
                     ("Main222", "Main219"), ("dag222", "dag219")]:
            t = t.replace(a, b)
        return t

    src = (CALC_DIR / "ProgLib222.v").read_text(encoding="utf-8")
    i = src.index("(** ** if_eq(scratch1, param2, body)")
    j = src.index("(* if_eq(scratch1, param2, par1()) *)")
    lib = ren(src[:i]) + NEW_EQ + ren(src[j:])
    assert "loop124" not in lib and "ENode 124" not in lib
    (output / "ProgLib219.v").write_text(
        f"(** ProgLib222.v (SHA256 {sha(CALC_DIR / 'ProgLib222.v')}) for dag219: the equality test's lemmas\n"
        "    are proved anew for Source 140's routine; everything else is unchanged. *)\n" + lib,
        encoding="utf-8", newline="\n")
    for n in ["L2Root222", "Main222"]:
        t = ren((CALC_DIR / f"{n}.v").read_text(encoding="utf-8"))
        assert "K224" not in re.sub(r"\(\*.*?\*\)", "", t, flags=re.S), n
        (output / f"{n.replace('222', '219')}.v").write_text(
            f"(** {n}.v (SHA256 {sha(CALC_DIR / (n + '.v'))}) renamed for dag219. *)\n" + t,
            encoding="utf-8", newline="\n")


def regenerate(reference, output):
    manifest = json.loads((ROOT / "manifest.json").read_text(encoding="utf-8"))
    ref = reference.resolve()
    assert sha(ref / "manifest.json") == manifest["reference_manifest_sha256"]
    rm = json.loads((ref / "manifest.json").read_text(encoding="utf-8"))
    inp = {"dense": ROOT / "inputs/218/table.tm", "sparse": ROOT / "inputs/218/table_k230labels.tm",
           "sites": ROOT / "inputs/218/sites.json", "certificate": ROOT / "inputs/218/Cert218Offsets.v"}
    sparse, dense, old = parse(inp["sparse"]), parse(inp["dense"]), parse(ref / "machine/k230.tm")
    used = {q for q, _ in sparse}
    deleted = set(range(230)) - used
    assert set(sparse) == {(q, b) for q in range(230) if q not in deleted for b in (0, 1)}
    assert len(used) == V
    labels = dense_labels(dense, sparse)
    program, stats = program_text(json.loads(inp["sites"].read_text(encoding="utf-8")))
    assert stats["depth"] <= 40, stats
    output.mkdir(parents=True, exist_ok=True)

    for name in CALCULUS:
        src = CALC_DIR / f"{name}.v"
        body = re.sub(r"From K224 Require", f"From {NS} Require", src.read_text(encoding="utf-8"))
        assert "K224" not in re.sub(r"\(\*.*?\*\)", "", body, flags=re.S), name
        body = f"(** Copy of rocq224/src/{name}.v (SHA256 {sha(src)}) under namespace {NS}. *)\n" + body
        (output / f"{name}.v").write_text(body, encoding="utf-8", newline="\n")
    program_files(output)

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
            for a, b in [("408419", str(BOOT_STEPS)), ("repeat 1 167", "repeat 1 130"),
                         ("zeros 181", "zeros 144"), ("a gap of 181 zero cells", "a gap of 144 zero cells"),
                         ("176 register blocks", "139 register blocks"), ("the 167 spare", "the 130 spare")]:
                assert a in body, (name, a)
                body = body.replace(a, b)
        if name == "Sim230":
            a = "exists (@nil bool), R0, 181, (repeat 1 167)."
            assert a in body
            body = body.replace(a, "exists (@nil bool), R0, 144, (repeat 1 130).")
        if name in ("Interpreter230Check", "Sim230", "Sim230Main"):
            body = f"From {NS} Require Import Prog218.\n" + body
            body = re.sub(r"\bp230\b", "p218", body)
            body = re.sub(r"\bp230_wf\b", "p218_wf", body)
        body = (f"(** Runtime-only fork of {relative}; original SHA256 {sha(source)}.\n"
                f"    Sparse labels {sorted(deleted)} are disabled; the 218's startup frame. "
                "Original source immutable. *)\n") + body
        (output / f"{name}.v").write_text(body, encoding="utf-8", newline="\n")

    prog = program.replace("p227", "p218")
    (output / "Prog218.v").write_text(f"(** Source sites SHA256 {sha(inp['sites'])}. *)\n" + prog,
                                      encoding="utf-8", newline="\n")
    (output / "Table218.v").write_text(table_text(dense, V, "table218", inp["dense"]), encoding="utf-8",
                                       newline="\n")
    shutil.copyfile(ROOT / "templates/OffsetBisim230.v", output / "OffsetBisim230.v")
    cert = inp["certificate"].read_text(encoding="utf-8")
    assert "Definition Cert218 :" in cert
    shutil.copyfile(inp["certificate"], output / "Cert218Offsets.v")
    bridge = f"""(** Kernel-checked equivalence of the 218's source with dag219, for every natural-valued
    register file. *)
From Coq Require Import List.
From K230 Require Import RM Prog230.
From K230P Require Import Bisim230.
From {NS} Require Import Prog218 OffsetBisim230 Cert218Offsets Dag219.
Import ListNotations.
Lemma certificate_forward : ocheck (ptree p218) (ptree dag219) Cert218 = true.
Proof. Time vm_compute. reflexivity. Qed.
Lemma certificate_backward : ocheck (ptree dag219) (ptree p218) (omirror Cert218) = true.
Proof. Time vm_compute. reflexivity. Qed.
Theorem p218_dag219 R : rm_halts p218 ([],R) <-> rm_halts dag219 ([],R).
Proof. exact (ocheck_iff p218 dag219 Cert218 certificate_forward certificate_backward R). Qed.
Print Assumptions p218_dag219.
"""
    (output / "Source218.v").write_text(bridge, encoding="utf-8", newline="\n")
    correct = f"""(** Closed endpoint for the sparse-label 218-state runtime. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From {NS} Require TM230 Sim230Main.
From {NS} Require Import Source218 Main219.
From K230S Require Import KQuotZFC.

Theorem tm218_sparse_halts_iff_ZFC_inconsistent :
  {NS}.TM230.TM230.halts {NS}.TM230.tm {NS}.TM230.TM230.c0
  <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite {NS}.Sim230Main.tm230_rm, p218_dag219.
  exact dag219_iff_standardZFC.
Qed.
Corollary tm218_sparse_nonhalting_iff_ZFC_consistent :
  (~ {NS}.TM230.TM230.halts {NS}.TM230.tm {NS}.TM230.TM230.c0)
  <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm218_sparse_halts_iff_ZFC_inconsistent. reflexivity. Qed.
Print Assumptions tm218_sparse_halts_iff_ZFC_inconsistent.
Print Assumptions tm218_sparse_nonhalting_iff_ZFC_consistent.
"""
    (output / "Correct218.v").write_text(correct, encoding="utf-8", newline="\n")
    dense_proof = (ROOT / "templates/Dense229.v").read_text(encoding="utf-8").replace("229", "218").replace("K230F", NS)
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
        "(** canonical dense index -> sparse label (K230 labels; native 301, 302 renamed 102, 120) *)\n"
        f"Definition dense_labels : list nat := [{lst}].\n"
        "Definition expand (q : nat) := nth q dense_labels 230.")
    (output / "Dense218.v").write_text(dense_proof, encoding="utf-8", newline="\n")
    (output / "CorrectDense218.v").write_text(
        (ROOT / "templates/CorrectDense229.v").read_text(encoding="utf-8").replace("229", "218").replace("K230F", NS),
        encoding="utf-8", newline="\n")
    receipt = {"status": "GENERATED", "states": V, "deleted_sparse_labels": sorted(deleted),
               "dense_labels": labels, "boot_steps": BOOT_STEPS,
               "reference_manifest_sha256": sha(ref / "manifest.json"), "source_stats": stats,
               "inputs_sha256": {k: sha(p) for k, p in inp.items()},
               "calculus_sources_sha256": {n: sha(CALC_DIR / f"{n}.v") for n in CALCULUS + ["ProgLib222", "L2Root222", "Main222"]},
               "dag219_nodes_sha256": sha(DAG219),
               "generated_source_sha256": {p.name: sha(p) for p in sorted(output.glob("*.v"))}}
    (output.parent / "regeneration218.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, default=ROOT.parent / "vendor/k230-rocq")
    parser.add_argument("--output", type=Path, default=ROOT / "coq/218")
    args = parser.parse_args()
    r = regenerate(args.reference, args.output)
    print(r["status"], r["source_stats"], "deleted", r["deleted_sparse_labels"])


if __name__ == "__main__":
    main()
