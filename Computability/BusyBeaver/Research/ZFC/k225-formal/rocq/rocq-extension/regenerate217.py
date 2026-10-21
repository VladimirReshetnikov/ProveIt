#!/usr/bin/env python3
"""Generate the K217F proof sources for the literal 217-state table (candidate-k217, Source 152).

The 217 runs Source 149's dominated program, so its calculus and program layers are new and its
TM layer is the 218's:

- calculus: rocq224's seed-K 222 files are copied (Codes222 ... Interp222, Sound222, Complete222:
  the judgment thm222 and its ZFC calibration). The dominated calculus thmDom (ThmDom.v: rho8
  restricted to u <= a) derives exactly thm222's codes, by Source 149's certificate (DomRho8.v,
  rendered from DomRho8.lean). The enumerator EnumDom.v is Enum222.v with the dominated AX
  command (fields z, y, x: U = d + z, A = U + x, B = h + y; GEN of the cache at U; rho8 at
  (A, B, c, U)); L1_SoundDom, L1_CompDom and SeedDom are Enum222's companions with the
  compiler's rho8 leaf AX(c, u, b, a - u);
- program: dagDom (k225-formal/lean217/dagdom_nodes.json, make_dagdom.py) is dag219 with the
  dominated AX word; ProgLibDom.v is the 218's ProgLib219.v for dagDom, L2RootDom.v the 218's
  L2Root219.v with the AX lemma ax1 restated for the new word, MainDom.v the 218's Main219.v;
- the 217's source is related to dagDom by an offset bisimulation (Cert217Offsets);
- the TM side is K230's runtime with the labels the 217 does not use disabled, the 219's startup
  (312,617 steps, a gap of 144 cells, 130 spare blocks), and site paths of up to 48 bits (the
  217's source reaches 45; K230's bound is 40, and the runtime proofs only need the path to fit
  in the 64 cells before the register header).

Untrusted generator: every emitted claim is checked by Rocq.
Usage: regenerate217.py [--reference vendor/k230-rocq] [--output coq/217]"""
from pathlib import Path
import argparse
import json
import re
import shutil

from source_data import sha, parse, table_text, program_text, RUNTIME
from regenerate221 import dense_labels as _dense_labels_221

ROOT = Path(__file__).resolve().parent
V = 217
BOOT_STEPS = 312617
NS = "K217F"
KF = ROOT.parent.parent
CALC_DIR = KF / "rocq224" / "src"
DOM_DIR = KF / "rocqdom"
V218 = ROOT / "coq" / "218"
CALCULUS = ["Codes222", "Thm222", "CD222", "Prop222", "G222", "L224Def", "L224Prop", "L224Meta",
            "L224E", "Interp222", "Sound222", "Complete222"]
DOMINATED = ["DomRho8", "ThmDom", "EnumDom", "L1_SoundDom", "L1_CompDom", "SeedDom"]
PROGRAM = ["DagDom", "ProgLibDom", "L2RootDom", "MainDom"]
DAGDOM = KF / "lean217" / "dagdom_nodes.json"


def dense_labels(dense, sparse):
    import regenerate221
    regenerate221.V = V
    return _dense_labels_221(dense, sparse)


def subs(text, pairs, name):
    for a, b, *n in pairs:
        k = text.count(a)
        assert (k == n[0]) if n else k > 0, (name, a[:70], k)
        text = text.replace(a, b)
    return text


def calc(name):
    body = re.sub(r"From K224 Require", f"From {NS} Require", (CALC_DIR / f"{name}.v").read_text(encoding="utf-8"))
    assert "K224" not in re.sub(r"\(\*.*?\*\)", "", body, flags=re.S), name
    return body


THMDOM = f"""(** * ThmDom: the dominated calculus of the 217 (Source 149).

    [thm222] with rho8 restricted to the instances whose fourth argument is at most its first:
    the only rho8 instances the 217's AX command emits.  It derives exactly [thm222]'s codes:
    a restricted row is a row, and every row follows from the restricted ones ([rho8_all],
    Source 149's certificate). *)
From Stdlib Require Import Arith Lia.
From K230L Require Import Codes230.
From {NS} Require Import Codes222 Thm222 DomRho8.

Inductive thmDom : nat -> Prop :=
  | D_true : thmDom 0
  | D_mp t b : thmDom t -> thmDom (wim t b) -> thmDom b
  | D_gen a h : thmDom h -> thmDom (wal a h)
  | D_r1 a b : thmDom (rho1 a b)
  | D_r2 a b c : thmDom (rho2 a b c)
  | D_r3 a b c : thmDom (rho3 a b c)
  | D_r4 a b c : thmDom (rho4 a b c)
  | D_r5 a b c : thmDom (rho5 a b c)
  | D_r6 a b : thmDom (rho6 a b)
  | D_rG a b c : thmDom (growG a b c)
  | D_r8 a b c u : u <= a -> thmDom (rho8 a b c u)
  | D_bundle a b c : c <> a -> c <> b -> thmDom (bundle222 a b c).

Lemma thm222_of_thmDom n : thmDom n -> thm222 n.
Proof.
  induction 1.
  - exact W_true.
  - now apply (W_mp t).
  - now apply W_gen.
  - apply W_r1.
  - apply W_r2.
  - apply W_r3.
  - apply W_r4.
  - apply W_r5.
  - apply W_r6.
  - apply W_rG.
  - apply W_r8.
  - now apply W_bundle.
Qed.

Lemma domImp : DomImp thmDom.
Proof.
  constructor.
  - exact D_true.
  - intros a b H1 H2. exact (D_mp a b H2 H1).
  - exact D_r8.
Qed.

Lemma thmDom_of_thm222 n : thm222 n -> thmDom n.
Proof.
  induction 1.
  - exact D_true.
  - now apply (D_mp t).
  - now apply D_gen.
  - apply D_r1.
  - apply D_r2.
  - apply D_r3.
  - apply D_r4.
  - apply D_r5.
  - apply D_r6.
  - apply D_rG.
  - apply (rho8_all thmDom domImp).
  - now apply D_bundle.
Qed.

Theorem thmDom_iff n : thmDom n <-> thm222 n.
Proof. split; [apply thm222_of_thmDom | apply thmDom_of_thm222]. Qed.

Print Assumptions thmDom_iff.
"""


def dominated_files(output):
    shutil.copyfile(DOM_DIR / "DomRho8.v", output / "DomRho8.v")
    (output / "ThmDom.v").write_text(THMDOM, encoding="utf-8", newline="\n")
    head = lambda n: (f"(** Forked by regenerate217.py from rocq224/src/{n}.v (SHA256 {sha(CALC_DIR / (n + '.v'))}):\n"
                      "    the 217's dominated AX command (Source 149). *)\n")
    enum = subs(calc("Enum222"), [
        ("      3 + c   AX    x y u    : d += x; a := d; b := h + y; push tw, wal a h, rho8 .. rho1;\n"
         "                               tw := (if c = a or c = b then 0 else bundle222 a b c); d := 0; h := 0",
         "      3 + c   AX    z y x    : d += z; U := d; A := U + x; b := h + y; push tw, wal U h,\n"
         "                               rho8 .. rho1 at (A, b, c) with rho8's fourth argument U;\n"
         "                               tw := (if c = A or c = b then 0 else bundle222 A b c); d := 0; h := 0", 1),
        ("(P (rho8 a b c u) (P (wal a h) (P t w)))", "(P (rho8 a b c u) (P (wal u h) (P t w)))", 1),
        ("""      let '(y, pl4) := unP pl3 in
      let '(u, pl5) := unP pl4 in
      let b := h s + y in
      Some (mkState pl5 np1 (gate d1 b c) (ax_stack d1 (h s) b c u (tw s) (ws s)) 0 0)""",
         """      let '(y, pl4) := unP pl3 in
      let '(u, pl5) := unP pl4 in
      let b := h s + y in
      Some (mkState pl5 np1 (gate (d1 + u) b c) (ax_stack (d1 + u) (h s) b c d1 (tw s) (ws s)) 0 0)""", 1),
    ], "Enum222")
    (output / "EnumDom.v").write_text(head("Enum222") + enum, encoding="utf-8", newline="\n")
    sound = subs(calc("L1_Sound222"), [
        (f"From {NS} Require Import Codes222 Enum222 Thm222.", f"From {NS} Require Import Codes222 EnumDom Thm222.", 1),
    ], "L1_Sound222")
    (output / "L1_SoundDom.v").write_text(head("L1_Sound222") + sound, encoding="utf-8", newline="\n")
    comp = subs(calc("L1_Comp222"), [
        (f"From {NS} Require Import Codes222 Enum222 Thm222.",
         f"From {NS} Require Import Codes222 EnumDom Thm222 ThmDom.", 1),
        ("  | CAX c x y u => Some (gate (dd + x) (hh + y) c, ax_stack (dd + x) hh (hh + y) c u t w, 0, 0)",
         "  | CAX c x y u => Some (gate (dd + x + u) (hh + y) c, ax_stack (dd + x + u) hh (hh + y) c (dd + x) t w, 0, 0)", 1),
        ("""Lemma ex_ax c x y u t w dd hh L : exec (CAX c x y u :: L) (t, w, dd, hh) =
  exec L (gate (dd + x) (hh + y) c, ax_stack (dd + x) hh (hh + y) c u t w, 0, 0).""",
         """Lemma ex_ax c x y u t w dd hh L : exec (CAX c x y u :: L) (t, w, dd, hh) =
  exec L (gate (dd + x + u) (hh + y) c, ax_stack (dd + x + u) hh (hh + y) c (dd + x) t w, 0, 0).""", 1),
        ("""Definition leaf (j a b c u : nat) : list cmd :=
  DISCARD ++ [CAX c a b u] ++ repeat CNIP j ++ [CDROP] ++ repeat CNIP (11 - j).

Ltac leaf_tac := intros T w; right; unfold leaf; rewrite exec_app, discard; xrun; reflexivity.

Lemma blk_r1 a b c u : blk (rho1 a b) (leaf 1 a b c u).       Proof. leaf_tac. Qed.
Lemma blk_r2 a b c u : blk (rho2 a b c) (leaf 2 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_r3 a b c u : blk (rho3 a b c) (leaf 3 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_r4 a b c u : blk (rho4 a b c) (leaf 4 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_r5 a b c u : blk (rho5 a b c) (leaf 5 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_r6 a b c u : blk (rho6 a c) (leaf 6 a b c u).       Proof. leaf_tac. Qed.
Lemma blk_r7 a b c u : blk (growG a b c) (leaf 7 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_r8 a b c u : blk (rho8 a b c u) (leaf 8 a b c u).   Proof. leaf_tac. Qed.""",
         """(** a leaf: AX(c, u, b, a - u) from the reset puts U = u, A = a; rows other than rho8 take u = a *)
Definition leaf (j a b c u : nat) : list cmd :=
  DISCARD ++ [CAX c u b (a - u)] ++ repeat CNIP j ++ [CDROP] ++ repeat CNIP (11 - j).
Lemma add_sub0 u a : u <= a -> 0 + u + (a - u) = a.
Proof. lia. Qed.
Ltac leaf_tac H := intros T w; right; unfold leaf; rewrite exec_app, discard; cbn [app];
  rewrite ex_ax, (add_sub0 _ _ H); xrun; reflexivity.
Lemma blk_r1 a b c : blk (rho1 a b) (leaf 1 a b c a).        Proof. leaf_tac (le_n a). Qed.
Lemma blk_r2 a b c : blk (rho2 a b c) (leaf 2 a b c a).      Proof. leaf_tac (le_n a). Qed.
Lemma blk_r3 a b c : blk (rho3 a b c) (leaf 3 a b c a).      Proof. leaf_tac (le_n a). Qed.
Lemma blk_r4 a b c : blk (rho4 a b c) (leaf 4 a b c a).      Proof. leaf_tac (le_n a). Qed.
Lemma blk_r5 a b c : blk (rho5 a b c) (leaf 5 a b c a).      Proof. leaf_tac (le_n a). Qed.
Lemma blk_r6 a b c : blk (rho6 a c) (leaf 6 a b c a).        Proof. leaf_tac (le_n a). Qed.
Lemma blk_r7 a b c : blk (growG a b c) (leaf 7 a b c a).      Proof. leaf_tac (le_n a). Qed.
Lemma blk_r8 a b c u : u <= a -> blk (rho8 a b c u) (leaf 8 a b c u).
Proof. intros H. leaf_tac H. Qed.""", 1),
        ("Lemma compile X : thm222 X -> exists L, blk X L.", "Lemma compile X : thmDom X -> exists L, blk X L.", 1),
        ("                  | a b | a b c | a b c | a b c | a b c | a b | a b c | a b c u | a b c H1 H2].",
         "                  | a b | a b c | a b c | a b c | a b c | a b | a b c | a b c u Hu | a b c H1 H2].", 1),
        ("  - exists (leaf 1 a b 0 0). apply blk_r1.", "  - exists (leaf 1 a b 0 a). apply blk_r1.", 1),
        ("  - exists (leaf 2 a b c 0). apply blk_r2.", "  - exists (leaf 2 a b c a). apply blk_r2.", 1),
        ("  - exists (leaf 3 a b c 0). apply blk_r3.", "  - exists (leaf 3 a b c a). apply blk_r3.", 1),
        ("  - exists (leaf 4 a b c 0). apply blk_r4.", "  - exists (leaf 4 a b c a). apply blk_r4.", 1),
        ("  - exists (leaf 5 a b c 0). apply blk_r5.", "  - exists (leaf 5 a b c a). apply blk_r5.", 1),
        ("  - exists (leaf 6 a 0 b 0). apply blk_r6.", "  - exists (leaf 6 a 0 b a). apply blk_r6.", 1),
        ("  - exists (leaf 7 a b c 0). apply blk_r7.", "  - exists (leaf 7 a b c a). apply blk_r7.", 1),
        ("  - exists (leaf 8 a b c u). apply blk_r8.", "  - exists (leaf 8 a b c u). now apply blk_r8.", 1),
        ("  destruct (HL (gate (dd + 1) (hh + 1) 0) (ax_stack (dd + 1) hh (hh + 1) 0 0 t w)) as [-> | ->];",
         "  destruct (HL (gate (dd + 1 + 0) (hh + 1) 0) (ax_stack (dd + 1 + 0) hh (hh + 1) 0 (dd + 1) t w)) as [-> | ->];", 1),
        ("  intro H. destruct (compile 1 H) as [L HL].", "  intro H. destruct (compile 1 (thmDom_of_thm222 1 H)) as [L HL].", 1),
    ], "L1_Comp222")
    (output / "L1_CompDom.v").write_text(head("L1_Comp222") + comp, encoding="utf-8", newline="\n")
    seed = subs(calc("Seed222"), [
        (f"From {NS} Require Import Codes222 Thm222 Enum222 L1_Sound222 L1_Comp222.",
         f"From {NS} Require Import Codes222 Thm222 ThmDom EnumDom L1_SoundDom L1_CompDom.", 1),
        ("  intros H. destruct (compile 1 H) as [L HL].", "  intros H. destruct (compile 1 (thmDom_of_thm222 1 H)) as [L HL].", 1),
    ], "Seed222")
    (output / "SeedDom.v").write_text(head("Seed222") + seed, encoding="utf-8", newline="\n")


AX1_OLD = """Lemma ax1 m y pl4 u pl5 : get m 6 = 0 -> get m 7 = 0 -> unP (get m 8) = (y, pl4) -> unP pl4 = (u, pl5) ->
  sem (ENode 236) m XNormal
    (mkSt (get m 0) (gate (get m 4) (get m 5 + y) (get m 3))
          (ax_stack (get m 4) (get m 5) (get m 5 + y) (get m 3) u (get m 1) (get m 2))
          0 0 0 0 0 pl5)."""
AX1_NEW = """Lemma ax1 m y pl4 u pl5 : get m 6 = 0 -> get m 7 = 0 -> unP (get m 8) = (y, pl4) -> unP pl4 = (u, pl5) ->
  sem (ENode 236) m XNormal
    (mkSt (get m 0) (gate (get m 4 + u) (get m 5 + y) (get m 3))
          (ax_stack (get m 4 + u) (get m 5) (get m 5 + y) (get m 3) (get m 4) (get m 1) (get m 2))
          0 0 0 0 0 pl5)."""


def program_files(output):
    d = json.load(open(DAGDOM))
    nn = d["nnodes"]
    nodes = {int(k): v for k, v in d["nodes"].items()}
    assert sorted(nodes) == list(range(nn)) and nn == 484
    name = {"N": "ENode", "EInc": "EInc", "EDecnz": "EDecnz", "EBreak": "EBreak", "EContinue": "EContinue"}

    def edge(e):
        op, a = e
        return "EHalt" if op == "EHalt" else f"{name[op]} {a}"

    rows = "\n".join(f"  | {n} => ({edge(nodes[n][0])}, {edge(nodes[n][1])})" for n in range(nn))
    (output / "DagDom.v").write_text(
        f"(** dagDom: dag219 with Source 149's dominated AX word: node 236 and nodes 467-483 replace the\n"
        f"    prefix of the AX chain (k225-formal/make_dagdom.py; nodes SHA256 {sha(DAGDOM)}). *)\n"
        "From K230 Require Import RM.\nDefinition dag_nodes (n : nat) : edge * edge :=\n  match n with\n"
        f"{rows}\n  | _ => (EHalt, EHalt)\n  end.\nDefinition dagDom : prog := mkProg dag_nodes 0 {nn}.\n",
        encoding="utf-8", newline="\n")

    def ren(t):
        t = t.replace("From K218F Require", f"From {NS} Require")
        for a, b in [("Dag219", "DagDom"), ("ProgLib219", "ProgLibDom"), ("L2Root219", "L2RootDom"),
                     ("Main219", "MainDom"), ("dag219", "dagDom")]:
            t = t.replace(a, b)
        assert "K218F" not in re.sub(r"\(\*.*?\*\)", "", t, flags=re.S)
        return t

    lib = ren((V218 / "ProgLib219.v").read_text(encoding="utf-8"))
    (output / "ProgLibDom.v").write_text(
        f"(** The 218's ProgLib219.v (SHA256 {sha(V218 / 'ProgLib219.v')}) for dagDom: the macros and the\n"
        "    equality test are dag219's nodes. *)\n" + lib, encoding="utf-8", newline="\n")
    root = ren((V218 / "L2Root219.v").read_text(encoding="utf-8"))
    root = subs(root, [
        (AX1_OLD, AX1_NEW, 1),
        ("Enum222", "EnumDom"),
        ("(* axioms(): the long straight-line block; the stack after it and the gated bundle *)",
         "(* axioms(): the dominated AX word; GEN at U = param1, then param1 := U + x; the stack after\n"
         "   it and the gated bundle *)", 1),
    ], "L2Root219")
    (output / "L2RootDom.v").write_text(
        f"(** The 218's L2Root219.v (SHA256 {sha(V218 / 'L2Root219.v')}) for dagDom and EnumDom: the AX\n"
        "    lemma ax1 is restated for the dominated AX word. *)\n" + root, encoding="utf-8", newline="\n")
    main = ren((V218 / "Main219.v").read_text(encoding="utf-8"))
    main = subs(main, [
        ("Enum222 L1_Comp222 Seed222 Complete222", "EnumDom L1_CompDom SeedDom Complete222", 1),
        ("L1_Comp222.halts_from", "L1_CompDom.halts_from"),
    ], "Main219")
    (output / "MainDom.v").write_text(
        f"(** The 218's Main219.v (SHA256 {sha(V218 / 'Main219.v')}) for dagDom. *)\n" + main,
        encoding="utf-8", newline="\n")


def regenerate(reference, output):
    manifest = json.loads((ROOT / "manifest.json").read_text(encoding="utf-8"))
    ref = reference.resolve()
    assert sha(ref / "manifest.json") == manifest["reference_manifest_sha256"]
    rm = json.loads((ref / "manifest.json").read_text(encoding="utf-8"))
    inp = {"dense": ROOT / "inputs/217/table.tm", "sparse": ROOT / "inputs/217/table_k230labels.tm",
           "sites": ROOT / "inputs/217/sites.json", "certificate": ROOT / "inputs/217/Cert217Offsets.v"}
    sparse, dense, old = parse(inp["sparse"]), parse(inp["dense"]), parse(ref / "machine/k230.tm")
    used = {q for q, _ in sparse}
    deleted = set(range(230)) - used
    assert set(sparse) == {(q, b) for q in range(230) if q not in deleted for b in (0, 1)}
    assert len(used) == V
    labels = dense_labels(dense, sparse)
    program, stats = program_text(json.loads(inp["sites"].read_text(encoding="utf-8")))
    assert stats["depth"] <= 48, stats
    output.mkdir(parents=True, exist_ok=True)

    for name in CALCULUS:
        body = f"(** Copy of rocq224/src/{name}.v (SHA256 {sha(CALC_DIR / (name + '.v'))}) under namespace {NS}. *)\n" + calc(name)
        (output / f"{name}.v").write_text(body, encoding="utf-8", newline="\n")
    dominated_files(output)
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
            assert body.count("d <= 40") >= 1, "Sim230 depth bound"
            body = body.replace("d <= 40", "d <= 48")
        if name == "Interpreter230Check":
            assert body.count("Nat.leb (length Qs) 40") == 1, "Interpreter230Check depth bound"
            body = body.replace("Nat.leb (length Qs) 40", "Nat.leb (length Qs) 48")
        if name in ("Interpreter230Check", "Sim230", "Sim230Main"):
            body = f"From {NS} Require Import Prog217.\n" + body
            body = re.sub(r"\bp230\b", "p217", body)
            body = re.sub(r"\bp230_wf\b", "p217_wf", body)
        body = (f"(** Runtime-only fork of {relative}; original SHA256 {sha(source)}.\n"
                f"    Sparse labels {sorted(deleted)} are disabled; the 217's startup frame; site paths of\n"
                "    up to 48 bits. Original source immutable. *)\n") + body
        (output / f"{name}.v").write_text(body, encoding="utf-8", newline="\n")

    prog = program.replace("p227", "p217")
    (output / "Prog217.v").write_text(f"(** Source sites SHA256 {sha(inp['sites'])}. *)\n" + prog,
                                      encoding="utf-8", newline="\n")
    (output / "Table217.v").write_text(table_text(dense, V, "table217", inp["dense"]), encoding="utf-8",
                                       newline="\n")
    shutil.copyfile(ROOT / "templates/OffsetBisim230.v", output / "OffsetBisim230.v")
    cert = inp["certificate"].read_text(encoding="utf-8")
    assert "Definition Cert217 :" in cert
    shutil.copyfile(inp["certificate"], output / "Cert217Offsets.v")
    (output / "Source217.v").write_text(f"""(** Kernel-checked equivalence of the 217's source with dagDom, for every natural-valued
    register file. *)
From Coq Require Import List.
From K230 Require Import RM Prog230.
From K230P Require Import Bisim230.
From {NS} Require Import Prog217 OffsetBisim230 Cert217Offsets DagDom.
Import ListNotations.
Lemma certificate_forward : ocheck (ptree p217) (ptree dagDom) Cert217 = true.
Proof. Time vm_compute. reflexivity. Qed.
Lemma certificate_backward : ocheck (ptree dagDom) (ptree p217) (omirror Cert217) = true.
Proof. Time vm_compute. reflexivity. Qed.
Theorem p217_dagDom R : rm_halts p217 ([],R) <-> rm_halts dagDom ([],R).
Proof. exact (ocheck_iff p217 dagDom Cert217 certificate_forward certificate_backward R). Qed.
Print Assumptions p217_dagDom.
""", encoding="utf-8", newline="\n")
    (output / "Correct217.v").write_text(f"""(** Closed endpoint for the sparse-label 217-state runtime. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From {NS} Require TM230 Sim230Main.
From {NS} Require Import Source217 MainDom.
From K230S Require Import KQuotZFC.

Theorem tm217_sparse_halts_iff_ZFC_inconsistent :
  {NS}.TM230.TM230.halts {NS}.TM230.tm {NS}.TM230.TM230.c0
  <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite {NS}.Sim230Main.tm230_rm, p217_dagDom.
  exact dagDom_iff_standardZFC.
Qed.
Corollary tm217_sparse_nonhalting_iff_ZFC_consistent :
  (~ {NS}.TM230.TM230.halts {NS}.TM230.tm {NS}.TM230.TM230.c0)
  <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm217_sparse_halts_iff_ZFC_inconsistent. reflexivity. Qed.
Print Assumptions tm217_sparse_halts_iff_ZFC_inconsistent.
Print Assumptions tm217_sparse_nonhalting_iff_ZFC_consistent.
""", encoding="utf-8", newline="\n")
    dense_proof = (ROOT / "templates/Dense229.v").read_text(encoding="utf-8").replace("229", "217").replace("K230F", NS)
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
    (output / "Dense217.v").write_text(dense_proof, encoding="utf-8", newline="\n")
    (output / "CorrectDense217.v").write_text(
        (ROOT / "templates/CorrectDense229.v").read_text(encoding="utf-8").replace("229", "217").replace("K230F", NS),
        encoding="utf-8", newline="\n")
    receipt = {"status": "GENERATED", "states": V, "deleted_sparse_labels": sorted(deleted),
               "dense_labels": labels, "boot_steps": BOOT_STEPS,
               "reference_manifest_sha256": sha(ref / "manifest.json"), "source_stats": stats,
               "inputs_sha256": {k: sha(p) for k, p in inp.items()},
               "calculus_sources_sha256": {n: sha(CALC_DIR / f"{n}.v") for n in
                                           CALCULUS + ["Enum222", "L1_Sound222", "L1_Comp222", "Seed222"]},
               "program_sources_sha256": {n: sha(V218 / f"{n}.v") for n in ["ProgLib219", "L2Root219", "Main219"]},
               "dagdom_nodes_sha256": sha(DAGDOM), "domrho8_sha256": sha(DOM_DIR / "DomRho8.v"),
               "generated_source_sha256": {p.name: sha(p) for p in sorted(output.glob("*.v"))}}
    (output.parent / "regeneration217.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, default=ROOT.parent / "vendor/k230-rocq")
    parser.add_argument("--output", type=Path, default=ROOT / "coq/217")
    args = parser.parse_args()
    r = regenerate(args.reference, args.output)
    print(r["status"], r["source_stats"], "deleted", r["deleted_sparse_labels"])


if __name__ == "__main__":
    main()
