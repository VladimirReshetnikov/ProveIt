#!/usr/bin/env python3
"""Generate the K215F proof sources for the literal 215-state table (candidate-k215).

The 215 runs Source 159's command-permuted commands on Source 149's dominated AX:

- calculus: as for the 217 (rocq224's 222 files and ThmDom from regenerate217).
  CD222 and DomRho8 instantiate one representation-independent implication core.
  The enumerator EnumPerm, L1_SoundPerm, L1_CompPerm and SeedPerm are hand-written
  (k225-formal/rocqperm/): NIP 0, DROP 1, MP 2 (with its own field), AX 3 + c (fields y, x;
  U = d); the compiler sets the counter with J u = MP u; the seed is candidate 4;
- program: dagPerm (k225-formal/lean215/dagperm_nodes.json, make_dagperm.py) is dagDom with the
  root reading only the selector, MP reading its field (node 484) and the permuted dispatch;
  ProgLibPerm.v is the 218's ProgLib219.v for dagPerm, L2RootPerm.v the 218's L2Root219.v with
  the AX lemma restated (as for the 217) and the dispatch and root step re-proved
  (rocqperm/L2RootPerm_dispatch.v), MainPerm.v the 218's Main219.v from the 215's boot registers
  R0p (nextproof = 4, Regs215.v);
- the 215's source is related to dagPerm by an offset bisimulation (Cert215Offsets);
- the TM side is K230's runtime with the unused labels disabled, the 215's startup (95,714 steps
  to the root with R0p, a gap of 65 cells and 40 spare blocks) and site paths of up to 48 bits.

Untrusted generator: every emitted claim is checked by Rocq.
Usage: regenerate215.py [--reference vendor/k230-rocq] [--output coq/215]"""
from pathlib import Path
import argparse
import json
import re
import shutil
import subprocess
import sys

from source_data import sha, parse, table_text, program_text, RUNTIME
from regenerate221 import dense_labels as _dense_labels_221
import regenerate217 as R217

ROOT = Path(__file__).resolve().parent
V = 215
BOOT_STEPS = 95714
NS = "K215F"
KF = ROOT.parent.parent
PERM_DIR = KF / "rocqperm"
V217 = ROOT / "coq" / "217"
V218 = ROOT / "coq" / "218"
DAGPERM = KF / "lean215" / "dagperm_nodes.json"


def dense_labels(dense, sparse):
    import regenerate221
    regenerate221.V = V
    return _dense_labels_221(dense, sparse)


def ns(text):
    text = text.replace("From K217F Require", f"From {NS} Require").replace("From K218F Require", f"From {NS} Require")
    text = re.sub(r"From NS Require", f"From {NS} Require", text)
    assert "K217F" not in re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
    assert "K218F" not in re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
    return text


def calculus_files(output):
    shared = ROOT / "templates/shared215"
    shutil.copyfile(shared / "DominatedImplication.v", output / "DominatedImplication.v")
    for name in R217.CALCULUS + ["DomRho8", "ThmDom"]:
        if name in ("CD222", "DomRho8"):
            shutil.copyfile(shared / f"{name}.v", output / f"{name}.v")
        else:
            body = ns((V217 / f"{name}.v").read_text(encoding="utf-8"))
            (output / f"{name}.v").write_text(body, encoding="utf-8", newline="\n")
    for name in ["EnumPerm", "L1_SoundPerm", "L1_CompPerm", "SeedPerm"]:
        src = PERM_DIR / f"{name}.v"
        (output / f"{name}.v").write_text(
            f"(** k225-formal/rocqperm/{name}.v (SHA256 {sha(src)}) under namespace {NS}. *)\n"
            + ns(src.read_text(encoding="utf-8")), encoding="utf-8", newline="\n")
    (output / "Regs215.v").write_text(
        "(** The 215's boot registers: nextproof = 4, every other register zero. *)\n"
        "From K230 Require Import RM.\nDefinition R0p : regs := upd regs0 0 4.\n",
        encoding="utf-8", newline="\n")


def program_files(output):
    d = json.load(open(DAGPERM))
    nn = d["nnodes"]
    nodes = {int(k): v for k, v in d["nodes"].items()}
    assert sorted(nodes) == list(range(nn)) and nn == 487
    name = {"N": "ENode", "EInc": "EInc", "EDecnz": "EDecnz", "EBreak": "EBreak", "EContinue": "EContinue"}

    def edge(e):
        op, a = e
        return "EHalt" if op == "EHalt" else f"{name[op]} {a}"

    rows = "\n".join(f"  | {n} => ({edge(nodes[n][0])}, {edge(nodes[n][1])})" for n in range(nn))
    (output / "DagPerm.v").write_text(
        "(** dagPerm: dagDom with the command-local field reads and the permuted dispatch\n"
        f"    (k225-formal/make_dagperm.py; nodes SHA256 {sha(DAGPERM)}). *)\n"
        "From K230 Require Import RM.\nDefinition dag_nodes (n : nat) : edge * edge :=\n  match n with\n"
        f"{rows}\n  | _ => (EHalt, EHalt)\n  end.\nDefinition dagPerm : prog := mkProg dag_nodes 0 {nn}.\n",
        encoding="utf-8", newline="\n")

    def ren(t):
        t = ns(t)
        for a, b in [("Dag219", "DagPerm"), ("ProgLib219", "ProgLibPerm"), ("L2Root219", "L2RootPerm"),
                     ("Main219", "MainPerm"), ("dag219", "dagPerm")]:
            t = t.replace(a, b)
        return t

    (output / "ProgLibPerm.v").write_text(
        f"(** The 218's ProgLib219.v (SHA256 {sha(V218 / 'ProgLib219.v')}) for dagPerm. *)\n"
        + ren((V218 / "ProgLib219.v").read_text(encoding="utf-8")), encoding="utf-8", newline="\n")
    root = ren((V218 / "L2Root219.v").read_text(encoding="utf-8"))
    root = R217.subs(root, [(R217.AX1_OLD, R217.AX1_NEW, 1), ("Enum222", "EnumPerm")], "L2Root219")
    i = root.index("(** ** dispatch (node 141)")
    j = root.index("(** ** The theorems on the register machine. *)")
    root = root[:i] + (PERM_DIR / "L2RootPerm_dispatch.v").read_text(encoding="utf-8") + root[j:]
    (output / "L2RootPerm.v").write_text(
        f"(** The 218's L2Root219.v (SHA256 {sha(V218 / 'L2Root219.v')}) for dagPerm and EnumPerm: ax1 is\n"
        "    restated for the dominated AX word and the dispatch and root step are re-proved for the\n"
        f"    permuted commands (rocqperm/L2RootPerm_dispatch.v, SHA256 {sha(PERM_DIR / 'L2RootPerm_dispatch.v')}). *)\n"
        + root, encoding="utf-8", newline="\n")
    main = ren((V218 / "Main219.v").read_text(encoding="utf-8"))
    main = R217.subs(main, [
        ("Enum222 L1_Comp222 Seed222 Complete222", "EnumPerm L1_CompPerm SeedPerm Complete222 Regs215", 1),
        ("L1_Comp222.halts_from", "L1_CompPerm.halts_from"),
        ("seed222_iff_thm", "seedPerm_iff_thm"),
        ("R0_enc_seed222", "R0p_enc_seedPerm"),
        ("seed222", "seedPerm"),
    ], "Main219")
    main = re.sub(r"\bR0\b", "R0p", main)
    (output / "MainPerm.v").write_text(
        f"(** The 218's Main219.v (SHA256 {sha(V218 / 'Main219.v')}) for dagPerm, from R0p. *)\n" + main,
        encoding="utf-8", newline="\n")


def regenerate(reference, output):
    manifest = json.loads((ROOT / "manifest.json").read_text(encoding="utf-8"))
    ref = reference.resolve()
    assert sha(ref / "manifest.json") == manifest["reference_manifest_sha256"]
    rm = json.loads((ref / "manifest.json").read_text(encoding="utf-8"))
    inp = {"dense": ROOT / "inputs/215/table.tm", "sparse": ROOT / "inputs/215/table_k230labels.tm",
           "sites": ROOT / "inputs/215/sites.json", "certificate": ROOT / "inputs/215/Cert215Offsets.v"}
    sparse, dense, old = parse(inp["sparse"]), parse(inp["dense"]), parse(ref / "machine/k230.tm")
    used = {q for q, _ in sparse}
    deleted = set(range(230)) - used
    assert set(sparse) == {(q, b) for q in range(230) if q not in deleted for b in (0, 1)}
    assert len(used) == V
    labels = dense_labels(dense, sparse)
    program, stats = program_text(json.loads(inp["sites"].read_text(encoding="utf-8")))
    assert stats["depth"] <= 48, stats
    output.mkdir(parents=True, exist_ok=True)
    calculus_files(output)
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
            for a, b in [("408419", str(BOOT_STEPS)), ("[0; 0; 0; 3; 0; 0; 3; 0; 0] ++ repeat 1 167",
                                                        "[0; 0; 0; 0; 0; 0; 4; 0; 0] ++ repeat 1 40"),
                         ("zeros 181", "zeros 65"), ("a gap of 181 zero cells", "a gap of 65 zero cells"),
                         ("176 register blocks", "49 register blocks"), ("the 167 spare", "the 40 spare")]:
                assert a in body, (name, a)
                body = body.replace(a, b)
        if name == "Sim230":
            a = "exists (@nil bool), R0, 181, (repeat 1 167)."
            assert a in body
            body = body.replace(a, "exists (@nil bool), R0, 65, (repeat 1 40).")
            assert body.count("d <= 40") >= 1, "Sim230 depth bound"
            body = body.replace("d <= 40", "d <= 48")
            body = body.replace("Nat.leb d 40", "Nat.leb d 48").replace("Nat.leb _ 40", "Nat.leb _ 48")
        if name == "Interpreter230Check":
            assert body.count("Nat.leb (length Qs) 40") == 1
            body = body.replace("Nat.leb (length Qs) 40", "Nat.leb (length Qs) 48")
        if name in ("Interpreter230Check", "Sim230", "Sim230Main"):
            body = f"From {NS} Require Import Prog215 Regs215.\n" + body
            body = re.sub(r"\bp230\b", "p215", body)
            body = re.sub(r"\bp230_wf\b", "p215_wf", body)
        if name in ("Sim230", "Sim230Main"):
            body = re.sub(r"\bR0\b", "R0p", body)
        body = (f"(** Runtime-only fork of {relative}; original SHA256 {sha(source)}.\n"
                f"    Sparse labels {sorted(deleted)} are disabled; the 215's startup frame (boot\n"
                "    registers R0p); site paths of up to 48 bits. Original source immutable. *)\n") + body
        (output / f"{name}.v").write_text(body, encoding="utf-8", newline="\n")

    prog = program.replace("p227", "p215")
    (output / "Prog215.v").write_text(f"(** Source sites SHA256 {sha(inp['sites'])}. *)\n" + prog,
                                      encoding="utf-8", newline="\n")
    (output / "Table215.v").write_text(table_text(dense, V, "table215", inp["dense"]), encoding="utf-8",
                                       newline="\n")
    shutil.copyfile(ROOT / "templates/OffsetBisim230.v", output / "OffsetBisim230.v")
    cert = inp["certificate"].read_text(encoding="utf-8")
    assert "Definition Cert215 :" in cert
    shutil.copyfile(inp["certificate"], output / "Cert215Offsets.v")
    (output / "Source215.v").write_text(f"""(** Kernel-checked equivalence of the 215's source with dagPerm, for every natural-valued
    register file. *)
From Coq Require Import List.
From K230 Require Import RM Prog230.
From K230P Require Import Bisim230.
From {NS} Require Import Prog215 OffsetBisim230 Cert215Offsets DagPerm.
Import ListNotations.
Lemma certificate_forward : ocheck (ptree p215) (ptree dagPerm) Cert215 = true.
Proof. Time vm_compute. reflexivity. Qed.
Lemma certificate_backward : ocheck (ptree dagPerm) (ptree p215) (omirror Cert215) = true.
Proof. Time vm_compute. reflexivity. Qed.
Theorem p215_dagPerm R : rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof. exact (ocheck_iff p215 dagPerm Cert215 certificate_forward certificate_backward R). Qed.
Print Assumptions p215_dagPerm.
""", encoding="utf-8", newline="\n")
    (output / "Correct215.v").write_text(f"""(** Closed endpoint for the sparse-label 215-state runtime. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From {NS} Require TM230 Sim230Main.
From {NS} Require Import Source215 MainPerm.
From K230S Require Import KQuotZFC.

Theorem tm215_sparse_halts_iff_ZFC_inconsistent :
  {NS}.TM230.TM230.halts {NS}.TM230.tm {NS}.TM230.TM230.c0
  <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite {NS}.Sim230Main.tm230_rm, p215_dagPerm.
  exact dagPerm_iff_standardZFC.
Qed.
Corollary tm215_sparse_nonhalting_iff_ZFC_consistent :
  (~ {NS}.TM230.TM230.halts {NS}.TM230.tm {NS}.TM230.TM230.c0)
  <-> ~(StandardZFC ⊢TC ⊥).
Proof. rewrite tm215_sparse_halts_iff_ZFC_inconsistent. reflexivity. Qed.
Print Assumptions tm215_sparse_halts_iff_ZFC_inconsistent.
Print Assumptions tm215_sparse_nonhalting_iff_ZFC_consistent.
""", encoding="utf-8", newline="\n")
    dense_proof = (ROOT / "templates/Dense229.v").read_text(encoding="utf-8").replace("229", "215").replace("K230F", NS)
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
    (output / "Dense215.v").write_text(dense_proof, encoding="utf-8", newline="\n")
    (output / "CorrectDense215.v").write_text(
        (ROOT / "templates/CorrectDense229.v").read_text(encoding="utf-8").replace("229", "215").replace("K230F", NS),
        encoding="utf-8", newline="\n")
    receipt = {"status": "GENERATED", "states": V, "deleted_sparse_labels": sorted(deleted),
               "dense_labels": labels, "boot_steps": BOOT_STEPS,
               "reference_manifest_sha256": sha(ref / "manifest.json"), "source_stats": stats,
               "inputs_sha256": {k: sha(p) for k, p in inp.items()},
               "shared_logic_source_sha256": {p.name: sha(p) for p in sorted((ROOT / "templates/shared215").glob("*.v"))},
               "perm_sources_sha256": {p.name: sha(p) for p in sorted(PERM_DIR.glob("*.v"))},
               "dagperm_nodes_sha256": sha(DAGPERM),
               "generated_source_sha256": {p.name: sha(p) for p in sorted(output.glob("*.v"))}}
    (output.parent / "regeneration215.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, default=ROOT.parent / "vendor/k230-rocq")
    parser.add_argument("--output", type=Path, default=ROOT / "coq/215")
    args = parser.parse_args()
    r = regenerate(args.reference, args.output)
    print(r["status"], r["source_stats"], "deleted", r["deleted_sparse_labels"])


if __name__ == "__main__":
    main()
