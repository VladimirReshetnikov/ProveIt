#!/usr/bin/env python3
"""Emit only untrusted template data; the Rocq kernel checks every replay."""
from pathlib import Path
import argparse
import hashlib
import json


def b(x):
    if x not in (True, False, 0, 1):
        raise ValueError(x)
    return "true" if x else "false"


def seg(x):
    if x[0] == "b":
        return "SB " + b(x[1])
    if x[0] == "r":
        return f"SR {b(x[1])} {x[2]} {x[3]}"
    if x == ["x", "none", 0]:
        return "SBox (BPlain FNone)"
    raise ValueError(x)


def segs(xs):
    return "[" + "; ".join(seg(x) for x in xs) + "]"


def conf(s):
    return f"({s[0]},{b(s[1])},{segs(s[2])},{segs(s[3])})"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("input", type=Path)
    ap.add_argument("--output", type=Path, default=Path("src/Refactor/LeftFrame215.v"))
    args = ap.parse_args()
    raw = args.input.read_bytes()
    templates = json.loads(raw)["templates_data"]
    assert len(templates) == 35
    lines = [f"(** Input SHA256: {hashlib.sha256(raw).hexdigest()}. Untrusted finite data. *)",
             "From Coq Require Import Lists.List Bool.Bool Arith.Arith.",
             "From K215F Require Import Runtime230Core.",
             "From Refactor Require Import LeftFrame.",
             "Import ListNotations.", "",
             "Record template := mkTemplate { start : sconf; steps : nat; right : list seg }.",
             "Definition templates : list template := ["]
    for i, t in enumerate(templates):
        assert t["id"] == i and t["pre_home"][:3] == [2, True, []]
        assert t["steps"] == len(t["trace"])
        lines += [f"  (* Template {i}: {t['key'][3]} {t['key'][4]}, suffix {t['key'][2]}. *)",
                  f"  mkTemplate {conf(t['start'])} {t['steps']} {segs(t['pre_home'][3])}" +
                  (";" if i < len(templates) - 1 else "].")]
    lines += ["", "Definition seg_dec (x y : seg) : {x = y} + {x <> y}.",
              "Proof. decide equality; first [apply Nat.eq_dec | apply bool_dec | apply boxst_dec]. Defined.",
              "Definition sconf_dec (x y : sconf) : {x = y} + {x <> y}.",
              "Proof. unfold sconf; repeat decide equality. Defined.",
              "", "Definition checked (t : template) : bool :=",
              "  match run_local None (steps t) (start t) with",
              "  | None => false",
              "  | Some s => if sconf_dec s (2,true,[],right t) then true else false",
              "  end.", "",
              "Lemma checked_ok t : checked t = true ->",
              "  run_local None (steps t) (start t) = Some (2,true,[],right t).",
              "Proof.",
              "  unfold checked. destruct (run_local None (steps t) (start t)) as [s|] eqn:E; [|discriminate].",
              "  destruct (sconf_dec s (2,true,[],right t)) as [Hs|Hs]; [intros _; now rewrite Hs|discriminate].",
              "Qed.", "",
              "Theorem template_count : length templates = 35.",
              "Proof. reflexivity. Qed.",
              "Theorem all_checked : forallb checked templates = true.",
              "Proof. vm_compute. reflexivity. Qed.", "",
              "Theorem template_replay t F : In t templates ->",
              "  run_local None (steps t) (add_left F (start t)) =",
              "  Some (add_left F (2,true,[],right t)).",
              "Proof.",
              "  intro Ht. apply run_local_frame, checked_ok.",
              "  exact (proj1 (forallb_forall checked templates) all_checked t Ht).",
              "Qed.", "",
              "Print Assumptions all_checked.",
              "Print Assumptions template_replay.", ""]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines))
    print(json.dumps({"templates": len(templates), "steps": sum(t["steps"] for t in templates),
                      "input_sha256": hashlib.sha256(raw).hexdigest(),
                      "output_sha256": hashlib.sha256(args.output.read_bytes()).hexdigest()}, indent=2))


if __name__ == "__main__":
    main()
