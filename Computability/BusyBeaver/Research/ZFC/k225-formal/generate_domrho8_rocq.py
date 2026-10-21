#!/usr/bin/env python3
"""Render DomRho8.v, the Rocq twin of DomRho8.lean.

  python generate_domrho8_rocq.py DOMRHO8_LEAN NAMESPACE OUT_V

DomRho8.lean is generated from Source 149's certificate by generate_domrho8_lean.py; its term
definitions, conversion lemmas and node theorems are one line each, in a fixed small syntax.
This script renders them in Rocq line by line (the same terms, the same proof terms), so both
kernels check the same derivation. Untrusted: Rocq checks every lemma.
"""
import re
import sys

src, ns, out = sys.argv[1], sys.argv[2], sys.argv[3]
lines = open(src, encoding="utf-8").read().split("\n")


def term(e):
    """a Lean proof/term expression -> Rocq"""
    e = e.replace("Nat.le_refl _", "le_n _").replace("Nat.zero_le _", "Nat.le_0_l _")
    e = re.sub(r"\bn(\d+) h\b", r"n\1 T h", e)
    e = re.sub(r"\(rfl : (t\d+) v = \1 v\)", r"eq_refl", e)
    e = e.replace("h.truth", "dtruth h")
    e = re.sub(r"h\.rho8 ", "drho8 h ", e)
    e = re.sub(r"h\.mp \(a := ([^)]*)\) \(b := ([^)]*)\) ", r"dmp h (\1) (\2) ", e)
    e = e.replace("h.mp ", "dmp h _ _ ")
    e = re.sub(r"sub \[([^\]]*)\]", lambda m: "sub [" + m.group(1).replace(", ", "; ") + "]", e)
    e = e.replace("congr (congrArg wim ", "f_equal2 wim (")
    return e


V = []
w = V.append
w(f"""(** Dominated rho8 instances derive every rho8 instance: the Rocq twin of DomRho8.lean.

    For a predicate [T] on codes that holds of truth (code 0), is closed under modus ponens, and
    contains every instance [rho8 a b c u] whose fourth argument is at most its first
    ([DomImp]), [rho8_all] derives every instance.  The derivation is Source 149's certificate
    (theory/dominated_rho8_full_certificate.json, 3,728 nodes); rendered from DomRho8.lean by
    k225-formal/generate_domrho8_rocq.py.  Codes need not decode. *)
From Stdlib Require Import Arith Lia List.
From K230L Require Import Codes230.
Import ListNotations.

Record DomImp (T : nat -> Prop) : Prop := {{
  dtruth : T 0;
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, u <= a -> T (rho8 a b c u) }}.
Arguments dtruth {{T}} _.
Arguments dmp {{T}} _ _ _ _ _.
Arguments drho8 {{T}} _ _ _ _ _ _.

Lemma le_l {{u x}} y : u <= x -> u <= wim x y.
Proof. intros H. unfold wim. pose proof (P_ge_l x y). lia. Qed.

Lemma le_r {{u y}} x : u <= y -> u <= wim x y.
Proof. intros H. unfold wim. pose proof (P_ge_r x y). lia. Qed.

Definition sub (l : list nat) (i : nat) : nat := nth i l 0.

Lemma wim00 : wim 0 0 = 0.
Proof. reflexivity. Qed.

Definition cast_T {{T : nat -> Prop}} {{x y : nat}} (e : x = y) (H : T x) : T y :=
  match e in _ = z return T z with eq_refl => H end.
""")
nt = nc = nn = 0
for ln in lines:
    m = re.match(r"def (t\d+) \(v : Nat → Nat\) : Nat := (.*)$", ln)
    if m:
        w(f"Definition {m.group(1)} (v : nat -> nat) : nat := {m.group(2)}.")
        nt += 1
        continue
    m = re.match(r"theorem (c\d+_\d+) \(v : Nat → Nat\) : (t\d+) v = (t\d+) v := (.*)$", ln)
    if m:
        pf = m.group(4)
        mm = re.match(r"\((c\d+_\d+) v\)\.symm$", pf)
        if mm:
            pf = f"eq_sym ({mm.group(1)} v)"
        else:
            mm = re.match(r"\((congr .*)\)\.trans wim00$", pf)
            pf = f"eq_trans ({term(mm.group(1))}) wim00" if mm else term(pf)
        w(f"Lemma {m.group(1)} (v : nat -> nat) : {m.group(2)} v = {m.group(3)} v.\n"
          f"Proof. exact ({pf}). Qed.")
        nc += 1
        continue
    m = re.match(r"theorem (n\d+) \(v : Nat → Nat\) : T \((t\d+) v\) := (.*)$", ln)
    if m:
        pf = m.group(3)
        mm = re.match(r"show T \((t\d+) v\) from let w := (sub \[[^\]]*\]); (.*)$", pf)
        if mm:
            pf = f"(let w := {term(mm.group(2))} in {term(mm.group(3))} : T ({mm.group(1)} v))"
        else:
            mm = re.match(r"cast_T \((c\d+_\d+) v\) \(show T \((t\d+) v\) from let w := (sub \[[^\]]*\]); (.*)\)$", pf)
            if mm:
                pf = (f"cast_T ({mm.group(1)} v) (let w := {term(mm.group(3))} in {term(mm.group(4))} "
                      f": T ({mm.group(2)} v))")
            else:
                pf = term(pf)
        w(f"Lemma {m.group(1)} (T : nat -> Prop) (h : DomImp T) (v : nat -> nat) : T ({m.group(2)} v).\n"
          f"Proof. exact ({pf}). Qed.")
        nn += 1
        continue
    m = re.match(r"  n(\d+) h \(sub \[(.*)\]\)$", ln)
    if m:
        root, slots = m.group(1), m.group(2).replace(", ", "; ")
        w(f"""
(** Every rho8 instance, from the dominated ones. *)
Theorem rho8_all (T : nat -> Prop) (h : DomImp T) a b c u : T (rho8 a b c u).
Proof. exact (n{root} T h (sub [{slots}])). Qed.

Print Assumptions rho8_all.""")
assert nt and nn and "rho8_all" in V[-1], (nt, nc, nn)
open(out, "w", encoding="utf-8", newline="\n").write("\n".join(V) + "\n")
print("wrote", out, nt, "terms", nc, "conversions", nn, "nodes")
