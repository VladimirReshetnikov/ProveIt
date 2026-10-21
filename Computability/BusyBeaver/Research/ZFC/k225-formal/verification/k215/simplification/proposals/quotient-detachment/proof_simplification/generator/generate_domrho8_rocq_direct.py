#!/usr/bin/env python3
"""Mirror the checked direct Lean schema hierarchy into ordinary Rocq proofs.

This generator is untrusted. Every emitted lemma must be checked by coqc.
Only the small source language emitted by generate_domrho8_lean.py is accepted.
"""
import argparse, hashlib, re
from pathlib import Path

HEAD = """(** Direct dominated-rho8 derivation through pointwise lifting.
    Mirrors the ProveIt Source149 / CD230 guarded schema hierarchy.
    All numerical constructors are imported unchanged from Codes230.
    Generated proofs use only dominated rho8, truth and modus ponens. *)
From Coq Require Import Arith Lia.
From K230L Require Import Codes230.

Record DomImp (T : nat -> Prop) : Prop := {
  dtruth : T 0;
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, u <= a -> T (rho8 a b c u) }.
Arguments dtruth {T} _.
Arguments dmp {T} _ _ _ _ _.
Arguments drho8 {T} _ _ _ _ _ _.

Module Direct.
Lemma wim00 : wim 0 0 = 0.
Proof. reflexivity. Qed.
Lemma le_l {u x : nat} (y : nat) (h : u <= x) : u <= wim x y.
Proof. unfold wim. pose proof (P_ge_l x y). lia. Qed.
Lemma le_r {u y : nat} (x : nat) (h : u <= y) : u <= wim x y.
Proof. unfold wim. pose proof (P_ge_r x y). lia. Qed.
Local Opaque wim.

Section Proof.
Variable T : nat -> Prop.
Variable h : DomImp T.
Definition mp {a b : nat} : T (wim a b) -> T a -> T b := dmp h a b.

"""
TAIL = """
Lemma composition (a b c : nat) :
  T (wim (wim a b) (wim (wim b c) (wim a c))).
Proof. exact (cd91 a b c). Qed.

Lemma lift_right {a b : nat} (hab : T (wim a b)) (x : nat) :
  T (wim (wim x a) (wim x b)).
Proof. exact (mp (cd88 a x b) (mp (cd99 a b x) hab)). Qed.

Lemma rho8_all (a b c u : nat) : T (rho8 a b c u).
Proof.
  pose proof (mp (basisJ c (wim b c) u) (basisK c b)) as hqd.
  exact (mp (lift_right (lift_right hqd (wim a c))
             (wim (wim c u) a)) (composition (wim c u) a c)).
Qed.
End Proof.
End Direct.

(** The original public interface remains unchanged. *)
Theorem rho8_all (T : nat -> Prop) (h : DomImp T) a b c u :
  T (rho8 a b c u).
Proof. exact (Direct.rho8_all T h a b c u). Qed.
Print Assumptions rho8_all.
"""

def convert_names(s):
    s = re.sub(r"\b(b\d+|cd\d+|basis[A-Z]) h\b", r"\1", s)
    for a,b in [("h.truth","(dtruth h)"),("h.rho8","drho8 h"),
                ("h.mp","mp"),("Code254.rho8","rho8"),
                ("Nat.zero_le","Nat.le_0_l"),("Nat","nat"),("≤","<=")]:
        if a == "Nat":
            s = re.sub(r"\bNat\b(?!\.)",b,s)
        else:
            s = s.replace(a,b)
    return s

def convert_body(s):
    # Replace innermost parenthesized show/ascription nodes first.
    # Each normalization is justified by the separately proved wim00.
    while "(show " in s:
        start = s.rindex("(show ")
        level = 0
        for end in range(start,len(s)):
            if s[end] == "(": level += 1
            elif s[end] == ")":
                level -= 1
                if level == 0: break
        else: raise ValueError("unbalanced show")
        whole = s[start+1:end]
        m = re.fullmatch(r"show T (.*?) from by simpa only \[(wim00|Code254.rho8)\] using (.*)",whole,re.S)
        if not m: raise ValueError("unrecognized show "+whole)
        goal,rule,pf = m.groups()
        if rule == "Code254.rho8":
            replacement = "("+pf+")"
        else:
            replacement = "(ltac:(let Hnorm := fresh in pose proof ("+pf+") as Hnorm; repeat rewrite wim00 in Hnorm; repeat rewrite wim00; exact Hnorm) : T "+goal+")"
        s = s[:start]+replacement+s[end+1:]
    return convert_names(s)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("lean",type=Path)
    ap.add_argument("output",type=Path)
    args=ap.parse_args()
    source=args.lean.read_text()
    assert "theorem lift_right" in source and "private inductive Proof" not in source
    body=source[source.index("private theorem b0"):source.index("theorem composition")]
    chunks=re.findall(r"private theorem (\w+)(.*?)(?=\nprivate theorem |\nend\n|\Z)",body,re.S)
    out=[HEAD]
    count=0
    for name,chunk in chunks:
        if not re.fullmatch(r"(b|cd)\d+|basis[KJ]",name):
            raise ValueError(name)
        sig,pf=chunk.split(":=",1)
        sig=convert_names(sig.strip())
        pf=pf.strip()
        prefix="by\n  simpa only [wim00] using "
        if pf.startswith(prefix):
            pf=pf[len(prefix):]
        pf=convert_body(pf)
        if "by " in pf or "simpa" in pf or "show " in pf:
            raise ValueError("untranslated proof "+name)
        out.append("Lemma "+name+" "+sig+".\n")
        # All substitution normalizations are already explicit cast nodes.
        out.append("Proof. exact ("+pf+"). Qed.\n\n")
        count+=1
    out.append(TAIL)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text("".join(out))
    print("Mirrored",count,"helper declarations; bytes",args.output.stat().st_size)
    print("Input SHA256",hashlib.sha256(source.encode()).hexdigest())
    print("Output SHA256",hashlib.sha256(args.output.read_bytes()).hexdigest())
if __name__=="__main__":main()
