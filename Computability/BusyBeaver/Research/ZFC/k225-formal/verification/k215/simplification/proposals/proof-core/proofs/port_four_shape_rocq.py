#!/usr/bin/env python3
"""Translate the four-shape direct proof terms, not tactic outcomes, to Rocq/Coq."""
from pathlib import Path
import re
HERE=Path(__file__).resolve().parent
source=HERE/'formal/BusyBeaver/ZFC/FourShapeImplication.lean'
out=HERE/'rocq/FourShapeImplication.v'
text=source.read_text()
starts=list(re.finditer(r'^private theorem ((?:b|cd)\d+)\b',text,re.M))
chunks=[]
for m in starts:
 end=text.find('\nprivate theorem ',m.end())
 if end<0:raise ValueError('missing declaration boundary')
 decl=text[m.start():end].strip()
 header,proof=decl.split(':=',1)
 proof=proof.strip()
 if proof.startswith('(show '):
  proof=proof.split(' using ',1)[1].strip()
  assert proof.endswith(')')
  proof=proof[:-1]
 for old,new in [('h.mp','mp'),('h.rho8','row'),('h.truth','seed'),('τ','tau'),('Allowed.llr','allow_llr'),('Allowed.ll','allow_ll'),('Allowed.right','allow_right'),('Allowed.same','allow_same')]:
  proof=proof.replace(old,new)
 proof=re.sub(r'\b((?:b|cd)\d+) h\b',r'\1',proof)
 header=header.replace('private theorem ','Lemma ').replace('τ','tau')
 chunks.append(header.strip()+'.\nProof. exact ('+proof+'). Qed.\n')
assert len(chunks)==84,len(chunks)
preamble='''(* Representation-independent implication from four finite axiom shapes.
   Direct proof-term port of FourShapeImplication.lean in this packet.
   Only the paths empty, R, LL and LLR are admitted. Allowed is not
   assumed closed under arbitrary contexts. No truth constant is required.
   The translator is untrusted; coqc and recursive coqchk check its output. *)

Module FourShapeImplication.
Section Generic.
Context {A : Type}.
Variable wim : A -> A -> A.
Definition rho8 (a b c u : A) : A :=
  wim (wim (wim c u) a) (wim (wim a c) (wim b c)).
Inductive Allowed : A -> A -> Prop :=
  | allow_same (u : A) : Allowed u u
  | allow_right (x u : A) : Allowed u (wim x u)
  | allow_ll (u x y : A) : Allowed u (wim (wim u x) y)
  | allow_llr (x u y z : A) : Allowed u (wim (wim (wim x u) y) z).
Local Infix "≼" := Allowed (at level 50).
Variable T : A -> Prop.
Hypothesis mp : forall {a b}, T (wim a b) -> T a -> T b.
Hypothesis ax_same : forall a b c, T (rho8 a b c a).
Hypothesis ax_right : forall x u b c, T (rho8 (wim x u) b c u).
Hypothesis ax_ll : forall u x y b c, T (rho8 (wim (wim u x) y) b c u).
Hypothesis ax_llr : forall x u y z b c, T (rho8 (wim (wim (wim x u) y) z) b c u).
Lemma row a b c u : Allowed u a -> T (rho8 a b c u).
Proof.
  intro hu; destruct hu.
  - apply ax_same.
  - apply ax_right.
  - apply ax_ll.
  - apply ax_llr.
Qed.

Section Seed.
Variable tau : A.
Hypothesis seed : T tau.

'''
post='''
Lemma basisK (a b : A) : T (wim a (wim b a)).
Proof. exact (b60 a b). Qed.
Lemma basisP (a b : A) : T (wim (wim (wim a b) a) a).
Proof. exact (b25 a b). Qed.
Lemma composition_seed (a b c : A) : T (wim (wim a b) (wim (wim b c) (wim a c))).
Proof. exact (cd91 a b c). Qed.
Lemma distribution_seed (a b c : A) : T (wim (wim a (wim b c)) (wim (wim a b) (wim a c))).
Proof. exact (cd106 a b c). Qed.
Lemma compose_derived {a b c : A}
    (hab : T (wim a b)) (hbc : T (wim b c)) : T (wim a c).
Proof. exact (mp (mp (composition_seed a b c) hab) hbc). Qed.
Lemma under_antecedent (z : A) {x y : A}
    (hxy : T (wim x y)) : T (wim (wim z x) (wim z y)).
Proof.
  exact (mp (mp (cd103 (wim z x) (wim x y) (wim z y))
    (composition_seed z x y)) hxy).
Qed.
Lemma rho8_seed (a b c u : A) : T (rho8 a b c u).
Proof.
  exact (compose_derived
    (compose_derived (composition_seed (wim c u) a c)
      (under_antecedent (wim a c) (basisP c u)))
    (under_antecedent (wim a c) (basisK c b))).
Qed.
End Seed.

Theorem rho8_all (a b c u : A) : T (rho8 a b c u).
Proof.
  exact (rho8_seed (rho8 a a a a) (row a a a a (allow_same a)) a b c u).
Qed.
Theorem composition (a b c : A) : T (wim (wim a b) (wim (wim b c) (wim a c))).
Proof.
  exact (composition_seed (rho8 a a a a) (row a a a a (allow_same a)) a b c).
Qed.
Theorem distribution (a b c : A) : T (wim (wim a (wim b c)) (wim (wim a b) (wim a c))).
Proof.
  exact (distribution_seed (rho8 a a a a) (row a a a a (allow_same a)) a b c).
Qed.
End Generic.
Print Assumptions rho8_all.
Print Assumptions composition.
Print Assumptions distribution.
End FourShapeImplication.
'''
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(preamble+'\n'.join(chunks)+post)
print(out)
