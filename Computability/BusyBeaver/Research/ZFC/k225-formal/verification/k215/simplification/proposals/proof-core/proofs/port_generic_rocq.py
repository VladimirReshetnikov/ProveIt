#!/usr/bin/env python3
"""Translate the finite direct proof terms, not tactic outcomes, to Rocq/Coq."""
from pathlib import Path
import re
HERE=Path(__file__).resolve().parent
source=HERE/'formal/BusyBeaver/ZFC/DominatedImplication.lean'
out=HERE/'rocq/DominatedImplication.v'
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
 for old,new in [('h.mp','mp'),('h.rho8','row'),('h.truth','seed'),('τ','tau'),('L.refl','below_refl')]:
  proof=proof.replace(old,new)
 proof=re.sub(r'\b((?:b|cd)\d+) h\b',r'\1',proof)
 header=header.replace('private theorem ','Lemma ').replace('τ','tau')
 chunks.append(header.strip()+'.\nProof. exact ('+proof+'). Qed.\n')
assert len(chunks)==84,len(chunks)
preamble='''(* Representation-independent dominated implication, direct proof-term port.
   Based on ProveIt aa66d0a33f1f8237a348899eb8095b045a502832 DomRho8,
   with the thirteen checked condensed-detachment shortcuts of this packet.
   The carrier need not encode formulas injectively. No truth constant,
   bottom element, transitivity, formula decoder, or zero-collapse axiom is used.
   Proof terms below are kernel checked; the translator is untrusted. *)

Module DominatedImplication.
Section Generic.
Context {A : Type}.
Variables (wim : A -> A -> A) (below : A -> A -> Prop).
Hypothesis below_refl : forall a, below a a.
Hypothesis grow_left : forall u x y, below u x -> below u (wim x y).
Hypothesis grow_right : forall u y x, below u y -> below u (wim x y).
Local Infix "≼" := below (at level 50).
Definition rho8 (a b c u : A) : A :=
  wim (wim (wim c u) a) (wim (wim a c) (wim b c)).
Variable T : A -> Prop.
Hypothesis mp : forall {a b}, T (wim a b) -> T a -> T b.
Hypothesis row : forall a b c u, below u a -> T (rho8 a b c u).
Local Definition le_l {u x : A} (y : A) (h : u ≼ x) : u ≼ wim x y :=
  grow_left u x y h.
Local Definition le_r {u y : A} (x : A) (h : u ≼ y) : u ≼ wim x y :=
  grow_right u y x h.

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
  exact (rho8_seed (rho8 a a a a) (row a a a a (below_refl a)) a b c u).
Qed.
Theorem composition (a b c : A) : T (wim (wim a b) (wim (wim b c) (wim a c))).
Proof.
  exact (composition_seed (rho8 a a a a) (row a a a a (below_refl a)) a b c).
Qed.
Theorem distribution (a b c : A) : T (wim (wim a (wim b c)) (wim (wim a b) (wim a c))).
Proof.
  exact (distribution_seed (rho8 a a a a) (row a a a a (below_refl a)) a b c).
Qed.
End Generic.
Print Assumptions rho8_all.
Print Assumptions composition.
Print Assumptions distribution.
End DominatedImplication.
'''
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(preamble+'\n'.join(chunks)+post)
print(out)
