From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import map_gal char0 abel.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticGaloisAction QuinticSolvableCriterion
  QuinticThetaOrbit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The Galois-theoretic form of the Frobenius--Dummit criterion for an
    irreducible rational quintic.  The concrete permutation image is the
    faithful, transitive image constructed in [QuinticGaloisAction]; the
    finite-group classification is supplied by [QuinticSolvableCriterion]. *)
Module PolynomialFormulasQuinticGaloisCriterion.

Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasQuinticGaloisAction.
Import PolynomialFormulasQuinticSolvableCriterion.
Import PolynomialFormulasQuinticThetaOrbit.

Local Open Scope group_scope.
Local Open Scope action_scope.

Section IrreducibleQuintic.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_irr : irreducible_poly p.

Let L := numfield p.

(** The directly executable finite Boolean attached to the concrete
    permutation image. *)
Definition quintic_galois_contained_in_conjugate_F20b : bool :=
  contained_in_conjugate_F20b
    (@quintic_galois_image p p_size p_irr).

(** Boolean equality version of the criterion.  In MathComp, [solvable] is
    itself a Boolean predicate, so this is also a decision procedure once
    the finite concrete image has been supplied. *)
Theorem quintic_galois_solvable_F20b :
  solvable 'Gal({:L} / 1%AS) =
    quintic_galois_contained_in_conjugate_F20b.
Proof.
rewrite -(@quintic_galois_image_solvableE p p_size p_irr).
exact: solvable_transitive_S5_criterion
  (@quintic_galois_image_transitive p p_size p_irr).
Qed.

(** Propositional wrapper spelling out the witness conjugate. *)
Corollary quintic_galois_solvable_iff_conjugate_F20 :
  (solvable 'Gal({:L} / 1%AS) <->
    exists x : S5,
      @quintic_galois_image p p_size p_irr \subset
        (standard_F20 :^ x)).
Proof.
rewrite -(@quintic_galois_image_solvableE p p_size p_irr).
exact: solvable_transitive_S5_iff
  (@quintic_galois_image_transitive p p_size p_irr).
Qed.

End IrreducibleQuintic.

(** The six inverse-representative theta tables are the six points of the
    conjugate-[F20] action.  Since [act_exponent] is anti-multiplicative, the
    genuine left action on exponent tables uses [g^-1].  Isolating that
    inverse here makes the conjugation orientation explicit. *)

Definition inverse_representative_theta_orbit (i : 'I_6) :
    seq quintic_exponent :=
  theta_table_image ((representative i)^-1).

Definition act_theta_table (g : S5) (table : seq quintic_exponent) :
    seq quintic_exponent :=
  map (act_exponent g^-1) table.

Lemma act_theta_table_one (table : seq quintic_exponent) :
  act_theta_table 1 table = table.
Proof.
rewrite /act_theta_table invg1.
elim: table=> [|d table IH] //=.
by rewrite act_exponent_one IH.
Qed.

Lemma act_theta_table_mul (g h : S5) (table : seq quintic_exponent) :
  act_theta_table (g * h)%g table =
    act_theta_table g (act_theta_table h table).
Proof.
rewrite /act_theta_table invgM -map_comp.
apply: eq_map=> d.
by rewrite /= -act_exponent_mul.
Qed.

Definition theta_orbit_stableb (G : {group S5}) (i : 'I_6) : bool :=
  [forall g in G,
    perm_eq
      (act_theta_table g (inverse_representative_theta_orbit i))
      (inverse_representative_theta_orbit i)].

Definition has_stable_inverse_theta_orbitb (G : {group S5}) : bool :=
  [exists i : 'I_6, theta_orbit_stableb G i].

(** Pointwise orientation certificate.  Stabilizing the orbit indexed by
    [(representative i)^-1] is exactly membership in the correspondingly
    conjugated Frobenius group. *)
Lemma act_inverse_representative_theta_orbitP g i :
  perm_eq
      (act_theta_table g (inverse_representative_theta_orbit i))
      (inverse_representative_theta_orbit i) =
    (g \in (standard_F20 :^ (representative i)^-1)).
Proof.
rewrite /act_theta_table /inverse_representative_theta_orbit.
rewrite -theta_table_image_mul theta_table_images_perm_iff.
rewrite invgM !invgK mem_conjgV conjgE.
exact: erefl.
Qed.

Lemma theta_orbit_stablebE G i :
  theta_orbit_stableb G i =
    (G \subset (standard_F20 :^ (representative i)^-1)).
Proof.
apply/idP/idP.
- move/forall_inP=> stable.
  apply/subsetP=> g Gg.
  move: (stable g Gg).
  by rewrite act_inverse_representative_theta_orbitP.
- move/subsetP=> subG.
  apply/forall_inP=> g Gg.
  rewrite act_inverse_representative_theta_orbitP.
  exact: subG g Gg.
Qed.

(** The arbitrary conjugating permutation can be replaced by one of the six
    inverse representatives.  If [representative i] is in the left coset of
    [x^-1], then [x * representative i] lies in [F20]; conjugating first by
    [x^-1] and then by this element proves the required containment. *)
Theorem contained_in_conjugate_F20b_theta_orbitE (G : {group S5}) :
  contained_in_conjugate_F20b G =
    has_stable_inverse_theta_orbitb G.
Proof.
apply/idP/idP.
- move/existsP=> [x subG].
  pose i := representative_index x^-1.
  apply/existsP; exists i.
  rewrite theta_orbit_stablebE.
  apply/subsetP=> g Gg.
  rewrite mem_conjgV.
  have gx : g ^ x^-1 \in standard_F20.
    have := subsetP subG g Gg.
    by rewrite mem_conjg.
  have hxr : (x * representative i)%g \in standard_F20.
    move: (representative_indexP x^-1).
    by rewrite /same_left_cosetb invgK.
  have hconj : (g ^ x^-1) ^ (x * representative i)%g \in standard_F20 :=
    groupJ gx hxr.
  have hcancel : (x^-1 * (x * representative i))%g = representative i.
    by rewrite mulgA mulVg mul1g.
  move: hconj.
  by rewrite -conjgM hcancel.
- move/existsP=> [i stable].
  apply/existsP; exists (representative i)^-1.
  by move: stable; rewrite theta_orbit_stablebE.
Qed.

Corollary contained_in_conjugate_F20_iff_theta_orbit
    (G : {group S5}) :
  ((exists x : S5, G \subset (standard_F20 :^ x)) <->
    exists i : 'I_6, theta_orbit_stableb G i).
Proof.
split=> h.
- have hb : contained_in_conjugate_F20b G.
    by apply/existsP.
  have hs : has_stable_inverse_theta_orbitb G.
    by move: hb; rewrite contained_in_conjugate_F20b_theta_orbitE.
  exact: (elimT existsP hs).
- have hs : has_stable_inverse_theta_orbitb G.
    by apply/existsP.
  have hb : contained_in_conjugate_F20b G.
    by move: hs; rewrite -contained_in_conjugate_F20b_theta_orbitE.
  exact: (elimT existsP hb).
Qed.

Section IrreducibleQuinticThetaOrbit.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_irr : irreducible_poly p.

Let L := numfield p.

(** Solvability of the quintic Galois group is equivalently witnessed by one
    of the six explicit inverse-representative theta orbits being permuted by
    every element of its faithful permutation image. *)
Theorem quintic_galois_solvable_iff_stable_theta_orbit :
  (solvable 'Gal({:L} / 1%AS) <->
    exists i : 'I_6,
      theta_orbit_stableb
        (@quintic_galois_image p p_size p_irr) i).
Proof.
rewrite quintic_galois_solvable_iff_conjugate_F20.
exact: contained_in_conjugate_F20_iff_theta_orbit.
Qed.

End IrreducibleQuinticThetaOrbit.

End PolynomialFormulasQuinticGaloisCriterion.
