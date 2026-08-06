From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import map_gal char0 abel.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues QuinticGaloisAction QuinticChapman.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.

(** The five-cycle extracted from the transitive Galois action of an
    irreducible quintic.  The group-theoretic part is kept independent of
    splitting fields; the final theorem lifts the resulting permutation and
    reindexes the canonical roots so that Chapman's standard [five_cycle]
    acts literally. *)
Module PolynomialFormulasQuinticFiveCycle.

Module F20 := PolynomialFormulasQuinticF20Data.
Module QTV := PolynomialFormulasQuinticThetaValues.
Module QGA := PolynomialFormulasQuinticGaloisAction.

(** Every transitive subgroup of [S5] contains a conjugate of the chosen
    standard five-cycle. *)
Lemma transitive_S5_contains_conjugate_five_cycle
    (G : {group F20.S5}) :
  [transitive G, on [set : 'I_5] | 'P] ->
  exists s : F20.S5, (F20.five_cycle ^ s)%g \in G.
Proof.
move=> htrans.
have h5G : (5 %| #|G|)%N.
  move: (atrans_dvd htrans).
  by rewrite cardsT card_ord.
have [c cG hcorder] := Cauchy (isT : prime 5) h5G.
have hcSylow : 5.-Sylow([set : F20.S5]) <[c]>.
  rewrite pHallE subsetT -orderE hcorder cardsT /F20.S5 card_Sn.
  rewrite andTb p_part (logn_fact 5) //.
  do 5! rewrite big_nat_recr //=.
  by rewrite big_geq //=.
have [s _ hcycle] := Sylow_trans F20.standard_C5_sylow hcSylow.
exists s.
have hcsub : (<[c]>%G \subset G).
  apply/subsetP=> x /cycleP[i ->].
  exact: groupX cG.
apply: (subsetP hcsub).
rewrite hcycle -cycleJ.
exact: cycle_id (F20.five_cycle ^ s).
Qed.

Section IrreducibleQuintic.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_irr : irreducible_poly p.

Let L := numfield p.
Let roots : 5.-tuple L := @QGA.quintic_root_tuple p p_size.

Definition reindexed_quintic_roots (s : F20.S5) : 5.-tuple L :=
  QTV.permute_quintic_roots s roots.

(** A full splitting-field Galois element is a genuine ring automorphism.
    Its group inverse supplies both cancellation directions. *)
Lemma full_gal_rmorphism_bijective (u : gal_of (L:=L) fullv) :
  bijective (gal_repr u : {rmorphism L -> L}).
Proof.
apply: (@Bijective L L (gal_repr u) (gal_repr (u^-1)%g)).
- move=> x.
  have h := @galM rat L fullv u (u^-1)%g x (memvf x).
  rewrite mulgV gal_id in h.
  exact: esym h.
- move=> x.
  have h := @galM rat L fullv (u^-1)%g u x (memvf x).
  rewrite mulVg gal_id in h.
  exact: esym h.
Qed.

(** Direct input for
    [quintic_theta_value_injective_of_five_cycle_automorphism]: after one
    explicit reindexing, a bijective ring morphism sends root [k] to root
    [five_cycle k]. *)
Theorem irreducible_quintic_five_cycle_automorphism :
  exists (s : F20.S5) (sigma : {rmorphism L -> L}),
    bijective sigma /\
    forall k : 'I_5,
      sigma (tnth (reindexed_quintic_roots s) k) =
        tnth (reindexed_quintic_roots s) (F20.five_cycle k).
Proof.
have [s hs] := transitive_S5_contains_conjugate_five_cycle
  (QGA.quintic_galois_image_transitive p_size p_irr).
rewrite /QGA.quintic_galois_image in hs.
case/morphimP: hs=> u _ huGal huperm.
have huperm' : @QGA.quintic_gal_perm p p_size u =
    (F20.five_cycle ^ s)%g.
  exact: esym huperm.
exists s, (gal_repr u : {rmorphism L -> L}); split.
- exact: full_gal_rmorphism_bijective.
- move=> k.
  rewrite /reindexed_quintic_roots
    !QTV.tnth_permute_quintic_roots.
  change (u (tnth (@QGA.quintic_root_tuple p p_size) (s k)) =
    tnth (@QGA.quintic_root_tuple p p_size) (s (F20.five_cycle k))).
  rewrite -(@QGA.quintic_gal_permP p p_size u (s k)).
  rewrite huperm' F20.conjg_permE permK.
  by [].
Qed.

End IrreducibleQuintic.

End PolynomialFormulasQuinticFiveCycle.
