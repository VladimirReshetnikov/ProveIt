From mathcomp Require Import all_ssreflect all_fingroup all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The finite-dimensional Reynolds argument underlying the constant blocks
    in Lazard's invariant-module theorem.

    This theorem is deliberately stated over a MathComp [vectType].  It proves
    the complete averaging result available from the installed finite linear
    algebra: the Reynolds endomorphism is idempotent, and its image and fixed
    space are exactly the vectors fixed by every element of the finite group.
    The canonical MathComp [vbasis] then supplies a finite basis of that
    invariant space.

    The visible hypothesis [cardG_neq0] is precisely the condition required
    to divide by the group order.  It is automatic in characteristic zero,
    but the theorem also applies in positive characteristic whenever that
    characteristic does not divide [#|G|]. *)
Module PolynomialFormulasLazardInvariantReynoldsFinite.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope group_scope.

Section Reynolds.

Variables (K : fieldType) (G : finGroupType) (V : vectType K).
Variable rho : G -> 'End(V).

(** These two laws expose [rho] as an honest left linear action.  Composition
    is written explicitly so that no opaque representation package is hidden
    in the section interface.  The averaging conclusions below actually need
    only [rhoM]; Coq therefore omits the unused [rho1] parameter from those
    individual exported constants.  This is a valid strengthening, not an
    assumed identity law.  Concrete action adapters should still establish
    both laws. *)
Hypothesis rho1 : rho 1 = \1%VF.
Hypothesis rhoM : forall g h, rho (g * h) = (rho g \o rho h)%VF.

(** The exact averaging hypothesis. *)
Hypothesis cardG_neq0 : (#|G|%:R : K) != 0.

(** The normalized group average as a linear endomorphism. *)
Definition reynolds : 'End(V) :=
  (#|G|%:R : K)^-1 *: \sum_(g : G) rho g.

(** The common fixed subspace of the action. *)
Definition common_fixed_space : {vspace V} :=
  (\bigcap_(g : G) fixedSpace (rho g))%VS.

Lemma common_fixed_spaceP v :
  reflect (forall g : G, rho g v = v) (v \in common_fixed_space).
Proof.
rewrite /common_fixed_space.
apply: (iffP subv_bigcapP).
- move=> h g; apply/fixedSpaceP; exact: h g erefl.
- move=> h g _; apply/fixedSpaceP; exact: h g.
Qed.

Lemma reynolds_apply v :
  reynolds v =
    (#|G|%:R : K)^-1 *: \sum_(g : G) rho g v.
Proof. by rewrite /reynolds scale_lfunE sum_lfunE. Qed.

(** Left multiplication permutes the finite group, so averaging is fixed by
    every action map. *)
Lemma reynolds_invariant (h : G) v :
  rho h (reynolds v) = reynolds v.
Proof.
rewrite !reynolds_apply linearZ linear_sum.
congr (_ *: _).
under [LHS]eq_bigr => g _ do
  rewrite -comp_lfunE -(rhoM h g).
by rewrite (reindex_inj (mulgI h)).
Qed.

Lemma reynolds_mem_common v :
  reynolds v \in common_fixed_space.
Proof.
apply/common_fixed_spaceP=> h.
exact: reynolds_invariant.
Qed.

(** Averaging a common fixed vector gives the vector itself. *)
Lemma reynolds_fix_common v :
  v \in common_fixed_space -> reynolds v = v.
Proof.
move/common_fixed_spaceP=> hv.
rewrite reynolds_apply.
under eq_bigr => g _ do rewrite hv.
rewrite sumr_const cardsT -scaler_nat scalerA mulVf // scale1r.
Qed.

(** Pointwise and endomorphism forms of Reynolds idempotence. *)
Lemma reynolds_idempotent v :
  reynolds (reynolds v) = reynolds v.
Proof. exact: reynolds_fix_common (reynolds_mem_common v). Qed.

Lemma reynolds_comp_self :
  (reynolds \o reynolds)%VF = reynolds.
Proof. by apply/lfunP=> v; rewrite comp_lfunE reynolds_idempotent. Qed.

(** The Reynolds image is exactly the common invariant subspace. *)
Lemma reynolds_image_eq_common_fixed :
  limg reynolds = common_fixed_space.
Proof.
apply/subv_anti/andP; split.
- apply/subvP=> _ /memv_imgP[v _ ->].
  exact: reynolds_mem_common.
- apply/subvP=> v hv.
  apply/memv_imgP; exists v; first exact: memvf.
  by rewrite reynolds_fix_common.
Qed.

(** Its fixed space is the same common invariant subspace. *)
Lemma reynolds_fixedSpace_eq_common_fixed :
  fixedSpace reynolds = common_fixed_space.
Proof.
apply/subv_anti/andP; split.
- apply/subvP=> v /fixedSpaceP hfix.
  have hmem := reynolds_mem_common v.
  by rewrite hfix in hmem.
- apply/subvP=> v hv.
  apply/fixedSpaceP.
  exact: reynolds_fix_common hv.
Qed.

(** Therefore image and fixed space agree. *)
Lemma reynolds_image_eq_fixedSpace :
  limg reynolds = fixedSpace reynolds.
Proof.
by rewrite reynolds_image_eq_common_fixed
  reynolds_fixedSpace_eq_common_fixed.
Qed.

(** A concrete finite tuple selected by MathComp as a basis of the Reynolds
    image.  The following theorems transport the same tuple to both equivalent
    presentations of the invariant space. *)
Definition reynolds_invariant_basis := vbasis (limg reynolds).

Lemma reynolds_invariant_basis_image :
  basis_of (limg reynolds) reynolds_invariant_basis.
Proof. exact: vbasisP (limg reynolds). Qed.

Lemma reynolds_invariant_basis_common :
  basis_of common_fixed_space reynolds_invariant_basis.
Proof.
by rewrite -reynolds_image_eq_common_fixed;
  exact: reynolds_invariant_basis_image.
Qed.

Lemma reynolds_invariant_basis_fixedSpace :
  basis_of (fixedSpace reynolds) reynolds_invariant_basis.
Proof.
by rewrite -reynolds_image_eq_fixedSpace;
  exact: reynolds_invariant_basis_image.
Qed.

End Reynolds.

End PolynomialFormulasLazardInvariantReynoldsFinite.
