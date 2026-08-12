From mathcomp Require Import all_ssreflect all_algebra.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A small finite-free-module interface for the Coq port of Lazard's
    invariant theorem.

    MathComp's bundled [basis_of]/[vbasis] API is deliberately specialized to
    finite-dimensional vector spaces over fields.  Lazard's ambient module is
    instead a module over a polynomial ring.  This file therefore records the
    exact finite-free data needed by the proof: a finite family, coordinates,
    reconstruction, and uniqueness.  The elementary coordinate laws below
    are derived from those two basis axioms rather than added as certificates.

    A graded refinement retains a degree for each basis vector, its
    homogeneity proof, and a visible uniform bound. *)
Module PolynomialFormulasLazardInvariantFiniteFree.

Import GRing.Theory.
Local Open Scope ring_scope.

Section FiniteFree.

Variables (R : ringType) (M : lmodType R).

Record finite_free_decomposition := FiniteFreeDecomposition {
  ffd_index : finType;
  ffd_basis : ffd_index -> M;
  ffd_coeff : M -> ffd_index -> R;
  ffd_reconstruct : forall x,
    x = \sum_i (ffd_coeff x i) *: ffd_basis i;
  ffd_unique : forall x (c : ffd_index -> R),
    x = \sum_i (c i) *: ffd_basis i ->
    forall i, c i = ffd_coeff x i
}.

Arguments ffd_index _ : clear implicits.
Arguments ffd_basis _ _ : clear implicits.
Arguments ffd_coeff _ _ _ : clear implicits.

Variable D : finite_free_decomposition.

Lemma ffd_coeff_unique x (c : ffd_index D -> R)
    (hc : x = \sum_i (c i) *: ffd_basis D i) i :
  c i = ffd_coeff D x i.
Proof. exact: ffd_unique hc i. Qed.

Lemma ffd_eq_of_coeff_eq x y
    (hxy : forall i, ffd_coeff D x i = ffd_coeff D y i) :
  x = y.
Proof.
rewrite (ffd_reconstruct D x) (ffd_reconstruct D y).
apply: eq_bigr => i _.
by rewrite hxy.
Qed.

Lemma ffd_coeff0 i : ffd_coeff D 0 i = 0.
Proof.
apply/esym.
apply: (ffd_coeff_unique (x := 0) (c := fun _ => 0)).
by rewrite big1 // => j _; rewrite scale0r.
Qed.

Lemma ffd_coeffD x y i :
  ffd_coeff D (x + y) i = ffd_coeff D x i + ffd_coeff D y i.
Proof.
apply/esym.
apply: (ffd_coeff_unique
  (c := fun j => ffd_coeff D x j + ffd_coeff D y j)).
under [RHS] eq_bigr => j _ do rewrite scalerDl.
by rewrite big_split -(ffd_reconstruct D x) -(ffd_reconstruct D y).
Qed.

Lemma ffd_coeffZ a x i :
  ffd_coeff D (a *: x) i = a * ffd_coeff D x i.
Proof.
apply/esym.
apply: (ffd_coeff_unique
  (c := fun j => a * ffd_coeff D x j)).
under [RHS] eq_bigr => j _ do rewrite -scalerA.
rewrite -scaler_sumr.
by rewrite -(ffd_reconstruct D x).
Qed.

(** Coordinates of a displayed basis vector are the Kronecker delta.
    This is derived from reconstruction uniqueness, rather than included
    as an additional field of [finite_free_decomposition]. *)
Lemma ffd_coeff_basis i j :
  ffd_coeff D (ffd_basis D j) i = (i == j)%:R.
Proof.
apply/esym.
apply: (ffd_coeff_unique
  (x := ffd_basis D j) (c := fun k => (k == j)%:R)).
rewrite (bigD1 j) //= eqxx scale1r.
rewrite big1 ?addr0 // => k hkj.
by rewrite (negbTE hkj) scale0r.
Qed.

Lemma ffd_coeff_basis_same i :
  ffd_coeff D (ffd_basis D i) i = 1.
Proof. by rewrite ffd_coeff_basis eqxx. Qed.

Lemma ffd_coeff_basis_other i j :
  i != j -> ffd_coeff D (ffd_basis D j) i = 0.
Proof. by move=> hij; rewrite ffd_coeff_basis (negbTE hij). Qed.

Definition ffd_coeff_fun i (x : M) := ffd_coeff D x i.

Fact ffd_coeff_is_linear i : scalar (ffd_coeff_fun i).
Proof.
move=> a x y.
by rewrite /ffd_coeff_fun ffd_coeffD ffd_coeffZ.
Qed.

HB.instance Definition ffd_coeff_isLinear i :=
  GRing.isLinear.Build R M R *%R (ffd_coeff_fun i)
    (ffd_coeff_is_linear i).

Definition ffd_coeff_linear i : {linear M -> R | *%R} :=
  [the {linear M -> R | *%R} of ffd_coeff_fun i].

Lemma ffd_coeff_linearE i x :
  ffd_coeff_linear i x = ffd_coeff D x i.
Proof. reflexivity. Qed.

Lemma ffd_coeff_sum (I : finType) (f : I -> M) i :
  ffd_coeff D (\sum_j f j) i = \sum_j ffd_coeff D (f j) i.
Proof.
change ((ffd_coeff_linear i) (\sum_j f j) =
  \sum_j (ffd_coeff_linear i) (f j)).
by rewrite linear_sum.
Qed.

Lemma ffd_coeffN x i :
  ffd_coeff D (- x) i = - ffd_coeff D x i.
Proof.
rewrite -scaleN1r ffd_coeffZ.
by rewrite mulN1r.
Qed.

Lemma ffd_coeffB x y i :
  ffd_coeff D (x - y) i = ffd_coeff D x i - ffd_coeff D y i.
Proof.
change (ffd_coeff D (x + (- y)) i =
  ffd_coeff D x i + (- ffd_coeff D y i)).
by rewrite ffd_coeffD ffd_coeffN.
Qed.

(** Coefficients vanish identically exactly for the zero vector. *)
Lemma ffd_coeff_eq0P x :
  (forall i, ffd_coeff D x i = 0) <-> x = 0.
Proof.
split=> [hx|->].
- apply: ffd_eq_of_coeff_eq => i.
  by rewrite hx ffd_coeff0.
- exact: ffd_coeff0.
Qed.

(** The chosen finite family is linearly independent in the precise
    coefficient-function sense needed by later matrix constructions. *)
Lemma ffd_basis_independent (c : ffd_index D -> R) :
  (\sum_i (c i) *: ffd_basis D i = 0) ->
  forall i, c i = 0.
Proof.
move=> hc i.
have hci := ffd_coeff_unique (x := 0) (c := c) (esym hc) i.
by rewrite ffd_coeff0 in hci.
Qed.

(** Conversely, every vector lies in the span of the displayed family. *)
Lemma ffd_basis_spans x :
  exists c : ffd_index D -> R,
    x = \sum_i (c i) *: ffd_basis D i.
Proof. by exists (ffd_coeff D x); exact: ffd_reconstruct. Qed.

End FiniteFree.

Arguments ffd_index {R M} _.
Arguments ffd_basis {R M} _ _.
Arguments ffd_coeff {R M} _ _ _.

Section GradedFiniteFree.

Variables (R : ringType) (M : lmodType R).
Variable homogeneous : M -> nat -> Prop.
Variable degree_bound : nat.

Record homogeneous_finite_free_decomposition :=
  HomogeneousFiniteFreeDecomposition {
    hffd_free : @finite_free_decomposition R M;
    hffd_degree : ffd_index hffd_free -> nat;
    hffd_basis_homogeneous : forall i,
      homogeneous (ffd_basis hffd_free i) (hffd_degree i);
    hffd_degree_le : forall i, (hffd_degree i <= degree_bound)%N
  }.

Arguments hffd_free _ : clear implicits.
Arguments hffd_degree _ _ : clear implicits.

Variable D : homogeneous_finite_free_decomposition.

Lemma hffd_basis_degree_bounded i :
  (hffd_degree D i <= degree_bound)%N.
Proof. exact: hffd_degree_le. Qed.

Lemma hffd_basis_is_homogeneous i :
  homogeneous (ffd_basis (hffd_free D) i) (hffd_degree D i).
Proof. exact: hffd_basis_homogeneous. Qed.

Lemma hffd_reconstruct x :
  x = \sum_i
    (ffd_coeff (hffd_free D) x i) *: ffd_basis (hffd_free D) i.
Proof. exact: ffd_reconstruct. Qed.

End GradedFiniteFree.

Arguments hffd_free {R M homogeneous degree_bound} _.
Arguments hffd_degree {R M homogeneous degree_bound} _ _.

End PolynomialFormulasLazardInvariantFiniteFree.
