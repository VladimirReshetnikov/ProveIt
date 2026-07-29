(**
  Semiterms over relational first-order languages.

  A relational language has no function symbols, so every semiterm is a
  bound or free variable.  This small interface packages that elimination
  principle, direct valuation, and its interaction with rewrites and de
  Bruijn bound shift.  All results are constructive.
*)

From Stdlib Require Import Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma semiterm_bvar_or_fvar_relational :
  forall L X n, language_relational L ->
  forall t : semiterm L X n,
    (exists i, t = Semiterm_bvar i) \/
    (exists x, t = Semiterm_fvar x).
Proof.
  intros L X n Hrel t.
  destruct t as [i | x | k f v].
  - left. now exists i.
  - right. now exists x.
  - exact (False_rect _ (Hrel k f)).
Qed.

Lemma term_fvar_relational :
  forall L X, language_relational L ->
  forall t : term L X, exists x, t = Semiterm_fvar x.
Proof.
  intros L X Hrel t.
  destruct (semiterm_bvar_or_fvar_relational Hrel t)
    as [[i Hi] | [x Hx]].
  - exact (Fin.case0 (fun _ => exists x, t = Semiterm_fvar x) i).
  - now exists x.
Qed.

Definition fin_cons {A n} (x : A) (v : Fin.t n -> A)
    (i : Fin.t (S n)) : A :=
  @Fin.caseS' n i (fun _ => A) x v.

Definition semiterm_relational_val {L X n M}
    (Hrel : language_relational L)
    (bv : Fin.t n -> M) (fv : X -> M)
    (t : semiterm L X n) : M :=
  match t with
  | Semiterm_bvar i => bv i
  | Semiterm_fvar x => fv x
  | @Semiterm_func _ _ _ k f _ => False_rect M (Hrel k f)
  end.

Lemma semiterm_relational_val_bvar :
  forall L X n M (Hrel : language_relational L)
    (bv : Fin.t n -> M) (fv : X -> M) i,
    semiterm_relational_val Hrel bv fv (Semiterm_bvar i) = bv i.
Proof. reflexivity. Qed.

Lemma semiterm_relational_val_fvar :
  forall L X n M (Hrel : language_relational L)
    (bv : Fin.t n -> M) (fv : X -> M) x,
    semiterm_relational_val Hrel bv fv (Semiterm_fvar x) = fv x.
Proof. reflexivity. Qed.

Lemma semiterm_relational_val_rew :
  forall L X n Y m M (Hrel : language_relational L)
    (bv : Fin.t m -> M) (fv : Y -> M)
    (w : rew L X n Y m) (t : semiterm L X n),
    semiterm_relational_val Hrel bv fv (rew_apply w t) =
    semiterm_relational_val Hrel
      (fun i => semiterm_relational_val Hrel bv fv
        (rew_apply w (Semiterm_bvar i)))
      (fun x => semiterm_relational_val Hrel bv fv
        (rew_apply w (Semiterm_fvar x))) t.
Proof.
  intros L X n Y m M Hrel bv fv w t.
  destruct t as [i | x | k f v]; try reflexivity.
  exact (False_rect _ (Hrel k f)).
Qed.

Lemma semiterm_relational_val_bshift :
  forall L X n M (Hrel : language_relational L)
    (x : M) (bv : Fin.t n -> M) (fv : X -> M)
    (t : semiterm L X n),
    semiterm_relational_val Hrel (fin_cons x bv) fv
      (rew_apply rew_bshift t) =
    semiterm_relational_val Hrel bv fv t.
Proof.
  intros L X n M Hrel x bv fv t.
  destruct t as [i | y | k f v]; reflexivity.
Qed.

Print Assumptions semiterm_bvar_or_fvar_relational.
Print Assumptions term_fvar_relational.
Print Assumptions semiterm_relational_val_rew.
Print Assumptions semiterm_relational_val_bshift.
