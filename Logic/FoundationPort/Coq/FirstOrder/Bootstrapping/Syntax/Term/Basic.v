(**
  Concrete codes and structural recognition for bootstrapped terms.

  This ports the constructor, [IsUTerm], [termBV], and [IsSemiterm]
  surface of
  [Foundation/FirstOrder/Bootstrapping/Syntax/Term/Basic.lean].  The Lean
  development obtains induction from an arithmetic least fixed point.  Coq
  can expose the same standard-natural relation directly as an inductive
  predicate.  A bound-variable policy parameter factors the untyped and
  bounded versions, so their cases and induction principles cannot drift.

  The codes deliberately agree definitionally with [semiterm_code] from the
  verified structural coding layer.  Foundation's representation-specific
  outer successor is unnecessary here: structural induction, rather than
  recursion on the numerical code, supplies well-foundedness.
*)

From Stdlib Require Import Arith.PeanoNat Cantor Lia Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic Require Import Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax Require Import Language.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Raw constructors *)

Definition boot_qq_bvar (z : nat) : nat :=
  Cantor.to_nat (0, z).

Definition boot_qq_fvar (x : nat) : nat :=
  Cantor.to_nat (1, x).

Definition boot_qq_func (k f args : nat) : nat :=
  Cantor.to_nat (2, Cantor.to_nat (k, Cantor.to_nat (f, args))).

(** Keep the pairing implementation abstract while decomposing codes. *)
Local Opaque Cantor.to_nat.

Lemma boot_qq_bvar_argument_le : forall z,
  z <= boot_qq_bvar z.
Proof.
  intro z. unfold boot_qq_bvar.
  pose proof (Cantor.to_nat_non_decreasing 0 z). lia.
Qed.

Lemma boot_qq_fvar_argument_le : forall x,
  x <= boot_qq_fvar x.
Proof.
  intro x. unfold boot_qq_fvar.
  pose proof (Cantor.to_nat_non_decreasing 1 x). lia.
Qed.

Lemma boot_qq_func_arity_le : forall k f args,
  k <= boot_qq_func k f args.
Proof.
  intros k f args. unfold boot_qq_func.
  pose proof (Cantor.to_nat_non_decreasing f args) as Hinner.
  pose proof (Cantor.to_nat_non_decreasing k (Cantor.to_nat (f, args)))
    as Hmiddle.
  pose proof (Cantor.to_nat_non_decreasing 2
    (Cantor.to_nat (k, Cantor.to_nat (f, args)))) as Houter.
  lia.
Qed.

Lemma boot_qq_func_symbol_le : forall k f args,
  f <= boot_qq_func k f args.
Proof.
  intros k f args. unfold boot_qq_func.
  pose proof (Cantor.to_nat_non_decreasing f args) as Hinner.
  pose proof (Cantor.to_nat_non_decreasing k (Cantor.to_nat (f, args)))
    as Hmiddle.
  pose proof (Cantor.to_nat_non_decreasing 2
    (Cantor.to_nat (k, Cantor.to_nat (f, args)))) as Houter.
  lia.
Qed.

Lemma boot_qq_func_arguments_le : forall k f args,
  args <= boot_qq_func k f args.
Proof.
  intros k f args. unfold boot_qq_func.
  pose proof (Cantor.to_nat_non_decreasing f args) as Hinner.
  pose proof (Cantor.to_nat_non_decreasing k (Cantor.to_nat (f, args)))
    as Hmiddle.
  pose proof (Cantor.to_nat_non_decreasing 2
    (Cantor.to_nat (k, Cantor.to_nat (f, args)))) as Houter.
  lia.
Qed.

Lemma boot_qq_func_component_le : forall k f (v : Fin.t k -> nat) i,
  v i <= boot_qq_func k f (fin_nat_code v).
Proof.
  intros k f v i.
  pose proof (fin_nat_code_component_le v i).
  pose proof (boot_qq_func_arguments_le k f (fin_nat_code v)). lia.
Qed.

Lemma boot_qq_bvar_injective : forall z w,
  boot_qq_bvar z = boot_qq_bvar w <-> z = w.
Proof.
  intros z w; split; [|now intros ->].
  unfold boot_qq_bvar. intro H. apply Cantor.to_nat_inj in H.
  now injection H.
Qed.

Lemma boot_qq_fvar_injective : forall x y,
  boot_qq_fvar x = boot_qq_fvar y <-> x = y.
Proof.
  intros x y; split; [|now intros ->].
  unfold boot_qq_fvar. intro H. apply Cantor.to_nat_inj in H.
  now injection H.
Qed.

Lemma boot_qq_func_injective : forall k f args l g rest,
  boot_qq_func k f args = boot_qq_func l g rest <->
  k = l /\ f = g /\ args = rest.
Proof.
  intros k f args l g rest; split.
  - unfold boot_qq_func. intro H.
    apply Cantor.to_nat_inj in H. injection H as Hpayload.
    apply Cantor.to_nat_inj in Hpayload. injection Hpayload as Hk Hinner.
    apply Cantor.to_nat_inj in Hinner. injection Hinner as Hf Hargs.
    now repeat split.
  - intros [-> [-> ->]]. reflexivity.
Qed.

Lemma boot_qq_bvar_fvar_disjoint : forall z x,
  boot_qq_bvar z <> boot_qq_fvar x.
Proof.
  intros z x H. unfold boot_qq_bvar, boot_qq_fvar in H.
  apply Cantor.to_nat_inj in H. discriminate H.
Qed.

Lemma boot_qq_bvar_func_disjoint : forall z k f args,
  boot_qq_bvar z <> boot_qq_func k f args.
Proof.
  intros z k f args H. unfold boot_qq_bvar, boot_qq_func in H.
  apply Cantor.to_nat_inj in H. discriminate H.
Qed.

Lemma boot_qq_fvar_func_disjoint : forall x k f args,
  boot_qq_fvar x <> boot_qq_func k f args.
Proof.
  intros x k f args H. unfold boot_qq_fvar, boot_qq_func in H.
  apply Cantor.to_nat_inj in H. discriminate H.
Qed.

(** The constructor equations are exact, not merely an isomorphism between
    two independently chosen code systems. *)
Lemma boot_qq_bvar_quote : forall L X n EL EX (i : Fin.t n),
  @semiterm_code L X n EL EX (Semiterm_bvar i) =
  boot_qq_bvar (fin_value i).
Proof. reflexivity. Qed.

Lemma boot_qq_fvar_quote : forall L X n EL EX (x : X),
  @semiterm_code L X n EL EX (Semiterm_fvar x) =
  boot_qq_fvar (encode EX x).
Proof. reflexivity. Qed.

Lemma boot_qq_func_quote : forall L X n EL EX k
    (f : language_func L k) (v : Fin.t k -> semiterm L X n),
  semiterm_code EL EX (Semiterm_func f v) =
  boot_qq_func k (boot_func_quote EL f)
    (fin_nat_code (fun i => semiterm_code EL EX (v i))).
Proof. reflexivity. Qed.

(** * One factored structural recognizer *)

Inductive boot_term_code {L : language} (EL : language_encodable L)
    (bound_ok : nat -> Prop) : nat -> Prop :=
| Boot_term_bvar : forall z,
    bound_ok z -> boot_term_code EL bound_ok (boot_qq_bvar z)
| Boot_term_fvar : forall x,
    boot_term_code EL bound_ok (boot_qq_fvar x)
| Boot_term_func : forall k f (v : Fin.t k -> nat),
    language_func_code_valid EL k f ->
    (forall i, boot_term_code EL bound_ok (v i)) ->
    boot_term_code EL bound_ok
      (boot_qq_func k f (fin_nat_code v)).

Definition boot_term_code_vec {L} (EL : language_encodable L)
    (bound_ok : nat -> Prop) k (v : Fin.t k -> nat) : Prop :=
  forall i, boot_term_code EL bound_ok (v i).

Definition boot_is_uterm {L} (EL : language_encodable L) : nat -> Prop :=
  boot_term_code EL (fun _ => True).

Definition boot_is_uterm_vec {L} (EL : language_encodable L)
    k (v : Fin.t k -> nat) : Prop :=
  boot_term_code_vec EL (fun _ => True) v.

Definition boot_is_semiterm {L} (EL : language_encodable L)
    (n : nat) : nat -> Prop :=
  boot_term_code EL (fun z => z < n).

Definition boot_is_semiterm_vec {L} (EL : language_encodable L)
    k n (v : Fin.t k -> nat) : Prop :=
  boot_term_code_vec EL (fun z => z < n) v.

Lemma boot_term_code_case_iff : forall L EL bound_ok t,
  @boot_term_code L EL bound_ok t <->
  (exists z, bound_ok z /\ t = boot_qq_bvar z) \/
  (exists x, t = boot_qq_fvar x) \/
  (exists k f (v : Fin.t k -> nat),
    language_func_code_valid EL k f /\
    boot_term_code_vec EL bound_ok v /\
    t = boot_qq_func k f (fin_nat_code v)).
Proof.
  intros L EL bound_ok t; split.
  - intro H. destruct H as [z Hz | x | k f v Hf Hv].
    + left. now exists z.
    + right; left. now exists x.
    + right; right. exists k, f, v. now repeat split.
  - intros [[z [Hz ->]] | [[x ->] |
      [k [f [v [Hf [Hv ->]]]]]]].
    + now apply Boot_term_bvar.
    + apply Boot_term_fvar.
    + now apply Boot_term_func.
Qed.

Lemma boot_term_code_bvar_iff : forall L EL bound_ok z,
  @boot_term_code L EL bound_ok (boot_qq_bvar z) <-> bound_ok z.
Proof.
  intros L EL bound_ok z. rewrite boot_term_code_case_iff.
  split.
  - intros [[w [Hw Hcode]] | [[x Hcode] |
      [k [f [v [_ [_ Hcode]]]]]]].
    + pose proof (proj1 (boot_qq_bvar_injective z w) Hcode) as Hzw.
      subst z. exact Hw.
    + exfalso. exact (@boot_qq_bvar_fvar_disjoint z x Hcode).
    + exfalso. exact (@boot_qq_bvar_func_disjoint z k f
        (fin_nat_code v) Hcode).
  - intro Hz. left. now exists z.
Qed.

Lemma boot_term_code_fvar : forall L EL bound_ok x,
  @boot_term_code L EL bound_ok (boot_qq_fvar x).
Proof. intros; apply Boot_term_fvar. Qed.

Lemma boot_term_code_func_iff : forall L EL bound_ok k f
    (v : Fin.t k -> nat),
  @boot_term_code L EL bound_ok
      (boot_qq_func k f (fin_nat_code v)) <->
  language_func_code_valid EL k f /\
  boot_term_code_vec EL bound_ok v.
Proof.
  intros L EL bound_ok k f v. rewrite boot_term_code_case_iff.
  split.
  - intros [[z [_ Hcode]] | [[x Hcode] |
      [l [g [w [Hg [Hw Hcode]]]]]]].
    + exfalso. apply (@boot_qq_bvar_func_disjoint z k f
        (fin_nat_code v)). symmetry. exact Hcode.
    + exfalso. apply (@boot_qq_fvar_func_disjoint x k f
        (fin_nat_code v)). symmetry. exact Hcode.
    + apply boot_qq_func_injective in Hcode.
      destruct Hcode as [Hlk [Hgf Hwv]].
      subst l. subst g. apply fin_nat_code_injective in Hwv. subst w.
      now split.
  - intros [Hf Hv]. right; right. exists k, f, v.
    now repeat split.
Qed.

Lemma boot_term_code_vec_empty : forall L EL bound_ok
    (v : Fin.t 0 -> nat),
  @boot_term_code_vec L EL bound_ok 0 v.
Proof. intros L EL bound_ok v i. inversion i. Qed.

Lemma boot_term_code_vec_cons_iff : forall L EL bound_ok k x
    (v : Fin.t k -> nat),
  @boot_term_code_vec L EL bound_ok (S k) (fin_coding_cons x v) <->
  boot_term_code EL bound_ok x /\ boot_term_code_vec EL bound_ok v.
Proof.
  intros L EL bound_ok k x v; split.
  - intro H. split.
    + exact (H Fin.F1).
    + intro i. exact (H (Fin.FS i)).
  - intros [Hx Hv] i.
    refine (@Fin.caseS' k i
      (fun j => boot_term_code EL bound_ok (fin_coding_cons x v j)) _ _).
    + exact Hx.
    + exact Hv.
Qed.

Lemma boot_term_code_vec_singleton_iff : forall L EL bound_ok x,
  @boot_term_code_vec L EL bound_ok 1
      (fin_coding_cons x (fun i : Fin.t 0 => match i with end)) <->
  boot_term_code EL bound_ok x.
Proof.
  intros. rewrite boot_term_code_vec_cons_iff. split.
  - tauto.
  - intro H; split; [exact H|apply boot_term_code_vec_empty].
Qed.

Lemma boot_term_code_vec_two_iff : forall L EL bound_ok x y,
  @boot_term_code_vec L EL bound_ok 2
      (fin_coding_cons x
        (fin_coding_cons y (fun i : Fin.t 0 => match i with end))) <->
  boot_term_code EL bound_ok x /\ boot_term_code EL bound_ok y.
Proof.
  intros. rewrite !boot_term_code_vec_cons_iff.
  split.
  - tauto.
  - intros [Hx Hy]. repeat split; try assumption.
    apply boot_term_code_vec_empty.
Qed.

Theorem boot_term_code_monotone : forall L EL B C,
  (forall z, B z -> C z) -> forall t,
  @boot_term_code L EL B t -> boot_term_code EL C t.
Proof.
  intros L EL B C HBC t H.
  induction H as [z Hz | x | k f v Hf Hv IH].
  - apply Boot_term_bvar. now apply HBC.
  - apply Boot_term_fvar.
  - apply Boot_term_func; [exact Hf|exact IH].
Qed.

Lemma boot_is_semiterm_is_uterm : forall L EL n t,
  @boot_is_semiterm L EL n t -> boot_is_uterm EL t.
Proof.
  intros L EL n t H. eapply boot_term_code_monotone; [|exact H].
  tauto.
Qed.

Lemma boot_is_semiterm_weaken : forall L EL n m t,
  n <= m -> @boot_is_semiterm L EL n t -> boot_is_semiterm EL m t.
Proof.
  intros L EL n m t Hnm H. unfold boot_is_semiterm in *.
  eapply (@boot_term_code_monotone L EL
    (fun z => z < n) (fun z => z < m)); [|exact H].
  intros z Hz. lia.
Qed.

(** Source-shaped public cases.  The generic policy theorem above is the
    shared proof; these specializations are convenient downstream APIs. *)
Lemma boot_is_uterm_case_iff : forall L EL t,
  @boot_is_uterm L EL t <->
  (exists z, t = boot_qq_bvar z) \/
  (exists x, t = boot_qq_fvar x) \/
  (exists k f (v : Fin.t k -> nat),
    language_func_code_valid EL k f /\
    boot_is_uterm_vec EL v /\
    t = boot_qq_func k f (fin_nat_code v)).
Proof.
  intros L EL t. unfold boot_is_uterm, boot_is_uterm_vec.
  rewrite boot_term_code_case_iff. split.
  - intros [[z [_ Hz]] | H]; [now left; exists z|now right].
  - intros [[z Hz] | H].
    + left. exists z. now split.
    + right. exact H.
Qed.

Lemma boot_is_uterm_bvar : forall L EL z,
  @boot_is_uterm L EL (boot_qq_bvar z).
Proof.
  intros. unfold boot_is_uterm. apply Boot_term_bvar. exact I.
Qed.

Lemma boot_is_uterm_fvar : forall L EL x,
  @boot_is_uterm L EL (boot_qq_fvar x).
Proof. intros. unfold boot_is_uterm. apply Boot_term_fvar. Qed.

Lemma boot_is_uterm_func_iff : forall L EL k f (v : Fin.t k -> nat),
  @boot_is_uterm L EL (boot_qq_func k f (fin_nat_code v)) <->
  language_func_code_valid EL k f /\ boot_is_uterm_vec EL v.
Proof.
  intros. unfold boot_is_uterm, boot_is_uterm_vec.
  apply boot_term_code_func_iff.
Qed.

Lemma boot_is_semiterm_case_iff : forall L EL n t,
  @boot_is_semiterm L EL n t <->
  (exists z, z < n /\ t = boot_qq_bvar z) \/
  (exists x, t = boot_qq_fvar x) \/
  (exists k f (v : Fin.t k -> nat),
    language_func_code_valid EL k f /\
    boot_is_semiterm_vec EL n v /\
    t = boot_qq_func k f (fin_nat_code v)).
Proof.
  intros L EL n t. unfold boot_is_semiterm, boot_is_semiterm_vec.
  apply boot_term_code_case_iff.
Qed.

Lemma boot_is_semiterm_bvar_iff : forall L EL n z,
  @boot_is_semiterm L EL n (boot_qq_bvar z) <-> z < n.
Proof.
  intros L EL n z. unfold boot_is_semiterm.
  apply (@boot_term_code_bvar_iff L EL (fun q => q < n) z).
Qed.

Lemma boot_is_semiterm_fvar : forall L EL n x,
  @boot_is_semiterm L EL n (boot_qq_fvar x).
Proof. intros. unfold boot_is_semiterm. apply Boot_term_fvar. Qed.

Lemma boot_is_semiterm_func_iff : forall L EL n k f
    (v : Fin.t k -> nat),
  @boot_is_semiterm L EL n (boot_qq_func k f (fin_nat_code v)) <->
  language_func_code_valid EL k f /\ boot_is_semiterm_vec EL n v.
Proof.
  intros L EL n k f v. unfold boot_is_semiterm, boot_is_semiterm_vec.
  apply (@boot_term_code_func_iff L EL (fun z => z < n) k f v).
Qed.

Theorem boot_term_code_induction : forall L EL bound_ok (P : nat -> Prop),
  (forall z, bound_ok z -> P (boot_qq_bvar z)) ->
  (forall x, P (boot_qq_fvar x)) ->
  (forall k f (v : Fin.t k -> nat),
    language_func_code_valid EL k f ->
    boot_term_code_vec EL bound_ok v ->
    (forall i, P (v i)) ->
    P (boot_qq_func k f (fin_nat_code v))) ->
  forall t, @boot_term_code L EL bound_ok t -> P t.
Proof.
  intros L EL bound_ok P Hb Hx Hfunc t H.
  induction H as [z Hz | x | k f v Hf Hv IH].
  - now apply Hb.
  - apply Hx.
  - now apply Hfunc.
Qed.

Theorem boot_is_uterm_induction : forall L EL (P : nat -> Prop),
  (forall z, P (boot_qq_bvar z)) ->
  (forall x, P (boot_qq_fvar x)) ->
  (forall k f (v : Fin.t k -> nat),
    language_func_code_valid EL k f ->
    boot_is_uterm_vec EL v ->
    (forall i, P (v i)) ->
    P (boot_qq_func k f (fin_nat_code v))) ->
  forall t, @boot_is_uterm L EL t -> P t.
Proof.
  intros L EL P Hb Hx Hfunc t H.
  unfold boot_is_uterm in H.
  exact (@boot_term_code_induction L EL (fun _ => True) P
    (fun z _ => Hb z) Hx Hfunc t H).
Qed.

Theorem boot_is_semiterm_induction : forall L EL n (P : nat -> Prop),
  (forall z, z < n -> P (boot_qq_bvar z)) ->
  (forall x, P (boot_qq_fvar x)) ->
  (forall k f (v : Fin.t k -> nat),
    language_func_code_valid EL k f ->
    boot_is_semiterm_vec EL n v ->
    (forall i, P (v i)) ->
    P (boot_qq_func k f (fin_nat_code v))) ->
  forall t, @boot_is_semiterm L EL n t -> P t.
Proof.
  intros L EL n P Hb Hx Hfunc t H.
  unfold boot_is_semiterm in H.
  exact (@boot_term_code_induction L EL (fun z => z < n) P
    Hb Hx Hfunc t H).
Qed.

(** * Exact connection to typed syntax *)

Theorem semiterm_code_policy_iff : forall L X n EL EX
    (bound_ok : nat -> Prop) (t : semiterm L X n),
  boot_term_code EL bound_ok (semiterm_code EL EX t) <->
  forall i, semiterm_bound_occurs i t -> bound_ok (fin_value i).
Proof.
  intros L X n EL EX bound_ok t.
  induction t as [i | x | k f v IH].
  - rewrite boot_qq_bvar_quote, boot_term_code_bvar_iff.
    split.
    + intros Hi j Hj. simpl in Hj. now subst j.
    + intro H. apply (H i). reflexivity.
  - rewrite boot_qq_fvar_quote.
    split.
    + intros _ i Hi. contradiction.
    + intros _. apply boot_term_code_fvar.
  - rewrite boot_qq_func_quote, boot_term_code_func_iff.
    split.
    + intros [_ Hv] i [j Hij].
      apply (proj1 (IH j)); [apply Hv|exact Hij].
    + intro H. split.
      * exists f. reflexivity.
      * intro j. apply (proj2 (IH j)). intros i Hi.
        apply H. now exists j.
Qed.

Theorem semiterm_code_is_uterm : forall L X n EL EX
    (t : semiterm L X n),
  boot_is_uterm EL (semiterm_code EL EX t).
Proof.
  intros L X n EL EX t. unfold boot_is_uterm.
  apply (proj2 (@semiterm_code_policy_iff L X n EL EX
    (fun _ => True) t)).
  tauto.
Qed.

Theorem semiterm_code_is_semiterm : forall L X n EL EX
    (t : semiterm L X n),
  boot_is_semiterm EL n (semiterm_code EL EX t).
Proof.
  intros L X n EL EX t. unfold boot_is_semiterm.
  apply (proj2 (@semiterm_code_policy_iff L X n EL EX
    (fun z => z < n) t)).
  intros i _. exact (proj2_sig (Fin.to_nat i)).
Qed.

(** Identity coding gives a canonical typed representative for every valid
    bounded raw code.  This is the converse of the quotation theorem and is
    stronger than mere closure of quotations. *)
Definition boot_nat_encoding : encoding nat :=
  {| encode := fun x => x;
     decode := fun x => Some x;
     decode_encode := fun _ => eq_refl |}.

Theorem boot_is_semiterm_has_quote : forall L EL n code,
  @boot_is_semiterm L EL n code ->
  exists t : semiterm L nat n,
    semiterm_code EL boot_nat_encoding t = code.
Proof.
  intros L EL n code H. unfold boot_is_semiterm in H.
  induction H as [z Hz | x | k fcode v Hvalid Hv IH].
  - exists (Semiterm_bvar (Fin.of_nat_lt Hz)).
    rewrite boot_qq_bvar_quote. unfold fin_value.
    now rewrite Fin.to_nat_of_nat.
  - exists (Semiterm_fvar x). reflexivity.
  - destruct Hvalid as [f Hf].
    destruct (@fin_forall_exists_choice k (semiterm L nat n)
      (fun i t => semiterm_code EL boot_nat_encoding t = v i) IH)
      as [terms Hterms].
    exists (Semiterm_func f terms). rewrite boot_qq_func_quote.
    unfold boot_func_quote. rewrite Hf. f_equal.
    f_equal. apply functional_extensionality. intro i.
    apply Hterms.
Qed.

Theorem boot_is_semiterm_quote_iff : forall L EL n code,
  @boot_is_semiterm L EL n code <->
  exists t : semiterm L nat n,
    semiterm_code EL boot_nat_encoding t = code.
Proof.
  intros L EL n code; split.
  - apply boot_is_semiterm_has_quote.
  - intros [t <-]. apply semiterm_code_is_semiterm.
Qed.

(** * Bound-variable calculation *)

Fixpoint boot_semiterm_bv {L X n} (t : semiterm L X n) : nat :=
  match t with
  | Semiterm_bvar i => S (fin_value i)
  | Semiterm_fvar _ => 0
  | @Semiterm_func _ _ _ k _ v =>
      @fin_max k (fun i => boot_semiterm_bv (v i))
  end.

Definition boot_semiterm_bv_vec {L X n k}
    (v : Fin.t k -> semiterm L X n) : Fin.t k -> nat :=
  fun i => boot_semiterm_bv (v i).

Lemma boot_semiterm_bv_bvar : forall L X n (i : Fin.t n),
  boot_semiterm_bv (@Semiterm_bvar L X n i) = S (fin_value i).
Proof. reflexivity. Qed.

Lemma boot_semiterm_bv_fvar : forall L X n (x : X),
  boot_semiterm_bv (@Semiterm_fvar L X n x) = 0.
Proof. reflexivity. Qed.

Lemma boot_semiterm_bv_func : forall L X n k
    (f : language_func L k) (v : Fin.t k -> semiterm L X n),
  boot_semiterm_bv (Semiterm_func f v) =
  @fin_max k (boot_semiterm_bv_vec v).
Proof. reflexivity. Qed.

Lemma boot_fin_max_le_iff : forall k (v : Fin.t k -> nat) n,
  @fin_max k v <= n <-> forall i, v i <= n.
Proof.
  induction k as [|k IH]; intros v n; split.
  - intros H i; inversion i.
  - intro H. simpl. lia.
  - intros H i. eapply Nat.le_trans; [apply fin_le_max|exact H].
  - intro H. simpl. apply Nat.max_lub.
    + apply H.
    + apply (proj2 (IH (fun i => v (Fin.FS i)) n)). intro i. apply H.
Qed.

Lemma boot_semiterm_bv_component_le : forall L X n k
    (f : language_func L k) (v : Fin.t k -> semiterm L X n) i,
  boot_semiterm_bv (v i) <= boot_semiterm_bv (Semiterm_func f v).
Proof.
  intros L X n k f v i. rewrite boot_semiterm_bv_func.
  change (boot_semiterm_bv_vec v i <=
    @fin_max k (boot_semiterm_bv_vec v)).
  apply fin_le_max.
Qed.

Theorem boot_semiterm_bv_le_iff : forall L X n
    (t : semiterm L X n) m,
  boot_semiterm_bv t <= m <->
  forall i, semiterm_bound_occurs i t -> fin_value i < m.
Proof.
  intros L X n t. induction t as [i | x | k f v IH]; intro m.
  - cbn [boot_semiterm_bv]. split.
    + intros H j Hj. pose proof (f_equal fin_value Hj). lia.
    + intro H. specialize (H i eq_refl). lia.
  - cbn [boot_semiterm_bv]. split.
    + intros H i Hi. contradiction.
    + intros H. lia.
  - rewrite boot_semiterm_bv_func, boot_fin_max_le_iff. split.
    + intros H i [j Hij]. apply (proj1 (IH j m)); [apply H|exact Hij].
    + intros H j. apply (proj2 (IH j m)). intros i Hi.
      apply H. now exists j.
Qed.

Theorem semiterm_code_is_semiterm_iff_bv : forall L X n EL EX
    (t : semiterm L X n) m,
  boot_is_semiterm EL m (semiterm_code EL EX t) <->
  boot_semiterm_bv t <= m.
Proof.
  intros L X n EL EX t m. unfold boot_is_semiterm.
  rewrite (@semiterm_code_policy_iff L X n EL EX
    (fun z => z < m) t).
  symmetry. apply boot_semiterm_bv_le_iff.
Qed.
