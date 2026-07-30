(**
  Predicate-valued modal logics, their normal and quasinormal sums, and
  global consequence.

  This file is an independent Coq port of the mathematical theorem surfaces
  in the pinned Foundation modules

    - Modal/Logic/Basic.lean,
    - Modal/Logic/SumNormal.lean,
    - Modal/Logic/SumQuasiNormal.lean, and
    - Modal/Logic/Global.lean.

  Lean's Set and Finset wrappers are represented by predicates and lists.
  In particular, finite witnesses are extensional lists: multiplicity and
  order are immaterial to every theorem below.  The file deliberately does
  not import [Boxdot], so the genuine global-consequence theorem can later be
  used by that layer without creating an import cycle.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Filtration CanonicalK NormalHilbert.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Basic predicate-valued logics *)

Definition modal_logic_set (AtomType : Type) : Type :=
  formula AtomType -> Prop.

Definition logic_subset {AtomType}
    (L M : modal_logic_set AtomType) : Prop :=
  forall p, L p -> M p.

Definition logic_equiv {AtomType}
    (L M : modal_logic_set AtomType) : Prop :=
  logic_subset L M /\ logic_subset M L.

Definition logic_strictly_weaker {AtomType}
    (L M : modal_logic_set AtomType) : Prop :=
  logic_subset L M /\ exists p, M p /\ ~ L p.

Definition logic_empty {AtomType} : modal_logic_set AtomType :=
  fun _ => False.

Definition logic_full {AtomType} : modal_logic_set AtomType :=
  fun _ => True.

Definition logic_union {AtomType}
    (L M : modal_logic_set AtomType) : modal_logic_set AtomType :=
  fun p => L p \/ M p.

Lemma logic_iff_provable :
  forall (AtomType : Type) (L : modal_logic_set AtomType) p,
    L p <-> L p.
Proof. reflexivity. Qed.

Lemma logic_iff_unprovable :
  forall (AtomType : Type) (L : modal_logic_set AtomType) p,
    ~ L p <-> ~ L p.
Proof. reflexivity. Qed.

Lemma logic_equiv_iff_pointwise :
  forall (AtomType : Type) (L M : modal_logic_set AtomType),
    logic_equiv L M <-> forall p, L p <-> M p.
Proof. firstorder. Qed.

Lemma logic_eq_iff_equiv :
  forall (AtomType : Type) (L M : modal_logic_set AtomType),
    L = M <-> logic_equiv L M.
Proof.
  intros AtomType L M; split.
  - intros ->; firstorder.
  - intros [HLM HML].
    apply functional_extensionality; intro p.
    apply propositional_extensionality; firstorder.
Qed.

Lemma logic_weaker_of_provable :
  forall (AtomType : Type) (L M : modal_logic_set AtomType),
    (forall p, L p -> M p) -> logic_subset L M.
Proof. firstorder. Qed.

Lemma logic_weaker_of_subset :
  forall (AtomType : Type) (L M : modal_logic_set AtomType),
    logic_subset L M -> logic_subset L M.
Proof. firstorder. Qed.

Lemma logic_equiv_of_provable :
  forall (AtomType : Type) (L M : modal_logic_set AtomType),
    (forall p, L p <-> M p) -> logic_equiv L M.
Proof. firstorder. Qed.

Lemma logic_strictly_weaker_of_proper_subset :
  forall (AtomType : Type) (L M : modal_logic_set AtomType),
    logic_subset L M ->
    (exists p, M p /\ ~ L p) ->
    logic_strictly_weaker L M.
Proof. firstorder. Qed.

Lemma logic_subset_of_weaker :
  forall (AtomType : Type) (L M : modal_logic_set AtomType),
    logic_subset L M -> logic_subset L M.
Proof. firstorder. Qed.

Lemma logic_empty_weaker :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    logic_subset logic_empty L.
Proof. firstorder. Qed.

Lemma logic_weaker_full :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    logic_subset L logic_full.
Proof. firstorder. Qed.

Lemma logic_union_comm :
  forall (AtomType : Type) (L M : modal_logic_set AtomType),
    logic_union L M = logic_union M L.
Proof.
  intros AtomType L M; apply functional_extensionality; intro p.
  apply propositional_extensionality; unfold logic_union; tauto.
Qed.

Lemma logic_union_idempotent :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    logic_union L L = L.
Proof.
  intros AtomType L; apply functional_extensionality; intro p.
  apply propositional_extensionality; unfold logic_union; tauto.
Qed.

(** Foundation's [Entailment.Cl] is represented extensionally: boxes are
    treated as propositional letters when evaluating a classical tautology. *)
Fixpoint classical_eval {AtomType}
    (rho : formula AtomType -> Prop) (p : formula AtomType) : Prop :=
  match p with
  | Atom _ => rho p
  | Bottom => False
  | Imp q r => classical_eval rho q -> classical_eval rho r
  | Box _ => rho p
  end.

Definition classical_tautology {AtomType} (p : formula AtomType) : Prop :=
  forall rho, classical_eval rho p.

Record classical_logic {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  logic_classical_tautology : forall p, classical_tautology p -> L p;
  logic_modus_ponens : forall p q, L (Imp p q) -> L p -> L q
}.

Definition logic_substitution_closed {AtomType}
    (L : modal_logic_set AtomType) : Prop :=
  forall (sigma : AtomType -> formula AtomType) p,
    L p -> L (substitute sigma p).

Record quasi_normal_logic {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  quasi_classical : classical_logic L;
  quasi_modal_K : forall p q, L (K p q);
  quasi_dia_duality : forall p, L (DiaDuality p);
  quasi_substitution : logic_substitution_closed L
}.

Record normal_logic {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  normal_quasi : quasi_normal_logic L;
  normal_nec : forall p, L p -> L (Box p)
}.

Lemma classical_eval_satisfies :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         w (p : formula AtomType),
    classical_eval (fun q => satisfies F V w q) p <->
    satisfies F V w p.
Proof.
  intros AtomType F V w p; induction p; simpl; try reflexivity.
  now rewrite IHp1, IHp2.
Qed.

Lemma classical_tautology_valid :
  forall (p : formula nat),
    classical_tautology p -> valid_on_all_frames p.
Proof.
  intros p Htaut F V w.
  apply (proj1 (@classical_eval_satisfies nat F V w p)).
  apply Htaut.
Qed.

Lemma normal_proves_logic_is_normal :
  forall Ax,
    schema_substitution_closed Ax ->
    normal_logic (@normal_proves Ax nat).
Proof.
  intros Ax Hclosed; constructor.
  - constructor.
    + constructor.
      * intros p Htaut.
        apply K_proves_normal, K_complete.
        now apply classical_tautology_valid.
      * intros p q; apply Np_mp.
    + intros p q; apply Np_modal_K.
    + intro p.
      apply K_proves_normal, K_complete, classical_tautology_valid.
      intro rho; unfold DiaDuality, Iff, And, Dia, Neg; simpl; tauto.
    + intros sigma p Hp.
      now apply normal_proves_substitute.
  - intros p; apply Np_nec.
Qed.

Lemma normal_logic_contains_K :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall p, K_proves p -> L p.
Proof.
  intros AtomType L Hnormal p Hp; induction Hp.
  - apply (logic_classical_tautology (quasi_classical (normal_quasi Hnormal))).
    intro rho; simpl; tauto.
  - apply (logic_classical_tautology (quasi_classical (normal_quasi Hnormal))).
    intro rho; simpl; tauto.
  - apply (logic_classical_tautology (quasi_classical (normal_quasi Hnormal))).
    intro rho; unfold Hilbert_elim_contra, Neg; simpl; tauto.
  - now apply (quasi_modal_K (normal_quasi Hnormal)).
  - eapply (logic_modus_ponens (quasi_classical (normal_quasi Hnormal)));
      eauto.
  - now apply (normal_nec Hnormal).
Qed.

Lemma normal_provable_of_K_provable :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall p, K_proves p -> L p.
Proof. exact normal_logic_contains_K. Qed.

Lemma logic_identity :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p, L (Imp p p).
Proof.
  intros AtomType L Hclass p.
  apply (logic_classical_tautology Hclass); intro rho; simpl; tauto.
Qed.

Lemma logic_imply_intro :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q, L q -> L (Imp p q).
Proof.
  intros AtomType L Hclass p q Hq.
  eapply (logic_modus_ponens Hclass); [|exact Hq].
  apply (logic_classical_tautology Hclass); intro rho; simpl; tauto.
Qed.

Lemma logic_imp_trans :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q r,
    L (Imp p q) -> L (Imp q r) -> L (Imp p r).
Proof.
  intros AtomType L Hclass p q r Hpq Hqr.
  eapply (logic_modus_ponens Hclass); [|exact Hqr].
  eapply (logic_modus_ponens Hclass); [|exact Hpq].
  apply (logic_classical_tautology Hclass); intro rho; simpl; tauto.
Qed.

Lemma logic_under_mp :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall a p q,
    L (Imp a (Imp p q)) -> L (Imp a p) -> L (Imp a q).
Proof.
  intros AtomType L Hclass a p q Hpq Hp.
  eapply (logic_modus_ponens Hclass); [|exact Hp].
  eapply (logic_modus_ponens Hclass); [|exact Hpq].
  apply (logic_classical_tautology Hclass); intro rho; simpl; tauto.
Qed.

Lemma logic_imp_and_intro :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall a p q,
    L (Imp a p) -> L (Imp a q) -> L (Imp a (And p q)).
Proof.
  intros AtomType L Hclass a p q Hp Hq.
  eapply (logic_modus_ponens Hclass); [|exact Hq].
  eapply (logic_modus_ponens Hclass); [|exact Hp].
  apply (logic_classical_tautology Hclass).
  intro rho; unfold And, Neg; simpl; tauto.
Qed.

Lemma logic_and_intro :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q,
    L p -> L q -> L (And p q).
Proof.
  intros AtomType L Hclass p q Hp Hq.
  eapply (logic_modus_ponens Hclass); [|exact Hq].
  eapply (logic_modus_ponens Hclass); [|exact Hp].
  apply (logic_classical_tautology Hclass).
  intro rho; unfold And, Neg; simpl; tauto.
Qed.

Lemma logic_mem_top :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> L Top.
Proof.
  intros AtomType L Hclass.
  apply (logic_classical_tautology Hclass).
  intro rho; unfold Top, Neg; simpl; tauto.
Qed.

Definition logic_inconsistent {AtomType}
    (L : modal_logic_set AtomType) : Prop :=
  forall p, L p.

(** This matches Foundation's generic notion: a logic is consistent when it
    does not prove every formula.  For a classical logic this is equivalent
    to the familiar specialization [~ L Bottom], proved below. *)
Definition logic_consistent {AtomType}
    (L : modal_logic_set AtomType) : Prop := ~ logic_inconsistent L.

Lemma logic_consistent_iff_exists_unprovable :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    logic_consistent L <-> exists p, ~ L p.
Proof.
  intros AtomType L; unfold logic_consistent, logic_inconsistent; split.
  - intro Hconsistent.
    destruct (classic (exists p, ~ L p)) as [Hex | Hnone]; [exact Hex |].
    exfalso; apply Hconsistent; intro p.
    apply NNPP; intro Hnot.
    apply Hnone; now exists p.
  - intros [p Hp] Hall; exact (Hp (Hall p)).
Qed.

Lemma logic_exists_unprovable :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    logic_consistent L -> exists p, ~ L p.
Proof.
  intros AtomType L H.
  now apply logic_consistent_iff_exists_unprovable.
Qed.

Lemma logic_no_bot :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> logic_consistent L -> ~ L Bottom.
Proof.
  intros AtomType L Hclass Hconsistent Hbot.
  apply Hconsistent; intro p.
  eapply (logic_modus_ponens Hclass); [|exact Hbot].
  apply (logic_classical_tautology Hclass); intro rho; simpl; tauto.
Qed.

Lemma logic_not_mem_bot :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> logic_consistent L -> ~ L Bottom.
Proof. exact logic_no_bot. Qed.

Lemma logic_not_neg_of :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> logic_consistent L ->
    forall p, L p -> ~ L (Neg p).
Proof.
  intros AtomType L Hclass Hconsistent p Hp Hneg.
  apply (logic_no_bot Hclass Hconsistent).
  exact (logic_modus_ponens Hclass Hneg Hp).
Qed.

Lemma logic_empty_strictly_weaker :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> logic_strictly_weaker logic_empty L.
Proof.
  intros AtomType L Hclass; split; [apply logic_empty_weaker |].
  exists Top; split; [now apply logic_mem_top | firstorder].
Qed.

Lemma logic_strictly_weaker_full :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    logic_consistent L -> logic_strictly_weaker L logic_full.
Proof.
  intros AtomType L Hconsistent; split; [apply logic_weaker_full |].
  destruct (logic_exists_unprovable Hconsistent) as [p Hp].
  exists p; split; [constructor | exact Hp].
Qed.

(** * Finite conjunction and substitution *)

Fixpoint logic_list_conj {AtomType}
    (Gamma : list (formula AtomType)) : formula AtomType :=
  match Gamma with
  | [] => Top
  | p :: rest => And p (logic_list_conj rest)
  end.

(** Foundation's [List.conj2] removes the trailing top from singleton lists.
    Keeping this exact presentation beside [logic_list_conj] lets the global
    development use the structurally convenient version while exposing a
    formally equivalent source-facing API. *)
Fixpoint logic_list_conj2 {AtomType}
    (Gamma : list (formula AtomType)) : formula AtomType :=
  match Gamma with
  | [] => Top
  | p :: rest =>
      match rest with
      | [] => p
      | _ => And p (logic_list_conj2 rest)
      end
  end.

(** The singleton-normalized finite disjunction dual to
    [logic_list_conj2].  Empty and singleton enumerations avoid a redundant
    trailing bottom, matching Foundation's [List.disj2]. *)
Fixpoint logic_list_disj2 {AtomType}
    (Gamma : list (formula AtomType)) : formula AtomType :=
  match Gamma with
  | [] => Bottom
  | p :: rest =>
      match rest with
      | [] => p
      | _ => Or p (logic_list_disj2 rest)
      end
  end.

Lemma substitute_logic_list_conj :
  forall (A B : Type) (sigma : A -> formula B) Gamma,
    substitute sigma (logic_list_conj Gamma) =
    logic_list_conj (map (substitute sigma) Gamma).
Proof.
  intros A B sigma Gamma; induction Gamma as [|p Gamma IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma substitute_logic_list_conj2 :
  forall (A B : Type) (sigma : A -> formula B) Gamma,
    substitute sigma (logic_list_conj2 Gamma) =
    logic_list_conj2 (map (substitute sigma) Gamma).
Proof.
  intros A B sigma Gamma; induction Gamma as [|p Gamma IH]; simpl.
  - reflexivity.
  - destruct Gamma as [|q Gamma]; simpl in *; [reflexivity |].
    now rewrite IH.
Qed.

Lemma logic_lconj_subst :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L ->
    forall (sigma : AtomType -> formula AtomType) Gamma,
      L (Imp (logic_list_conj (map (substitute sigma) Gamma))
             (substitute sigma (logic_list_conj Gamma))).
Proof.
  intros AtomType L Hclass sigma Gamma.
  rewrite substitute_logic_list_conj.
  apply logic_identity; exact Hclass.
Qed.

Lemma logic_lconj2_subst :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L ->
    forall (sigma : AtomType -> formula AtomType) Gamma,
      L (Imp (logic_list_conj2 (map (substitute sigma) Gamma))
             (substitute sigma (logic_list_conj2 Gamma))).
Proof.
  intros AtomType L Hclass sigma Gamma.
  rewrite substitute_logic_list_conj2.
  apply logic_identity; exact Hclass.
Qed.

Definition logic_fconj_subst := logic_lconj2_subst.

Lemma classical_eval_list_conj :
  forall (AtomType : Type) (rho : formula AtomType -> Prop) Gamma,
    classical_eval rho (logic_list_conj Gamma) <->
    Forall (classical_eval rho) Gamma.
Proof.
  intros AtomType rho Gamma; induction Gamma as [|p Gamma IH]; simpl.
  - unfold Top, Neg; simpl; split.
    + intros _; constructor.
    + intros _ Hfalse; exact Hfalse.
  - unfold And, Neg; simpl. rewrite IH.
    rewrite Forall_cons_iff.
    change (((classical_eval rho p ->
              Forall (classical_eval rho) Gamma -> False) -> False) <->
            classical_eval rho p /\ Forall (classical_eval rho) Gamma).
    split.
    + intro Hnot; split.
      * apply NNPP; intro Hnp.
        apply Hnot; intros Hp; contradiction.
      * apply NNPP; intro HnGamma.
        apply Hnot; intros _; exact HnGamma.
    + intros [Hp HGamma] Himp.
      exact (Himp Hp HGamma).
Qed.

Lemma classical_eval_list_conj2 :
  forall (AtomType : Type) (rho : formula AtomType -> Prop) Gamma,
    classical_eval rho (logic_list_conj2 Gamma) <->
    Forall (classical_eval rho) Gamma.
Proof.
  intros AtomType rho Gamma; induction Gamma as [|p Gamma IH]; simpl.
  - unfold Top, Neg; simpl; split.
    + intros _; constructor.
    + intros _ Hfalse; exact Hfalse.
  - destruct Gamma as [|q Gamma].
    + simpl; split.
      * intro Hp; constructor; [exact Hp | constructor].
      * intro Hforall; inversion Hforall; assumption.
    + simpl in IH |- *.
      unfold And, Neg; simpl. rewrite IH.
      rewrite !Forall_cons_iff.
      split.
      * intro Hnot; split.
        -- apply NNPP; intro Hnp.
           apply Hnot; intros Hp; contradiction.
        -- apply NNPP; intro Hnrest.
           apply Hnot; intros _; exact Hnrest.
      * intros [Hp Hrest] Himp.
        exact (Himp Hp Hrest).
Qed.

Lemma classical_eval_list_disj2 :
  forall (AtomType : Type) (rho : formula AtomType -> Prop) Gamma,
    classical_eval rho (logic_list_disj2 Gamma) <->
    Exists (classical_eval rho) Gamma.
Proof.
  intros AtomType rho Gamma; induction Gamma as [|p Gamma IH]; simpl.
  - split; [contradiction | intro H; inversion H].
  - destruct Gamma as [|q Gamma].
    + simpl; split.
      * intro Hp; now constructor.
      * intro H; inversion H as [x l Hp | x l Hnone]; subst.
        -- exact Hp.
        -- inversion Hnone.
    + simpl in IH |- *.
      unfold Or, Neg; simpl. rewrite IH.
      split.
      * intro Hor. destruct (classic (classical_eval rho p)) as [Hp | Hnp].
        -- now constructor.
        -- right. apply Hor. exact Hnp.
      * intros Hex Hnp. inversion Hex; subst; [contradiction | assumption].
Qed.

Lemma logic_list_conj_to_conj2 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma,
    L (Imp (logic_list_conj Gamma) (logic_list_conj2 Gamma)).
Proof.
  intros AtomType L Hclass Gamma.
  apply (logic_classical_tautology Hclass); intro rho; simpl.
  rewrite classical_eval_list_conj, classical_eval_list_conj2; tauto.
Qed.

Lemma logic_list_conj2_to_conj :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma,
    L (Imp (logic_list_conj2 Gamma) (logic_list_conj Gamma)).
Proof.
  intros AtomType L Hclass Gamma.
  apply (logic_classical_tautology Hclass); intro rho; simpl.
  rewrite classical_eval_list_conj, classical_eval_list_conj2; tauto.
Qed.

Lemma logic_list_conj_equivalence :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma,
    L (Iff (logic_list_conj Gamma) (logic_list_conj2 Gamma)).
Proof.
  intros AtomType L Hclass Gamma.
  unfold Iff.
  eapply logic_and_intro.
  - exact Hclass.
  - now apply logic_list_conj_to_conj2.
  - now apply logic_list_conj2_to_conj.
Qed.

Lemma logic_list_conj_intro :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma,
    (forall p, In p Gamma -> L p) -> L (logic_list_conj Gamma).
Proof.
  intros AtomType L Hclass Gamma; induction Gamma as [|p Gamma IH]; intro Hall.
  - change (L Top); apply logic_mem_top; exact Hclass.
  - change (L (And p (logic_list_conj Gamma))).
    apply logic_and_intro; [exact Hclass | apply Hall; now left |].
    apply IH; intros q Hq; apply Hall; now right.
Qed.

Lemma logic_list_conj_incl :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma Delta,
    incl Gamma Delta ->
    L (Imp (logic_list_conj Delta) (logic_list_conj Gamma)).
Proof.
  intros AtomType L Hclass Gamma Delta Hincl.
  apply (logic_classical_tautology Hclass); intro rho; simpl.
  rewrite !classical_eval_list_conj.
  rewrite !Forall_forall; firstorder.
Qed.

Lemma logic_list_conj_elim :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p,
    In p Gamma -> L (logic_list_conj Gamma) -> L p.
Proof.
  intros AtomType L Hclass Gamma p Hp HGamma.
  eapply (logic_modus_ponens Hclass); [|exact HGamma].
  apply (logic_classical_tautology Hclass); intro rho; simpl.
  rewrite classical_eval_list_conj, Forall_forall; firstorder.
Qed.

(** * Letterless formulas and logics *)

Fixpoint formula_letterless {AtomType} (p : formula AtomType) : Prop :=
  match p with
  | Atom _ => False
  | Bottom => True
  | Imp q r => formula_letterless q /\ formula_letterless r
  | Box q => formula_letterless q
  end.

Definition logic_letterless {AtomType}
    (L : modal_logic_set AtomType) : Prop :=
  forall p, L p -> formula_letterless p.

Lemma substitute_letterless :
  forall (AtomType : Type) (sigma : AtomType -> formula AtomType) p,
    formula_letterless p -> substitute sigma p = p.
Proof.
  intros AtomType sigma p.
  induction p as [a| |p IHp q IHq|p IHp]; simpl; intros H.
  - contradiction.
  - reflexivity.
  - destruct H as [Hp Hq]; rewrite IHp, IHq; auto.
  - now rewrite IHp.
Qed.

Lemma logic_substitution_of_letterless :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    logic_letterless L -> logic_substitution_closed L.
Proof.
  intros AtomType L Hletterless sigma p Hp.
  rewrite (substitute_letterless sigma (Hletterless p Hp)); exact Hp.
Qed.

(** * The normal sum of two logics *)

(** This is the least normal-rule closure containing both operands.  As in
    Foundation, substitution is a rule of the generated derivation rather
    than a side condition on the two input predicates. *)
Inductive logic_sum_normal {AtomType}
    (L1 L2 : modal_logic_set AtomType) : modal_logic_set AtomType :=
| LSN_mem_left : forall p, L1 p -> logic_sum_normal L1 L2 p
| LSN_mem_right : forall p, L2 p -> logic_sum_normal L1 L2 p
| LSN_mp : forall p q,
    logic_sum_normal L1 L2 (Imp p q) ->
    logic_sum_normal L1 L2 p ->
    logic_sum_normal L1 L2 q
| LSN_substitute : forall sigma p,
    logic_sum_normal L1 L2 p ->
    logic_sum_normal L1 L2 (substitute sigma p)
| LSN_nec : forall p,
    logic_sum_normal L1 L2 p ->
    logic_sum_normal L1 L2 (Box p).

Arguments LSN_mem_left {AtomType L1 L2 p} _.
Arguments LSN_mem_right {AtomType L1 L2 p} _.
Arguments LSN_mp {AtomType L1 L2 p q} _ _.
Arguments LSN_substitute {AtomType L1 L2} sigma {p} _.
Arguments LSN_nec {AtomType L1 L2 p} _.

Lemma logic_sum_normal_mem_left :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType) p,
    L1 p -> logic_sum_normal L1 L2 p.
Proof. intros; now apply LSN_mem_left. Qed.

Lemma logic_sum_normal_mem_right :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType) p,
    L2 p -> logic_sum_normal L1 L2 p.
Proof. intros; now apply LSN_mem_right. Qed.

Lemma logic_sum_normal_modus_ponens :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType) p q,
    logic_sum_normal L1 L2 (Imp p q) ->
    logic_sum_normal L1 L2 p ->
    logic_sum_normal L1 L2 q.
Proof. intros; eapply LSN_mp; eassumption. Qed.

Lemma logic_sum_normal_substitution :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    logic_substitution_closed (logic_sum_normal L1 L2).
Proof. intros AtomType L1 L2 sigma p Hp; now apply LSN_substitute. Qed.

Lemma logic_sum_normal_necessitation :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType) p,
    logic_sum_normal L1 L2 p ->
    logic_sum_normal L1 L2 (Box p).
Proof. intros; now apply LSN_nec. Qed.

Lemma logic_sum_normal_rec :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType)
         (P : formula AtomType -> Prop),
    (forall p, L1 p -> P p) ->
    (forall p, L2 p -> P p) ->
    (forall p q, logic_sum_normal L1 L2 (Imp p q) -> P (Imp p q) ->
                 logic_sum_normal L1 L2 p -> P p -> P q) ->
    (forall sigma p, logic_sum_normal L1 L2 p -> P p ->
                     P (substitute sigma p)) ->
    (forall p, logic_sum_normal L1 L2 p -> P p -> P (Box p)) ->
    forall p, logic_sum_normal L1 L2 p -> P p.
Proof.
  intros AtomType L1 L2 P Hleft Hright Hmp Hsubst Hnec p Hp.
  induction Hp; eauto.
Qed.

Lemma logic_sum_normal_sym_equiv :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    logic_equiv (logic_sum_normal L1 L2) (logic_sum_normal L2 L1).
Proof.
  intros AtomType L1 L2; split; intros p Hp; induction Hp.
  - now apply LSN_mem_right.
  - now apply LSN_mem_left.
  - eapply LSN_mp; eassumption.
  - now apply LSN_substitute.
  - now apply LSN_nec.
  - now apply LSN_mem_right.
  - now apply LSN_mem_left.
  - eapply LSN_mp; eassumption.
  - now apply LSN_substitute.
  - now apply LSN_nec.
Qed.

Lemma logic_sum_normal_sym :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    logic_sum_normal L1 L2 = logic_sum_normal L2 L1.
Proof.
  intros; apply (proj2 (logic_eq_iff_equiv _ _)).
  apply logic_sum_normal_sym_equiv.
Qed.

Lemma logic_sum_normal_classical_left :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    classical_logic L1 -> classical_logic (logic_sum_normal L1 L2).
Proof.
  intros AtomType L1 L2 Hclass; constructor.
  - intros p Hp; apply LSN_mem_left, (logic_classical_tautology Hclass), Hp.
  - intros p q; apply LSN_mp.
Qed.

Lemma logic_sum_normal_classical_right :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    classical_logic L2 -> classical_logic (logic_sum_normal L1 L2).
Proof.
  intros AtomType L1 L2 Hclass; constructor.
  - intros p Hp; apply LSN_mem_right, (logic_classical_tautology Hclass), Hp.
  - intros p q; apply LSN_mp.
Qed.

Lemma logic_sum_normal_quasi_left :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    quasi_normal_logic L1 -> quasi_normal_logic (logic_sum_normal L1 L2).
Proof.
  intros AtomType L1 L2 Hquasi; constructor.
  - now apply logic_sum_normal_classical_left, (quasi_classical Hquasi).
  - intros p q; now apply LSN_mem_left, (quasi_modal_K Hquasi).
  - intro p; now apply LSN_mem_left, (quasi_dia_duality Hquasi).
  - apply logic_sum_normal_substitution.
Qed.

Lemma logic_sum_normal_quasi_right :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    quasi_normal_logic L2 -> quasi_normal_logic (logic_sum_normal L1 L2).
Proof.
  intros AtomType L1 L2 Hquasi; constructor.
  - now apply logic_sum_normal_classical_right, (quasi_classical Hquasi).
  - intros p q; now apply LSN_mem_right, (quasi_modal_K Hquasi).
  - intro p; now apply LSN_mem_right, (quasi_dia_duality Hquasi).
  - apply logic_sum_normal_substitution.
Qed.

Lemma logic_sum_normal_normal_left :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    normal_logic L1 -> normal_logic (logic_sum_normal L1 L2).
Proof.
  intros AtomType L1 L2 Hnormal; constructor.
  - now apply logic_sum_normal_quasi_left, (normal_quasi Hnormal).
  - intros p; apply LSN_nec.
Qed.

Lemma logic_sum_normal_normal_right :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    normal_logic L2 -> normal_logic (logic_sum_normal L1 L2).
Proof.
  intros AtomType L1 L2 Hnormal; constructor.
  - now apply logic_sum_normal_quasi_right, (normal_quasi Hnormal).
  - intros p; apply LSN_nec.
Qed.

Lemma logic_sum_normal_includes_left :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    logic_subset L1 (logic_sum_normal L1 L2).
Proof. intros AtomType L1 L2 p; apply LSN_mem_left. Qed.

Lemma logic_sum_normal_includes_right :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    logic_subset L2 (logic_sum_normal L1 L2).
Proof. intros AtomType L1 L2 p; apply LSN_mem_right. Qed.

(** Universal property of the normal sum.  This factors the closure argument
    used by generated companion logics and later least-extension proofs. *)
Lemma logic_sum_normal_covered :
  forall (AtomType : Type) (L1 L2 L3 : modal_logic_set AtomType),
    normal_logic L3 ->
    logic_subset L1 L3 -> logic_subset L2 L3 ->
    logic_subset (logic_sum_normal L1 L2) L3.
Proof.
  intros AtomType L1 L2 L3 Hnormal Hleft Hright p Hp.
  induction Hp.
  - now apply Hleft.
  - now apply Hright.
  - exact (logic_modus_ponens (quasi_classical (normal_quasi Hnormal))
      IHHp1 IHHp2).
  - exact (quasi_substitution (normal_quasi Hnormal) sigma IHHp).
  - exact (normal_nec Hnormal IHHp).
Qed.

(** * The quasinormal sum *)

Inductive logic_sum_quasi_normal {AtomType}
    (L1 L2 : modal_logic_set AtomType) : modal_logic_set AtomType :=
| LSQ_mem_left : forall p, L1 p -> logic_sum_quasi_normal L1 L2 p
| LSQ_mem_right : forall p, L2 p -> logic_sum_quasi_normal L1 L2 p
| LSQ_mp : forall p q,
    logic_sum_quasi_normal L1 L2 (Imp p q) ->
    logic_sum_quasi_normal L1 L2 p ->
    logic_sum_quasi_normal L1 L2 q
| LSQ_substitute : forall sigma p,
    logic_sum_quasi_normal L1 L2 p ->
    logic_sum_quasi_normal L1 L2 (substitute sigma p).

Arguments LSQ_mem_left {AtomType L1 L2 p} _.
Arguments LSQ_mem_right {AtomType L1 L2 p} _.
Arguments LSQ_mp {AtomType L1 L2 p q} _ _.
Arguments LSQ_substitute {AtomType L1 L2} sigma {p} _.

Lemma logic_sum_quasi_normal_mem_left :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType) p,
    L1 p -> logic_sum_quasi_normal L1 L2 p.
Proof. intros; now apply LSQ_mem_left. Qed.

Lemma logic_sum_quasi_normal_mem_right :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType) p,
    L2 p -> logic_sum_quasi_normal L1 L2 p.
Proof. intros; now apply LSQ_mem_right. Qed.

Lemma logic_sum_quasi_normal_modus_ponens :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType) p q,
    logic_sum_quasi_normal L1 L2 (Imp p q) ->
    logic_sum_quasi_normal L1 L2 p ->
    logic_sum_quasi_normal L1 L2 q.
Proof. intros; eapply LSQ_mp; eassumption. Qed.

Lemma logic_sum_quasi_normal_substitution :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    logic_substitution_closed (logic_sum_quasi_normal L1 L2).
Proof. intros AtomType L1 L2 sigma p Hp; now apply LSQ_substitute. Qed.

Lemma logic_sum_quasi_normal_rec :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType)
         (P : formula AtomType -> Prop),
    (forall p, L1 p -> P p) ->
    (forall p, L2 p -> P p) ->
    (forall p q, logic_sum_quasi_normal L1 L2 (Imp p q) -> P (Imp p q) ->
                 logic_sum_quasi_normal L1 L2 p -> P p -> P q) ->
    (forall sigma p, logic_sum_quasi_normal L1 L2 p -> P p ->
                     P (substitute sigma p)) ->
    forall p, logic_sum_quasi_normal L1 L2 p -> P p.
Proof.
  intros AtomType L1 L2 P Hleft Hright Hmp Hsubst p Hp.
  induction Hp; eauto.
Qed.

Lemma logic_sum_quasi_normal_sym_equiv :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    logic_equiv (logic_sum_quasi_normal L1 L2)
                (logic_sum_quasi_normal L2 L1).
Proof.
  intros AtomType L1 L2; split; intros p Hp; induction Hp.
  - now apply LSQ_mem_right.
  - now apply LSQ_mem_left.
  - eapply LSQ_mp; eassumption.
  - now apply LSQ_substitute.
  - now apply LSQ_mem_right.
  - now apply LSQ_mem_left.
  - eapply LSQ_mp; eassumption.
  - now apply LSQ_substitute.
Qed.

Lemma logic_sum_quasi_normal_sym :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    logic_sum_quasi_normal L1 L2 = logic_sum_quasi_normal L2 L1.
Proof.
  intros; apply (proj2 (logic_eq_iff_equiv _ _)).
  apply logic_sum_quasi_normal_sym_equiv.
Qed.

Lemma logic_sum_quasi_normal_classical_left :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    classical_logic L1 -> classical_logic (logic_sum_quasi_normal L1 L2).
Proof.
  intros AtomType L1 L2 Hclass; constructor.
  - intros p Hp; apply LSQ_mem_left, (logic_classical_tautology Hclass), Hp.
  - intros p q; apply LSQ_mp.
Qed.

Lemma logic_sum_quasi_normal_classical_right :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    classical_logic L2 -> classical_logic (logic_sum_quasi_normal L1 L2).
Proof.
  intros AtomType L1 L2 Hclass; constructor.
  - intros p Hp; apply LSQ_mem_right, (logic_classical_tautology Hclass), Hp.
  - intros p q; apply LSQ_mp.
Qed.

Lemma logic_sum_quasi_normal_quasi_left :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    quasi_normal_logic L1 ->
    quasi_normal_logic (logic_sum_quasi_normal L1 L2).
Proof.
  intros AtomType L1 L2 Hquasi; constructor.
  - now apply logic_sum_quasi_normal_classical_left,
      (quasi_classical Hquasi).
  - intros p q; now apply LSQ_mem_left, (quasi_modal_K Hquasi).
  - intro p; now apply LSQ_mem_left, (quasi_dia_duality Hquasi).
  - apply logic_sum_quasi_normal_substitution.
Qed.

Lemma logic_sum_quasi_normal_quasi_right :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    quasi_normal_logic L2 ->
    quasi_normal_logic (logic_sum_quasi_normal L1 L2).
Proof.
  intros AtomType L1 L2 Hquasi; constructor.
  - now apply logic_sum_quasi_normal_classical_right,
      (quasi_classical Hquasi).
  - intros p q; now apply LSQ_mem_right, (quasi_modal_K Hquasi).
  - intro p; now apply LSQ_mem_right, (quasi_dia_duality Hquasi).
  - apply logic_sum_quasi_normal_substitution.
Qed.

Lemma logic_sum_quasi_normal_includes_left :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    logic_subset L1 (logic_sum_quasi_normal L1 L2).
Proof. intros AtomType L1 L2 p; apply LSQ_mem_left. Qed.

Lemma logic_sum_quasi_normal_includes_right :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    logic_subset L2 (logic_sum_quasi_normal L1 L2).
Proof. intros AtomType L1 L2 p; apply LSQ_mem_right. Qed.

Lemma logic_sum_quasi_normal_iff_subset :
  forall (AtomType : Type) (L X Y : modal_logic_set AtomType),
    logic_subset (logic_sum_quasi_normal L Y)
                 (logic_sum_quasi_normal L X) <->
    forall p, Y p -> logic_sum_quasi_normal L X p.
Proof.
  intros AtomType L X Y; split.
  - intros Hsubset p Hp; apply Hsubset, LSQ_mem_right, Hp.
  - intros HY p Hp; induction Hp.
    + now apply LSQ_mem_left.
    + now apply HY.
    + eapply LSQ_mp; eassumption.
    + now apply LSQ_substitute.
Qed.

(** The eliminator used by [covered]: closure of a target predicate is
    exactly the universal property of the generated quasinormal sum. *)
Lemma logic_sum_quasi_normal_covered :
  forall (AtomType : Type) (L1 L2 L3 : modal_logic_set AtomType),
    (forall p q, L3 (Imp p q) -> L3 p -> L3 q) ->
    logic_substitution_closed L3 ->
    logic_subset L1 L3 -> logic_subset L2 L3 ->
    logic_subset (logic_sum_quasi_normal L1 L2) L3.
Proof.
  intros AtomType L1 L2 L3 Hmp Hsubst Hleft Hright p Hp.
  induction Hp.
  - now apply Hleft.
  - now apply Hright.
  - eapply Hmp; eassumption.
  - now apply Hsubst.
Qed.

Lemma logic_sum_quasi_normal_sum_union :
  forall (AtomType : Type) (L X Y : modal_logic_set AtomType),
    logic_sum_quasi_normal (logic_sum_quasi_normal L X) Y =
    logic_sum_quasi_normal L (logic_union X Y).
Proof.
  intros AtomType L X Y.
  apply (proj2 (logic_eq_iff_equiv _ _)); split; intros p Hp.
  - induction Hp.
    + induction H.
      * now apply LSQ_mem_left.
      * apply LSQ_mem_right; now left.
      * eapply LSQ_mp; eassumption.
      * now apply LSQ_substitute.
    + apply LSQ_mem_right; now right.
    + eapply LSQ_mp; eassumption.
    + now apply LSQ_substitute.
  - induction Hp.
    + apply LSQ_mem_left; now apply LSQ_mem_left.
    + destruct H as [HX | HY].
      * apply LSQ_mem_left; now apply LSQ_mem_right.
      * now apply LSQ_mem_right.
    + eapply LSQ_mp; eassumption.
    + now apply LSQ_substitute.
Qed.

(** A list is the constructive finite witness corresponding to Foundation's
    finite set.  Repetition and ordering do not affect the statement. *)
Definition logic_finitely_provable_from {AtomType}
    (L1 L2 : modal_logic_set AtomType) (p : formula AtomType) : Prop :=
  exists Gamma : list (formula AtomType),
    (forall q, In q Gamma -> L2 q) /\
    L1 (Imp (logic_list_conj Gamma) p).

Lemma logic_sum_quasi_normal_provable_of_finite_provable :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    classical_logic L1 -> forall p,
    logic_finitely_provable_from L1 L2 p ->
    logic_sum_quasi_normal L1 L2 p.
Proof.
  intros AtomType L1 L2 Hclass p [Gamma [HGamma Himp]].
  eapply LSQ_mp.
  - exact (LSQ_mem_left Himp).
  - apply logic_list_conj_intro.
    + now apply logic_sum_quasi_normal_classical_left.
    + intros q Hq; apply LSQ_mem_right, HGamma, Hq.
Qed.

Lemma logic_sum_quasi_normal_finite_provable_of_provable :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    classical_logic L1 ->
    logic_substitution_closed L1 ->
    logic_substitution_closed L2 ->
    forall p, logic_sum_quasi_normal L1 L2 p ->
    logic_finitely_provable_from L1 L2 p.
Proof.
  intros AtomType L1 L2 Hclass Hsubst1 Hsubst2 p Hp.
  induction Hp as
      [p Hp | p Hp | p q Hpq IHpq Hp IHp | sigma p Hp IH].
  - exists []; split.
    + intros q Hq; contradiction.
    + now apply logic_imply_intro.
  - exists [p]; split.
    + intros q Hq; destruct Hq as [-> | Hq]; [exact Hp | contradiction].
    + apply (logic_classical_tautology Hclass); intro rho; simpl.
      unfold And, Top, Neg; simpl.
      destruct (classic (classical_eval rho p)); tauto.
  - destruct IHpq as [Gamma1 [HGamma1 Himp1]].
    destruct IHp as [Gamma2 [HGamma2 Himp2]].
    exists (Gamma1 ++ Gamma2); split.
    + intros r Hr; apply in_app_or in Hr; destruct Hr.
      * now apply HGamma1.
      * now apply HGamma2.
    + pose proof
        (logic_list_conj_incl Hclass
          (Gamma := Gamma1) (Delta := Gamma1 ++ Gamma2)
          (fun r Hr => in_or_app Gamma1 Gamma2 r (or_introl Hr))) as Hleft.
      pose proof
        (logic_list_conj_incl Hclass
          (Gamma := Gamma2) (Delta := Gamma1 ++ Gamma2)
          (fun r Hr => in_or_app Gamma1 Gamma2 r (or_intror Hr))) as Hright.
      eapply logic_under_mp; [exact Hclass | |].
      * eapply logic_imp_trans; [exact Hclass | exact Hleft | exact Himp1].
      * eapply logic_imp_trans; [exact Hclass | exact Hright | exact Himp2].
  - destruct IH as [Gamma [HGamma Himp]].
    exists (map (substitute sigma) Gamma); split.
    + intros r Hr; apply in_map_iff in Hr.
      destruct Hr as [q [<- Hq]].
      now apply Hsubst2, HGamma.
    + rewrite <- substitute_logic_list_conj.
      change (L1 (substitute sigma (Imp (logic_list_conj Gamma) p))).
      now apply Hsubst1.
Qed.

Lemma logic_sum_quasi_normal_iff_finite_provable :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    classical_logic L1 ->
    logic_substitution_closed L1 ->
    logic_substitution_closed L2 ->
    forall p,
      logic_sum_quasi_normal L1 L2 p <->
      logic_finitely_provable_from L1 L2 p.
Proof.
  intros AtomType L1 L2 Hclass Hsubst1 Hsubst2 p; split.
  - now apply logic_sum_quasi_normal_finite_provable_of_provable.
  - now apply logic_sum_quasi_normal_provable_of_finite_provable.
Qed.

Lemma logic_sum_quasi_normal_iff_finite_provable_letterless :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    classical_logic L1 ->
    logic_substitution_closed L1 ->
    logic_letterless L2 ->
    forall p,
      logic_sum_quasi_normal L1 L2 p <->
      logic_finitely_provable_from L1 L2 p.
Proof.
  intros AtomType L1 L2 Hclass Hsubst1 Hletterless p.
  apply logic_sum_quasi_normal_iff_finite_provable; try assumption.
  now apply logic_substitution_of_letterless.
Qed.

Lemma logic_sum_quasi_normal_with_empty :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    quasi_normal_logic L ->
    logic_sum_quasi_normal L logic_empty = L.
Proof.
  intros AtomType L Hquasi.
  apply (proj2 (logic_eq_iff_equiv _ _)); split.
  - intros p Hp; induction Hp.
    + exact H.
    + contradiction.
    + eapply (logic_modus_ponens (quasi_classical Hquasi)); eassumption.
    + now apply (quasi_substitution Hquasi).
  - intros p Hp; now apply LSQ_mem_left.
Qed.

(** Foundation's alternate presentation places substitutions only at the
    two leaves.  It is useful for induction principles that omit an explicit
    substitution case. *)
Inductive logic_sum_quasi_normal_alt {AtomType}
    (L1 L2 : modal_logic_set AtomType) : modal_logic_set AtomType :=
| LSQA_mem_left : forall sigma p, L1 p ->
    logic_sum_quasi_normal_alt L1 L2 (substitute sigma p)
| LSQA_mem_right : forall sigma p, L2 p ->
    logic_sum_quasi_normal_alt L1 L2 (substitute sigma p)
| LSQA_mp : forall p q,
    logic_sum_quasi_normal_alt L1 L2 (Imp p q) ->
    logic_sum_quasi_normal_alt L1 L2 p ->
    logic_sum_quasi_normal_alt L1 L2 q.

Arguments LSQA_mem_left {AtomType L1 L2} sigma {p} _.
Arguments LSQA_mem_right {AtomType L1 L2} sigma {p} _.
Arguments LSQA_mp {AtomType L1 L2 p q} _ _.

Lemma logic_sum_quasi_normal_alt_mem_left :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType)
         sigma p, L1 p ->
    logic_sum_quasi_normal_alt L1 L2 (substitute sigma p).
Proof. intros; now apply LSQA_mem_left. Qed.

Lemma logic_sum_quasi_normal_alt_mem_left_nosub :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType) p,
    L1 p -> logic_sum_quasi_normal_alt L1 L2 p.
Proof.
  intros AtomType L1 L2 p Hp.
  rewrite <- (@substitute_id AtomType p).
  exact (LSQA_mem_left (@Atom AtomType) Hp).
Qed.

Lemma logic_sum_quasi_normal_alt_mem_right :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType)
         sigma p, L2 p ->
    logic_sum_quasi_normal_alt L1 L2 (substitute sigma p).
Proof. intros; now apply LSQA_mem_right. Qed.

Lemma logic_sum_quasi_normal_alt_mem_right_nosub :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType) p,
    L2 p -> logic_sum_quasi_normal_alt L1 L2 p.
Proof.
  intros AtomType L1 L2 p Hp.
  rewrite <- (@substitute_id AtomType p).
  exact (LSQA_mem_right (@Atom AtomType) Hp).
Qed.

Lemma logic_sum_quasi_normal_alt_modus_ponens :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType) p q,
    logic_sum_quasi_normal_alt L1 L2 (Imp p q) ->
    logic_sum_quasi_normal_alt L1 L2 p ->
    logic_sum_quasi_normal_alt L1 L2 q.
Proof. intros; eapply LSQA_mp; eassumption. Qed.

Lemma logic_sum_quasi_normal_alt_rec :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType)
         (P : formula AtomType -> Prop),
    (forall sigma p, L1 p -> P (substitute sigma p)) ->
    (forall sigma p, L2 p -> P (substitute sigma p)) ->
    (forall p q,
        logic_sum_quasi_normal_alt L1 L2 (Imp p q) -> P (Imp p q) ->
        logic_sum_quasi_normal_alt L1 L2 p -> P p -> P q) ->
    forall p, logic_sum_quasi_normal_alt L1 L2 p -> P p.
Proof.
  intros AtomType L1 L2 P Hleft Hright Hmp p Hp.
  induction Hp; eauto.
Qed.

Lemma logic_sum_quasi_normal_alt_substitution :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    logic_substitution_closed (logic_sum_quasi_normal_alt L1 L2).
Proof.
  intros AtomType L1 L2 tau p Hp; induction Hp.
  - rewrite substitute_comp; now apply LSQA_mem_left.
  - rewrite substitute_comp; now apply LSQA_mem_right.
  - simpl; eapply LSQA_mp; eassumption.
Qed.

Lemma logic_sum_quasi_normal_to_alt :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    logic_subset (logic_sum_quasi_normal L1 L2)
                 (logic_sum_quasi_normal_alt L1 L2).
Proof.
  intros AtomType L1 L2 p Hp; induction Hp.
  - now apply logic_sum_quasi_normal_alt_mem_left_nosub.
  - now apply logic_sum_quasi_normal_alt_mem_right_nosub.
  - eapply LSQA_mp; eassumption.
  - now apply logic_sum_quasi_normal_alt_substitution.
Qed.

Lemma logic_sum_quasi_normal_alt_to_main :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    logic_subset (logic_sum_quasi_normal_alt L1 L2)
                 (logic_sum_quasi_normal L1 L2).
Proof.
  intros AtomType L1 L2 p Hp; induction Hp.
  - apply LSQ_substitute; now apply LSQ_mem_left.
  - apply LSQ_substitute; now apply LSQ_mem_right.
  - eapply LSQ_mp; eassumption.
Qed.

Lemma logic_sum_quasi_normal_eq_alt :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType),
    logic_sum_quasi_normal L1 L2 = logic_sum_quasi_normal_alt L1 L2.
Proof.
  intros; apply (proj2 (logic_eq_iff_equiv _ _)); split.
  - apply logic_sum_quasi_normal_to_alt.
  - apply logic_sum_quasi_normal_alt_to_main.
Qed.

Lemma logic_sum_quasi_normal_alt_iff_main :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType) p,
    logic_sum_quasi_normal_alt L1 L2 p <->
    logic_sum_quasi_normal L1 L2 p.
Proof.
  intros; split.
  - apply logic_sum_quasi_normal_alt_to_main.
  - apply logic_sum_quasi_normal_to_alt.
Qed.

Lemma logic_sum_quasi_normal_rec_omit_substitution :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType)
         (P : formula AtomType -> Prop),
    (forall sigma p, L1 p -> P (substitute sigma p)) ->
    (forall sigma p, L2 p -> P (substitute sigma p)) ->
    (forall p q, P (Imp p q) -> P p -> P q) ->
    forall p, logic_sum_quasi_normal L1 L2 p -> P p.
Proof.
  intros AtomType L1 L2 P Hleft Hright Hmp p Hp.
  pose proof (logic_sum_quasi_normal_to_alt Hp) as Halt.
  eapply (logic_sum_quasi_normal_alt_rec (P := P)).
  - exact Hleft.
  - exact Hright.
  - intros r s Hrs IHrs Hr IHr; eapply Hmp; eassumption.
  - exact Halt.
Qed.

Lemma logic_sum_quasi_normal_rec_omit_substitution_left :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType)
         (P : formula AtomType -> Prop),
    logic_substitution_closed L1 ->
    (forall p, L1 p -> P p) ->
    (forall sigma p, L2 p -> P (substitute sigma p)) ->
    (forall p q, P (Imp p q) -> P p -> P q) ->
    forall p, logic_sum_quasi_normal L1 L2 p -> P p.
Proof.
  intros AtomType L1 L2 P Hsubst Hleft Hright Hmp.
  eapply logic_sum_quasi_normal_rec_omit_substitution.
  - intros sigma p Hp; apply Hleft, Hsubst, Hp.
  - exact Hright.
  - exact Hmp.
Qed.

Lemma logic_sum_quasi_normal_rec_omit_substitution_right :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType)
         (P : formula AtomType -> Prop),
    logic_substitution_closed L2 ->
    (forall sigma p, L1 p -> P (substitute sigma p)) ->
    (forall p, L2 p -> P p) ->
    (forall p q, P (Imp p q) -> P p -> P q) ->
    forall p, logic_sum_quasi_normal L1 L2 p -> P p.
Proof.
  intros AtomType L1 L2 P Hsubst Hleft Hright Hmp.
  eapply logic_sum_quasi_normal_rec_omit_substitution.
  - exact Hleft.
  - intros sigma p Hp; apply Hright, Hsubst, Hp.
  - exact Hmp.
Qed.

Lemma logic_sum_quasi_normal_rec_omit_substitution_strong :
  forall (AtomType : Type) (L1 L2 : modal_logic_set AtomType)
         (P : formula AtomType -> Prop),
    logic_substitution_closed L1 ->
    logic_substitution_closed L2 ->
    (forall p, L1 p -> P p) ->
    (forall p, L2 p -> P p) ->
    (forall p q, P (Imp p q) -> P p -> P q) ->
    forall p, logic_sum_quasi_normal L1 L2 p -> P p.
Proof.
  intros AtomType L1 L2 P Hsubst1 Hsubst2 Hleft Hright Hmp.
  eapply logic_sum_quasi_normal_rec_omit_substitution.
  - intros sigma p Hp; apply Hleft, Hsubst1, Hp.
  - intros sigma p Hp; apply Hright, Hsubst2, Hp.
  - exact Hmp.
Qed.

Lemma logic_sum_quasi_normal_rec_letterless_expansion :
  forall (AtomType : Type) (L X : modal_logic_set AtomType)
         (P : formula AtomType -> Prop),
    logic_substitution_closed L ->
    logic_letterless X ->
    (forall p, L p -> P p) ->
    (forall p, X p -> P p) ->
    (forall p q, P (Imp p q) -> P p -> P q) ->
    forall p, logic_sum_quasi_normal L X p -> P p.
Proof.
  intros AtomType L X P Hsubst Hletterless Hleft Hright Hmp.
  eapply logic_sum_quasi_normal_rec_omit_substitution_strong.
  - exact Hsubst.
  - now apply logic_substitution_of_letterless.
  - exact Hleft.
  - exact Hright.
  - exact Hmp.
Qed.

(** * Global consequence *)

Definition theory_union {AtomType}
    (X Y : theory AtomType) : theory AtomType :=
  fun p => X p \/ Y p.

Lemma theory_union_comm :
  forall (AtomType : Type) (X Y : theory AtomType),
    theory_union X Y = theory_union Y X.
Proof.
  intros AtomType X Y; apply functional_extensionality; intro p.
  apply propositional_extensionality; unfold theory_union; tauto.
Qed.

Lemma theory_union_idempotent :
  forall (AtomType : Type) (X : theory AtomType),
    theory_union X X = X.
Proof.
  intros AtomType X; apply functional_extensionality; intro p.
  apply propositional_extensionality; unfold theory_union; tauto.
Qed.

Lemma logic_and_elim_left_imp :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q, L (Imp (And p q) p).
Proof.
  intros AtomType L Hclass p q.
  apply (logic_classical_tautology Hclass); intro rho.
  unfold And, Neg; simpl.
  destruct (classic (classical_eval rho p));
    destruct (classic (classical_eval rho q)); tauto.
Qed.

Lemma logic_and_elim_right_imp :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q, L (Imp (And p q) q).
Proof.
  intros AtomType L Hclass p q.
  apply (logic_classical_tautology Hclass); intro rho.
  unfold And, Neg; simpl.
  destruct (classic (classical_eval rho p));
    destruct (classic (classical_eval rho q)); tauto.
Qed.

Lemma logic_box_regularity :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall p q,
    L (Imp p q) -> L (Imp (Box p) (Box q)).
Proof.
  intros AtomType L Hnormal p q Hpq.
  eapply (logic_modus_ponens (quasi_classical (normal_quasi Hnormal))).
  - exact (quasi_modal_K (normal_quasi Hnormal) p q).
  - now apply (normal_nec Hnormal).
Qed.

Lemma logic_box_and_collect :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall p q,
    L (Imp (And (Box p) (Box q)) (Box (And p q))).
Proof.
  intros AtomType L Hnormal p q.
  pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
  assert (Hintro : L (Imp p (Imp q (And p q)))).
  { apply (logic_classical_tautology Hclass).
    intro rho; unfold And, Neg; simpl; tauto. }
  pose proof (normal_nec Hnormal Hintro) as Hboxed.
  pose proof
    (logic_modus_ponens Hclass
      (quasi_modal_K (normal_quasi Hnormal) p (Imp q (And p q)))
      Hboxed) as Hfirst.
  pose proof (quasi_modal_K (normal_quasi Hnormal) q (And p q)) as Hsecond.
  pose proof (logic_imp_trans Hclass Hfirst Hsecond) as Hcurried.
  eapply (logic_modus_ponens Hclass); [|exact Hcurried].
  apply (logic_classical_tautology Hclass).
  intro rho; unfold And, Neg; simpl; tauto.
Qed.

(** [global_box_le n p] is an idiomatic cumulative presentation of the
    finite conjunction [p /\ box p /\ ... /\ box^n p].  It is K-equivalent
    to Foundation's [boxLe], while its successor equation makes contextual
    necessitation transparent. *)
Fixpoint global_box_le {AtomType} (n : nat) (p : formula AtomType)
    : formula AtomType :=
  match n with
  | 0 => p
  | S k => And (global_box_le k p) (Box (global_box_le k p))
  end.

(** A source-facing presentation of Foundation's [boxLe]: the conjunction
    contains the individual iterates [p], [box p], ..., [box^n p]. *)
Fixpoint foundation_box_le {AtomType} (n : nat) (p : formula AtomType)
    : formula AtomType :=
  match n with
  | 0 => p
  | S k => And (foundation_box_le k p) (box_iter (S k) p)
  end.

Lemma substitute_global_box_le :
  forall (A B : Type) (sigma : A -> formula B) n p,
    substitute sigma (global_box_le n p) =
    global_box_le n (substitute sigma p).
Proof.
  intros A B sigma n; induction n as [|n IH]; intros p; simpl; auto.
  now rewrite IH.
Qed.

Lemma substitute_foundation_box_le :
  forall (A B : Type) (sigma : A -> formula B) n p,
    substitute sigma (foundation_box_le n p) =
    foundation_box_le n (substitute sigma p).
Proof.
  intros A B sigma n; induction n as [|n IH]; intros p; simpl; auto.
  now rewrite IH, substitute_box_iter.
Qed.

Lemma logic_foundation_box_le_last :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall n p,
    L (Imp (foundation_box_le n p) (box_iter n p)).
Proof.
  intros AtomType L Hclass n; destruct n as [|n]; intro p; simpl.
  - now apply logic_identity.
  - now apply logic_and_elim_right_imp.
Qed.

Lemma logic_foundation_box_le_collect_next :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n p,
    L (Imp (foundation_box_le (S n) p)
           (Box (foundation_box_le n p))).
Proof.
  intros AtomType L Hnormal n; induction n as [|n IH]; intro p.
  - simpl; now apply logic_and_elim_right_imp,
      (quasi_classical (normal_quasi Hnormal)).
  - pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
    change
      (L (Imp
        (And (foundation_box_le (S n) p) (box_iter (S (S n)) p))
        (Box (foundation_box_le (S n) p)))).
    pose proof
      (logic_and_elim_left_imp Hclass
        (foundation_box_le (S n) p) (box_iter (S (S n)) p)) as Hleft.
    pose proof (logic_imp_trans Hclass Hleft (IH p)) as Hboxed_left.
    pose proof
      (logic_and_elim_right_imp Hclass
        (foundation_box_le (S n) p) (box_iter (S (S n)) p)) as Hboxed_right.
    pose proof
      (logic_imp_and_intro Hclass Hboxed_left Hboxed_right) as Hpair.
    eapply logic_imp_trans; [exact Hclass | exact Hpair |].
    change
      (L (Imp
        (And (Box (foundation_box_le n p)) (Box (box_iter (S n) p)))
        (Box (And (foundation_box_le n p) (box_iter (S n) p))))).
    now apply logic_box_and_collect.
Qed.

Lemma logic_global_box_le_regularity :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n p q,
    L (Imp p q) ->
    L (Imp (global_box_le n p) (global_box_le n q)).
Proof.
  intros AtomType L Hnormal n; induction n as [|n IH]; intros p q Hpq.
  - exact Hpq.
  - simpl.
    pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
    eapply logic_imp_and_intro; [exact Hclass | |].
    + eapply logic_imp_trans; [exact Hclass | |exact (IH p q Hpq)].
      now apply logic_and_elim_left_imp.
    + eapply logic_imp_trans; [exact Hclass | |].
      * now apply logic_and_elim_right_imp.
      * now apply logic_box_regularity, IH.
Qed.

Lemma logic_global_box_le_to_foundation :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n p,
    L (Imp (global_box_le n p) (foundation_box_le n p)).
Proof.
  intros AtomType L Hnormal n; induction n as [|n IH]; intro p.
  - simpl; now apply logic_identity,
      (quasi_classical (normal_quasi Hnormal)).
  - pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
    change
      (L (Imp
        (And (global_box_le n p) (Box (global_box_le n p)))
        (And (foundation_box_le n p) (box_iter (S n) p)))).
    pose proof
      (logic_and_elim_left_imp Hclass
        (global_box_le n p) (Box (global_box_le n p))) as Hleft.
    pose proof (logic_imp_trans Hclass Hleft (IH p)) as Hto_foundation.
    pose proof
      (logic_and_elim_right_imp Hclass
        (global_box_le n p) (Box (global_box_le n p))) as Hright.
    pose proof
      (logic_imp_trans Hclass (IH p)
        (logic_foundation_box_le_last Hclass n p)) as Hto_last.
    pose proof (logic_box_regularity Hnormal Hto_last) as Hboxed_last.
    pose proof (logic_imp_trans Hclass Hright Hboxed_last) as Hto_boxed_last.
    now apply logic_imp_and_intro.
Qed.

Lemma logic_foundation_box_le_to_global :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n p,
    L (Imp (foundation_box_le n p) (global_box_le n p)).
Proof.
  intros AtomType L Hnormal n; induction n as [|n IH]; intro p.
  - simpl; now apply logic_identity,
      (quasi_classical (normal_quasi Hnormal)).
  - pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
    change
      (L (Imp
        (And (foundation_box_le n p) (box_iter (S n) p))
        (And (global_box_le n p) (Box (global_box_le n p))))).
    pose proof
      (logic_and_elim_left_imp Hclass
        (foundation_box_le n p) (box_iter (S n) p)) as Hleft.
    pose proof (logic_imp_trans Hclass Hleft (IH p)) as Hto_global.
    pose proof (logic_foundation_box_le_collect_next Hnormal n p) as Hcollect.
    pose proof (logic_box_regularity Hnormal (IH p)) as Hboxed_IH.
    pose proof (logic_imp_trans Hclass Hcollect Hboxed_IH) as Hto_boxed_global.
    now apply logic_imp_and_intro.
Qed.

Lemma logic_global_foundation_box_le_equivalence :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n p,
    L (Iff (global_box_le n p) (foundation_box_le n p)).
Proof.
  intros AtomType L Hnormal n p; unfold Iff.
  eapply logic_and_intro.
  - exact (quasi_classical (normal_quasi Hnormal)).
  - now apply logic_global_box_le_to_foundation.
  - now apply logic_foundation_box_le_to_global.
Qed.

Lemma logic_foundation_box_le_regularity :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n p q,
    L (Imp p q) ->
    L (Imp (foundation_box_le n p) (foundation_box_le n q)).
Proof.
  intros AtomType L Hnormal n p q Hpq.
  pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
  eapply logic_imp_trans; [exact Hclass | |].
  - now apply logic_foundation_box_le_to_global.
  - eapply logic_imp_trans; [exact Hclass | |].
    + exact (logic_global_box_le_regularity Hnormal n Hpq).
    + exact (logic_global_box_le_to_foundation Hnormal n q).
Qed.

Lemma logic_global_box_le_depth_add :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall n d p,
    L (Imp (global_box_le (n + d) p) (global_box_le n p)).
Proof.
  intros AtomType L Hclass n d; induction d as [|d IH]; intro p.
  - rewrite Nat.add_0_r; now apply logic_identity.
  - rewrite Nat.add_succ_r; simpl.
    eapply logic_imp_trans; [exact Hclass | |exact (IH p)].
    now apply logic_and_elim_left_imp.
Qed.

Lemma logic_global_box_le_depth_weaken :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall n k p,
    n <= k ->
    L (Imp (global_box_le k p) (global_box_le n p)).
Proof.
  intros AtomType L Hclass n k p Hle.
  replace k with (n + (k - n)) by lia.
  now apply logic_global_box_le_depth_add.
Qed.

Inductive global_consequence {AtomType}
    (L : modal_logic_set AtomType) :
    theory AtomType -> formula AtomType -> Prop :=
| GC_theorem : forall X p,
    L p -> global_consequence L X p
| GC_context : forall X p,
    X p -> global_consequence L X p
| GC_mp : forall X Y p q,
    global_consequence L X (Imp p q) ->
    global_consequence L Y p ->
    global_consequence L (theory_union X Y) q
| GC_nec : forall X p,
    global_consequence L X p ->
    global_consequence L X (Box p)
| GC_imply_K : forall X p q,
    global_consequence L X (Hilbert_imply_K p q)
| GC_imply_S : forall X p q r,
    global_consequence L X (Hilbert_imply_S p q r)
| GC_elim_contra : forall X p q,
    global_consequence L X (Hilbert_elim_contra p q).

Arguments GC_theorem {AtomType L X p} _.
Arguments GC_context {AtomType L X p} _.
Arguments GC_mp {AtomType L X Y p q} _ _.
Arguments GC_nec {AtomType L X p} _.
Arguments GC_imply_K {AtomType L} X p q.
Arguments GC_imply_S {AtomType L} X p q r.
Arguments GC_elim_contra {AtomType L} X p q.

Lemma global_consequence_theorem :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (X : theory AtomType) p,
    L p -> global_consequence L X p.
Proof. intros; now apply GC_theorem. Qed.

Lemma global_consequence_context :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (X : theory AtomType) p,
    X p -> global_consequence L X p.
Proof. intros; now apply GC_context. Qed.

Lemma global_consequence_modus_ponens :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (X : theory AtomType) p q,
    global_consequence L X (Imp p q) ->
    global_consequence L X p ->
    global_consequence L X q.
Proof.
  intros AtomType L X p q Hpq Hp.
  rewrite <- (theory_union_idempotent X).
  eapply GC_mp; eassumption.
Qed.

Lemma global_consequence_necessitation :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (X : theory AtomType) p,
    global_consequence L X p ->
    global_consequence L X (Box p).
Proof. intros; now apply GC_nec. Qed.

Lemma global_consequence_modal_K :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (X : theory AtomType) p q,
    global_consequence L X (K p q).
Proof.
  intros AtomType L Hnormal X p q.
  apply GC_theorem, (quasi_modal_K (normal_quasi Hnormal)).
Qed.

Lemma global_consequence_weaken :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (X Y : theory AtomType) p,
    theory_included X Y ->
    global_consequence L X p -> global_consequence L Y p.
Proof.
  intros AtomType L X Y p HXY Hp; revert Y HXY.
  induction Hp; intros Delta Hinc.
  - now apply GC_theorem.
  - apply GC_context, Hinc, H.
  - eapply global_consequence_modus_ponens.
    + apply IHHp1; intros r Hr; apply Hinc; now left.
    + apply IHHp2; intros r Hr; apply Hinc; now right.
  - apply GC_nec, IHHp; exact Hinc.
  - apply GC_imply_K.
  - apply GC_imply_S.
  - apply GC_elim_contra.
Qed.

Lemma global_consequence_rec :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (P : theory AtomType -> formula AtomType -> Prop),
    (forall X p, L p -> P X p) ->
    (forall X p, X p -> P X p) ->
    (forall X Y p q,
        global_consequence L X (Imp p q) -> P X (Imp p q) ->
        global_consequence L Y p -> P Y p ->
        P (theory_union X Y) q) ->
    (forall X p, global_consequence L X p -> P X p -> P X (Box p)) ->
    (forall X p q, P X (Hilbert_imply_K p q)) ->
    (forall X p q r, P X (Hilbert_imply_S p q r)) ->
    (forall X p q, P X (Hilbert_elim_contra p q)) ->
    forall X p, global_consequence L X p -> P X p.
Proof.
  intros AtomType L P Hthm Hctx Hmp Hnec HK HS Hcontra X p Hp.
  induction Hp; eauto.
Qed.

Lemma global_consequence_classical :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall X,
    classical_logic (@global_consequence AtomType L X).
Proof.
  intros AtomType L Hclass X; constructor.
  - intros p Hp; apply GC_theorem, (logic_classical_tautology Hclass), Hp.
  - intros p q; apply global_consequence_modus_ponens.
Qed.

Lemma global_consequence_contains_K :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall X p,
    K_proves p -> global_consequence L X p.
Proof.
  intros AtomType L Hnormal X p Hp.
  apply GC_theorem, (normal_logic_contains_K Hnormal), Hp.
Qed.

Lemma global_consequence_list_conj_intro :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall X Gamma,
    (forall p, In p Gamma -> global_consequence L X p) ->
    global_consequence L X (logic_list_conj Gamma).
Proof.
  intros AtomType L Hclass X Gamma Hall.
  apply logic_list_conj_intro.
  - now apply global_consequence_classical.
  - exact Hall.
Qed.

Lemma global_consequence_box_le_intro :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall X n p,
    global_consequence L X p ->
    global_consequence L X (global_box_le n p).
Proof.
  intros AtomType L Hclass X n; induction n as [|n IH]; intros p Hp.
  - exact Hp.
  - simpl; apply logic_and_intro.
    + now apply global_consequence_classical.
    + now apply IH.
    + apply GC_nec; now apply IH.
Qed.

Definition global_finite_box_le_provable {AtomType}
    (L : modal_logic_set AtomType) (X : theory AtomType)
    (p : formula AtomType) : Prop :=
  exists Gamma : list (formula AtomType), exists n : nat,
    (forall q, In q Gamma -> X q) /\
    L (Imp (global_box_le n (logic_list_conj Gamma)) p).

Lemma global_consequence_finite_box_le_provable :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall X p,
    global_consequence L X p ->
    global_finite_box_le_provable L X p.
Proof.
  intros AtomType L Hnormal X p Hp.
  pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
  eapply (global_consequence_rec
    (P := fun Y q => global_finite_box_le_provable L Y q)).
  - intros Y q Hq.
    exists [], 0; split.
    + intros r Hr; contradiction.
    + change (L (Imp Top q)).
      apply logic_imply_intro; [exact Hclass | exact Hq].
  - intros Y q Hq.
    exists [q], 0; split.
    + intros r Hr; destruct Hr as [-> | Hr]; [exact Hq | contradiction].
    + change (L (Imp (And q Top) q)).
      now apply logic_and_elim_left_imp.
  - intros Y Z a b Hab IH_ab Ha IH_a.
    destruct IH_ab as [Gamma1 [n [HGamma1 Himp1]]].
    destruct IH_a as [Gamma2 [m [HGamma2 Himp2]]].
    exists (Gamma1 ++ Gamma2), (n + m); split.
    + intros r Hr; apply in_app_or in Hr; destruct Hr as [Hr | Hr].
      * left; now apply HGamma1.
      * right; now apply HGamma2.
    + pose proof
        (logic_list_conj_incl Hclass
          (Gamma := Gamma1) (Delta := Gamma1 ++ Gamma2)
          (fun r Hr => in_or_app Gamma1 Gamma2 r (or_introl Hr))) as Hlist1.
      pose proof
        (logic_list_conj_incl Hclass
          (Gamma := Gamma2) (Delta := Gamma1 ++ Gamma2)
          (fun r Hr => in_or_app Gamma1 Gamma2 r (or_intror Hr))) as Hlist2.
      pose proof
        (logic_global_box_le_regularity Hnormal (n + m) Hlist1) as Hreg1.
      pose proof
        (logic_global_box_le_regularity Hnormal (n + m) Hlist2) as Hreg2.
      pose proof
        (logic_global_box_le_depth_weaken Hclass
          (logic_list_conj Gamma1)
          (Nat.le_add_r n m)) as Hdepth1.
      assert (m <= n + m) as Hmn by lia.
      pose proof
        (logic_global_box_le_depth_weaken Hclass
          (logic_list_conj Gamma2) Hmn) as Hdepth2.
      pose proof (logic_imp_trans Hclass Hreg1 Hdepth1) as Hto1.
      pose proof (logic_imp_trans Hclass Hreg2 Hdepth2) as Hto2.
      pose proof (logic_imp_trans Hclass Hto1 Himp1) as HAimp.
      pose proof (logic_imp_trans Hclass Hto2 Himp2) as HAa.
      exact (logic_under_mp Hclass HAimp HAa).
  - intros Y q Hq IH.
    destruct IH as [Gamma [n [HGamma Himp]]].
    exists Gamma, (S n); split; [exact HGamma |].
    simpl.
    eapply logic_imp_trans; [exact Hclass | |].
    + now apply logic_and_elim_right_imp.
    + now apply logic_box_regularity.
  - intros Y q r.
    exists [], 0; split.
    + intros s Hs; contradiction.
    + change (L (Imp Top (Hilbert_imply_K q r))).
      apply logic_imply_intro; [exact Hclass |].
      exact (normal_logic_contains_K Hnormal (Kp_imply_K q r)).
  - intros Y q r s.
    exists [], 0; split.
    + intros t Ht; contradiction.
    + change (L (Imp Top (Hilbert_imply_S q r s))).
      apply logic_imply_intro; [exact Hclass |].
      exact (normal_logic_contains_K Hnormal (Kp_imply_S q r s)).
  - intros Y q r.
    exists [], 0; split.
    + intros s Hs; contradiction.
    + change (L (Imp Top (Hilbert_elim_contra q r))).
      apply logic_imply_intro; [exact Hclass |].
      exact (normal_logic_contains_K Hnormal (Kp_elim_contra q r)).
  - exact Hp.
Qed.

Lemma global_consequence_of_finite_box_le_provable :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall X p,
    global_finite_box_le_provable L X p ->
    global_consequence L X p.
Proof.
  intros AtomType L Hnormal X p [Gamma [n [HGamma Himp]]].
  pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
  eapply global_consequence_modus_ponens.
  - exact (GC_theorem Himp).
  - apply global_consequence_box_le_intro; [exact Hclass |].
    apply global_consequence_list_conj_intro; [exact Hclass |].
    intros q Hq; apply GC_context, HGamma, Hq.
Qed.

(** Jeřábek, Fact 2.7. *)
Theorem global_consequence_iff_finite_box_le_provable :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall X p,
    global_consequence L X p <->
    global_finite_box_le_provable L X p.
Proof.
  intros AtomType L Hnormal X p; split.
  - now apply global_consequence_finite_box_le_provable.
  - now apply global_consequence_of_finite_box_le_provable.
Qed.

(** The exact source-facing form of Jeřábek's Fact 2.7.  It uses
    singleton-normalized conjunction and the conjunction of the individual
    box iterates, rather than the cumulative implementation conveniences. *)
Definition global_finite_foundation_box_le_provable {AtomType}
    (L : modal_logic_set AtomType) (X : theory AtomType)
    (p : formula AtomType) : Prop :=
  exists Gamma : list (formula AtomType), exists n : nat,
    (forall q, In q Gamma -> X q) /\
    L (Imp (foundation_box_le n (logic_list_conj2 Gamma)) p).

Lemma global_consequence_finite_foundation_box_le_provable :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall X p,
    global_consequence L X p ->
    global_finite_foundation_box_le_provable L X p.
Proof.
  intros AtomType L Hnormal X p Hglobal.
  pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
  destruct
    (global_consequence_finite_box_le_provable Hnormal Hglobal)
    as [Gamma [n [HGamma Himp]]].
  exists Gamma, n; split; [exact HGamma |].
  eapply logic_imp_trans; [exact Hclass | |].
  - exact
      (logic_foundation_box_le_to_global Hnormal n
        (logic_list_conj2 Gamma)).
  - eapply logic_imp_trans; [exact Hclass | |exact Himp].
    exact
      (logic_global_box_le_regularity Hnormal n
        (logic_list_conj2_to_conj Hclass Gamma)).
Qed.

Lemma global_consequence_of_finite_foundation_box_le_provable :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall X p,
    global_finite_foundation_box_le_provable L X p ->
    global_consequence L X p.
Proof.
  intros AtomType L Hnormal X p [Gamma [n [HGamma Himp]]].
  pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
  assert (Hcurrent : global_finite_box_le_provable L X p).
  { exists Gamma, n; split; [exact HGamma |].
    eapply logic_imp_trans; [exact Hclass | |].
    - exact
        (logic_global_box_le_regularity Hnormal n
          (logic_list_conj_to_conj2 Hclass Gamma)).
    - eapply logic_imp_trans; [exact Hclass | |exact Himp].
      exact
        (logic_global_box_le_to_foundation Hnormal n
          (logic_list_conj2 Gamma)). }
  exact
    (@global_consequence_of_finite_box_le_provable
      AtomType L Hnormal X p Hcurrent).
Qed.

Theorem global_consequence_iff_finite_foundation_box_le_provable :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall X p,
    global_consequence L X p <->
    global_finite_foundation_box_le_provable L X p.
Proof.
  intros AtomType L Hnormal X p; split.
  - now apply global_consequence_finite_foundation_box_le_provable.
  - now apply global_consequence_of_finite_foundation_box_le_provable.
Qed.
