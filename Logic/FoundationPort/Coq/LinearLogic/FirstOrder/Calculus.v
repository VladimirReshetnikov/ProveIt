(** One-sided sequent calculus for first-order classical linear logic. *)

From Stdlib Require Import Lists.List Sorting.Permutation Vectors.Fin
  Program.Wf Program.Equality Lia.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.LinearLogic.FirstOrder Require Import Formula Rew.
From Foundation.Vorspiel.List Require Import Perm.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition llfo_sequent (L : language) := list (llfo_proposition L).

Definition llfo_sequent_is_quest {L} (Gamma : llfo_sequent L) : Prop :=
  forall phi, In phi Gamma -> llfo_is_quest phi.

Definition llfo_sequent_negative {L} (Gamma : llfo_sequent L) : Prop :=
  forall phi, In phi Gamma -> llfo_negative 0 phi.

Lemma llfo_sequent_is_quest_nil : forall L,
  llfo_sequent_is_quest (@nil (llfo_proposition L)).
Proof. intros L phi H. inversion H. Qed.

Lemma llfo_sequent_is_quest_cons : forall L (phi : llfo_proposition L) Gamma,
  llfo_sequent_is_quest (phi :: Gamma) <->
  llfo_is_quest phi /\ llfo_sequent_is_quest Gamma.
Proof.
  intros L phi Gamma. split.
  - intro H. split; [apply H; now left |].
    intros psi Hpsi. apply H. now right.
  - intros [Hphi HGamma] psi [<- | Hpsi]; auto.
Qed.

Lemma llfo_sequent_negative_nil : forall L,
  llfo_sequent_negative (@nil (llfo_proposition L)).
Proof. intros L phi H. inversion H. Qed.

Lemma llfo_sequent_negative_cons : forall L (phi : llfo_proposition L) Gamma,
  llfo_sequent_negative (phi :: Gamma) <->
  llfo_negative 0 phi /\ llfo_sequent_negative Gamma.
Proof.
  intros L phi Gamma. split.
  - intro H. split; [apply H; now left |].
    intros psi Hpsi. apply H. now right.
  - intros [Hphi HGamma] psi [<- | Hpsi]; auto.
Qed.

Definition llfo_quest_sequent {L} (Gamma : llfo_sequent L) : llfo_sequent L :=
  map LLQuest Gamma.

Definition llfo_shift_sequent {L} (Gamma : llfo_sequent L) : llfo_sequent L :=
  map llfo_shift Gamma.

Lemma llfo_quest_sequent_is_quest : forall L (Gamma : llfo_sequent L),
  llfo_sequent_is_quest (llfo_quest_sequent Gamma).
Proof.
  intros L Gamma phi Hphi. apply in_map_iff in Hphi.
  destruct Hphi as [psi [<- _]]. constructor.
Qed.

Unset Implicit Arguments.

Inductive llfo_derivation (L : language) : llfo_sequent L -> Type :=
| LLDIdentity : forall phi,
    llfo_derivation L [phi; llfo_neg phi]
| LLDCut : forall phi Gamma Delta,
    llfo_derivation L (phi :: Gamma) ->
    llfo_derivation L (llfo_neg phi :: Delta) ->
    llfo_derivation L (Gamma ++ Delta)
| LLDExchange : forall Gamma Delta,
    llfo_derivation L Gamma -> Permutation Gamma Delta ->
    llfo_derivation L Delta
| LLDOne : llfo_derivation L [LLOne]
| LLDFalsum : forall Gamma,
    llfo_derivation L Gamma -> llfo_derivation L (LLFalsum :: Gamma)
| LLDTensor : forall phi psi Gamma Delta,
    llfo_derivation L (phi :: Gamma) ->
    llfo_derivation L (psi :: Delta) ->
    llfo_derivation L (LLTensor phi psi :: Gamma ++ Delta)
| LLDPar : forall phi psi Gamma,
    llfo_derivation L (phi :: psi :: Gamma) ->
    llfo_derivation L (LLPar phi psi :: Gamma)
| LLDVerum : forall Gamma,
    llfo_derivation L (LLVerum :: Gamma)
| LLDWith : forall phi psi Gamma,
    llfo_derivation L (phi :: Gamma) ->
    llfo_derivation L (psi :: Gamma) ->
    llfo_derivation L (LLWith phi psi :: Gamma)
| LLDPlusLeft : forall phi psi Gamma,
    llfo_derivation L (psi :: Gamma) ->
    llfo_derivation L (LLPlus phi psi :: Gamma)
| LLDPlusRight : forall phi psi Gamma,
    llfo_derivation L (phi :: Gamma) ->
    llfo_derivation L (LLPlus phi psi :: Gamma)
| LLDOfCourse : forall phi Gamma,
    llfo_derivation L (phi :: Gamma) ->
    llfo_sequent_is_quest Gamma ->
    llfo_derivation L (LLBang phi :: Gamma)
| LLDWeakening : forall phi Gamma,
    llfo_derivation L Gamma ->
    llfo_derivation L (LLQuest phi :: Gamma)
| LLDDereliction : forall phi Gamma,
    llfo_derivation L (phi :: Gamma) ->
    llfo_derivation L (LLQuest phi :: Gamma)
| LLDContraction : forall phi Gamma,
    llfo_derivation L (LLQuest phi :: LLQuest phi :: Gamma) ->
    llfo_derivation L (LLQuest phi :: Gamma)
| LLDAll : forall (phi : llfo_semiproposition L 1) Gamma,
    llfo_derivation L (@llfo_free L 0 phi :: llfo_shift_sequent Gamma) ->
    llfo_derivation L (LLAll phi :: Gamma)
| LLDExs : forall (phi : llfo_semiproposition L 1) Gamma
    (t : syntactic_term L),
    llfo_derivation L
      (llfo_substitute (fun _ : Fin.t 1 => t) phi :: Gamma) ->
    llfo_derivation L (LLExs phi :: Gamma).

Set Implicit Arguments.

Arguments LLDIdentity {L} phi.
Arguments LLDCut {L phi Gamma Delta} _ _.
Arguments LLDExchange {L Gamma Delta} _ _.
Arguments LLDOne {L}.
Arguments LLDFalsum {L Gamma} _.
Arguments LLDTensor {L phi psi Gamma Delta} _ _.
Arguments LLDPar {L phi psi Gamma} _.
Arguments LLDVerum {L} Gamma.
Arguments LLDWith {L phi psi Gamma} _ _.
Arguments LLDPlusLeft {L phi psi Gamma} _.
Arguments LLDPlusRight {L phi psi Gamma} _.
Arguments LLDOfCourse {L phi Gamma} _ _.
Arguments LLDWeakening {L phi Gamma} _.
Arguments LLDDereliction {L phi Gamma} _.
Arguments LLDContraction {L phi Gamma} _.
Arguments LLDAll {L phi Gamma} _.
Arguments LLDExs {L phi Gamma} t _.

Definition llfo_proof {L} (phi : llfo_proposition L) : Type :=
  llfo_derivation L [phi].

Definition llfo_sentence_proof {L} (sigma : llfo_sentence L) : Type :=
  llfo_derivation L [llfo_emb (fun x : Empty_set => match x with end) sigma].

Definition llfo_derivable {L} (Gamma : llfo_sequent L) : Prop :=
  exists d : llfo_derivation L Gamma, True.

Definition llfo_derivation_cast {L Gamma Delta}
    (d : llfo_derivation L Gamma) (e : Gamma = Delta) :
    llfo_derivation L Delta :=
  match e with eq_refl => d end.

Definition llfo_rotate {L phi Gamma}
    (d : llfo_derivation L (phi :: Gamma)) :
    llfo_derivation L (Gamma ++ [phi]) :=
  @LLDExchange L (phi :: Gamma) (Gamma ++ [phi])
    d (Permutation_cons_append Gamma phi).

Definition llfo_inv_rotate {L phi Gamma}
    (d : llfo_derivation L (Gamma ++ [phi])) :
    llfo_derivation L (phi :: Gamma) :=
  @LLDExchange L (Gamma ++ [phi]) (phi :: Gamma)
    d (Permutation_sym (Permutation_cons_append Gamma phi)).

Fixpoint llfo_derivation_height {L Gamma}
    (d : llfo_derivation L Gamma) : nat :=
  match d with
  | LLDIdentity _ => 0
  | LLDCut d0 d1 => Nat.max (llfo_derivation_height d0)
      (llfo_derivation_height d1) + 1
  | LLDExchange d0 _ => llfo_derivation_height d0
  | LLDOne => 0
  | LLDFalsum d0 => llfo_derivation_height d0 + 1
  | LLDTensor d0 d1 => Nat.max (llfo_derivation_height d0)
      (llfo_derivation_height d1) + 1
  | LLDPar d0 => llfo_derivation_height d0 + 1
  | LLDVerum _ => 0
  | LLDWith d0 d1 => Nat.max (llfo_derivation_height d0)
      (llfo_derivation_height d1) + 1
  | LLDPlusLeft d0 => llfo_derivation_height d0 + 1
  | LLDPlusRight d0 => llfo_derivation_height d0 + 1
  | LLDOfCourse d0 _ => llfo_derivation_height d0 + 1
  | LLDWeakening d0 => llfo_derivation_height d0 + 1
  | LLDDereliction d0 => llfo_derivation_height d0 + 1
  | LLDContraction d0 => llfo_derivation_height d0 + 1
  | LLDAll d0 => llfo_derivation_height d0 + 1
  | LLDExs _ d0 => llfo_derivation_height d0 + 1
  end.

Lemma llfo_height_identity : forall L (phi : llfo_proposition L),
  llfo_derivation_height (LLDIdentity phi) = 0.
Proof. reflexivity. Qed.

Lemma llfo_height_cut : forall L (phi : llfo_proposition L) Gamma Delta
    (d1 : llfo_derivation L (phi :: Gamma))
    (d2 : llfo_derivation L (llfo_neg phi :: Delta)),
  llfo_derivation_height (LLDCut d1 d2) =
  Nat.max (llfo_derivation_height d1) (llfo_derivation_height d2) + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_exchange : forall L Gamma Delta
    (d : llfo_derivation L Gamma) (p : Permutation Gamma Delta),
  llfo_derivation_height (LLDExchange d p) = llfo_derivation_height d.
Proof. reflexivity. Qed.

Lemma llfo_height_one : forall L,
  llfo_derivation_height (@LLDOne L) = 0.
Proof. reflexivity. Qed.

Lemma llfo_height_falsum : forall L Gamma (d : llfo_derivation L Gamma),
  llfo_derivation_height (LLDFalsum d) = llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_tensor : forall L phi psi Gamma Delta
    (d1 : llfo_derivation L (phi :: Gamma))
    (d2 : llfo_derivation L (psi :: Delta)),
  llfo_derivation_height (LLDTensor d1 d2) =
  Nat.max (llfo_derivation_height d1) (llfo_derivation_height d2) + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_par : forall L phi psi Gamma
    (d : llfo_derivation L (phi :: psi :: Gamma)),
  llfo_derivation_height (LLDPar d) = llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_verum : forall L (Gamma : llfo_sequent L),
  llfo_derivation_height (LLDVerum Gamma) = 0.
Proof. reflexivity. Qed.

Lemma llfo_height_with : forall L phi psi Gamma
    (d1 : llfo_derivation L (phi :: Gamma))
    (d2 : llfo_derivation L (psi :: Gamma)),
  llfo_derivation_height (LLDWith d1 d2) =
  Nat.max (llfo_derivation_height d1) (llfo_derivation_height d2) + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_plus_left : forall L phi psi Gamma
    (d : llfo_derivation L (psi :: Gamma)),
  llfo_derivation_height (@LLDPlusLeft L phi psi Gamma d) =
  llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_plus_right : forall L phi psi Gamma
    (d : llfo_derivation L (phi :: Gamma)),
  llfo_derivation_height (@LLDPlusRight L phi psi Gamma d) =
  llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_of_course : forall L phi Gamma
    (d : llfo_derivation L (phi :: Gamma))
    (h : llfo_sequent_is_quest Gamma),
  llfo_derivation_height (LLDOfCourse d h) = llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_weakening : forall L phi Gamma
    (d : llfo_derivation L Gamma),
  llfo_derivation_height (@LLDWeakening L phi Gamma d) =
  llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_dereliction : forall L phi Gamma
    (d : llfo_derivation L (phi :: Gamma)),
  llfo_derivation_height (LLDDereliction d) = llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_contraction : forall L phi Gamma
    (d : llfo_derivation L (LLQuest phi :: LLQuest phi :: Gamma)),
  llfo_derivation_height (LLDContraction d) = llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_all : forall L (phi : llfo_semiproposition L 1) Gamma
    (d : llfo_derivation L (@llfo_free L 0 phi :: llfo_shift_sequent Gamma)),
  llfo_derivation_height (LLDAll d) = llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_exs : forall L (phi : llfo_semiproposition L 1) Gamma
    (t : syntactic_term L)
    (d : llfo_derivation L
      (llfo_substitute (fun _ : Fin.t 1 => t) phi :: Gamma)),
  llfo_derivation_height (LLDExs t d) = llfo_derivation_height d + 1.
Proof. reflexivity. Qed.

Lemma llfo_height_cast : forall L Gamma Delta (d : llfo_derivation L Gamma)
    (e : Gamma = Delta),
  llfo_derivation_height (llfo_derivation_cast d e) =
  llfo_derivation_height d.
Proof. intros L Gamma Delta d e. destruct e. reflexivity. Qed.

(** The primitive identity rule already ranges over arbitrary formulas, so the
    source's structural eta expansion has this shorter extensionally exact
    inhabitant. *)
Definition llfo_eta {L} (phi : llfo_proposition L) :
    llfo_derivation L [phi; llfo_neg phi] := LLDIdentity phi.

Definition llfo_identity_proof {L} (phi : llfo_proposition L) :
    llfo_proof (llfo_lolli phi phi) :=
  @LLDPar L (llfo_neg phi) phi [] (llfo_rotate (llfo_eta phi)).

Theorem llfo_modus_ponens : forall L (phi psi : llfo_proposition L),
  llfo_proof (llfo_lolli phi psi) ->
  llfo_proof phi -> llfo_proof psi.
Proof.
  intros L phi psi Himp Hphi.
  assert (Himp' : llfo_derivation L
      [llfo_neg (LLTensor phi (llfo_neg psi))]).
  { eapply llfo_derivation_cast; [exact Himp |].
    simpl. now rewrite llfo_neg_involutive. }
  assert (Hbridge : llfo_derivation L
      [LLTensor phi (llfo_neg psi); llfo_neg phi; psi]).
  { exact (@LLDTensor L phi (llfo_neg psi)
      [llfo_neg phi] [psi]
      (llfo_eta phi) (llfo_rotate (llfo_eta psi))). }
  exact (@LLDCut L phi [] [psi] Hphi
    (@LLDCut L (LLTensor phi (llfo_neg psi))
      [llfo_neg phi; psi] [] Hbridge Himp')).
Qed.

Corollary llfo_excluded_middle : forall L (phi : llfo_proposition L),
  llfo_derivable [LLPar phi (llfo_neg phi)].
Proof.
  intros L phi. exists (@LLDPar L phi (llfo_neg phi) [] (llfo_eta phi)).
  trivial.
Qed.

(** Exponentials mediate the additive choice needed by the classical
    disjunction branch of Girard's embedding. *)
Definition llfo_exp_comm {L} (phi psi : llfo_proposition L) :
    llfo_derivation L
      [LLTensor (LLBang (llfo_neg phi)) (LLBang (llfo_neg psi));
       LLQuest (LLPlus phi psi)].
Proof.
  assert (dphi : llfo_derivation L
      [LLBang (llfo_neg phi); LLQuest (LLPlus phi psi)]).
  { apply LLDOfCourse.
    - exact (llfo_rotate (LLDDereliction
        (@LLDPlusRight L phi psi [llfo_neg phi]
          (LLDIdentity phi)))).
    - apply llfo_sequent_is_quest_cons. split.
      + constructor.
      + apply llfo_sequent_is_quest_nil. }
  assert (dpsi : llfo_derivation L
      [LLBang (llfo_neg psi); LLQuest (LLPlus phi psi)]).
  { apply LLDOfCourse.
    - exact (llfo_rotate (LLDDereliction
        (@LLDPlusLeft L phi psi [llfo_neg psi]
          (LLDIdentity psi)))).
    - apply llfo_sequent_is_quest_cons. split.
      + constructor.
      + apply llfo_sequent_is_quest_nil. }
  pose (d := @LLDTensor L
    (LLBang (llfo_neg phi)) (LLBang (llfo_neg psi))
    [LLQuest (LLPlus phi psi)] [LLQuest (LLPlus phi psi)]
    dphi dpsi).
  exact (llfo_rotate (LLDContraction (llfo_rotate d))).
Defined.

Fixpoint llfo_add_quest_append_right {L} (Delta : llfo_sequent L) :
    forall Gamma,
    llfo_derivation L (Gamma ++ Delta) ->
    llfo_derivation L (Gamma ++ llfo_quest_sequent Delta) :=
  match Delta as Delta0 return forall Gamma,
      llfo_derivation L (Gamma ++ Delta0) ->
      llfo_derivation L (Gamma ++ llfo_quest_sequent Delta0) with
  | [] => fun Gamma d => d
  | nu :: Delta0 => fun Gamma d =>
      let dfront := @LLDExchange L
        (Gamma ++ nu :: Delta0) (nu :: Gamma ++ Delta0) d
        (Permutation_sym (Permutation_middle Gamma Delta0 nu)) in
      let dtail := @llfo_add_quest_append_right L Delta0
        (nu :: Gamma) dfront in
      @LLDExchange L
        (LLQuest nu :: Gamma ++ llfo_quest_sequent Delta0)
        (Gamma ++ LLQuest nu :: llfo_quest_sequent Delta0)
        (LLDDereliction dtail)
        (Permutation_middle Gamma (llfo_quest_sequent Delta0)
          (LLQuest nu))
  end.

Definition llfo_add_quest_tail {L phi Gamma}
    (d : llfo_derivation L (phi :: Gamma)) :
    llfo_derivation L (phi :: llfo_quest_sequent Gamma) :=
  @llfo_add_quest_append_right L Gamma [phi] d.

Lemma llfo_sequent_is_quest_singleton : forall L
    (phi : llfo_proposition L),
  llfo_sequent_is_quest [LLQuest phi].
Proof.
  intros. apply llfo_sequent_is_quest_cons. split; [constructor |].
  apply llfo_sequent_is_quest_nil.
Qed.

Definition llfo_of_negative_par_step {L} (nu mu : llfo_proposition L)
    (dnu : llfo_derivation L [llfo_neg (LLQuest nu); nu])
    (dmu : llfo_derivation L [llfo_neg (LLQuest mu); mu]) :
    llfo_derivation L
      [llfo_neg (LLQuest (LLPar nu mu)); LLPar nu mu].
Proof.
  assert (dtensor : llfo_derivation L
      [LLTensor (llfo_neg nu) (llfo_neg mu); nu; mu]).
  { exact (@LLDTensor L (llfo_neg nu) (llfo_neg mu) [nu] [mu]
      (llfo_rotate (llfo_eta nu)) (llfo_rotate (llfo_eta mu))). }
  assert (dpromoted : llfo_derivation L
      [LLBang (LLTensor (llfo_neg nu) (llfo_neg mu));
       LLQuest nu; LLQuest mu]).
  { apply LLDOfCourse.
    - exact (llfo_rotate (LLDDereliction
        (llfo_rotate (LLDDereliction (llfo_rotate dtensor))))).
    - apply llfo_sequent_is_quest_cons. split; [constructor |].
      apply llfo_sequent_is_quest_cons. split; [constructor |].
      apply llfo_sequent_is_quest_nil. }
  assert (dcut_nu : llfo_derivation L
      [LLQuest mu; LLBang (LLTensor (llfo_neg nu) (llfo_neg mu)); nu]).
  { exact (@LLDCut L (LLQuest nu)
      [LLQuest mu; LLBang (LLTensor (llfo_neg nu) (llfo_neg mu))]
      [nu] (llfo_rotate dpromoted) dnu). }
  assert (dcut_mu : llfo_derivation L
      [LLBang (LLTensor (llfo_neg nu) (llfo_neg mu)); nu; mu]).
  { exact (@LLDCut L (LLQuest mu)
      [LLBang (LLTensor (llfo_neg nu) (llfo_neg mu)); nu]
      [mu] dcut_nu dmu). }
  exact (llfo_rotate (LLDPar (llfo_rotate dcut_mu))).
Defined.

Definition llfo_of_negative_with_step {L} (nu mu : llfo_proposition L)
    (dnu : llfo_derivation L [llfo_neg (LLQuest nu); nu])
    (dmu : llfo_derivation L [llfo_neg (LLQuest mu); mu]) :
    llfo_derivation L
      [llfo_neg (LLQuest (LLWith nu mu)); LLWith nu mu].
Proof.
  assert (dpromoted_nu : llfo_derivation L
      [LLBang (LLPlus (llfo_neg nu) (llfo_neg mu)); LLQuest nu]).
  { apply LLDOfCourse.
    - exact (llfo_rotate (LLDDereliction (llfo_rotate
        (@LLDPlusRight L (llfo_neg nu) (llfo_neg mu) [nu]
          (llfo_rotate (llfo_eta nu)))))).
    - apply llfo_sequent_is_quest_cons. split; [constructor |].
      apply llfo_sequent_is_quest_nil. }
  assert (dpromoted_mu : llfo_derivation L
      [LLBang (LLPlus (llfo_neg nu) (llfo_neg mu)); LLQuest mu]).
  { apply LLDOfCourse.
    - exact (llfo_rotate (LLDDereliction (llfo_rotate
        (@LLDPlusLeft L (llfo_neg nu) (llfo_neg mu) [mu]
          (llfo_rotate (llfo_eta mu)))))).
    - apply llfo_sequent_is_quest_cons. split; [constructor |].
      apply llfo_sequent_is_quest_nil. }
  assert (dwith_nu : llfo_derivation L
      [nu; LLBang (LLPlus (llfo_neg nu) (llfo_neg mu))]).
  { exact (llfo_rotate (@LLDCut L (LLQuest nu)
      [LLBang (LLPlus (llfo_neg nu) (llfo_neg mu))] [nu]
      (llfo_rotate dpromoted_nu) dnu)). }
  assert (dwith_mu : llfo_derivation L
      [mu; LLBang (LLPlus (llfo_neg nu) (llfo_neg mu))]).
  { exact (llfo_rotate (@LLDCut L (LLQuest mu)
      [LLBang (LLPlus (llfo_neg nu) (llfo_neg mu))] [mu]
      (llfo_rotate dpromoted_mu) dmu)). }
  exact (llfo_rotate (LLDWith dwith_nu dwith_mu)).
Defined.

Definition llfo_of_negative_all_step {L}
    (nu : llfo_semiproposition L 1)
    (dnu : llfo_derivation L
      [llfo_neg (LLQuest (@llfo_free L 0 nu)); @llfo_free L 0 nu]) :
    llfo_derivation L
      [llfo_neg (LLQuest (LLAll nu)); LLAll nu].
Proof.
  assert (dinst : llfo_derivation L
      [llfo_substitute
         (fun _ : Fin.t 1 => Semiterm_fvar 0)
         (llfo_neg (llfo_shift nu));
       LLQuest (@llfo_free L 0 nu)]).
  { eapply llfo_derivation_cast.
    - exact (llfo_rotate (LLDDereliction
        (llfo_eta (@llfo_free L 0 nu)))).
    - simpl. f_equal. apply eq_sym.
      apply llfo_substitute_neg_shift_one_eq_neg_free. }
  assert (dpromoted : llfo_derivation L
      [LLBang (LLExs (llfo_neg (llfo_shift nu)));
       LLQuest (@llfo_free L 0 nu)]).
  { apply LLDOfCourse.
    - exact (@LLDExs L (llfo_neg (llfo_shift nu))
        [LLQuest (@llfo_free L 0 nu)] (Semiterm_fvar 0) dinst).
    - apply llfo_sequent_is_quest_cons. split; [constructor |].
      apply llfo_sequent_is_quest_nil. }
  assert (dcut : llfo_derivation L
      [LLBang (LLExs (llfo_neg (llfo_shift nu))); @llfo_free L 0 nu]).
  { exact (@LLDCut L (LLQuest (@llfo_free L 0 nu))
      [LLBang (LLExs (llfo_neg (llfo_shift nu)))]
      [@llfo_free L 0 nu] (llfo_rotate dpromoted) dnu). }
  assert (dall : llfo_derivation L
      [LLAll nu; LLBang (LLExs (llfo_neg nu))]).
  { apply LLDAll.
    eapply llfo_derivation_cast.
    - exact (llfo_rotate dcut).
    - change
        ([@llfo_free L 0 nu;
          LLBang (LLExs (llfo_neg (llfo_shift nu)))] =
         [@llfo_free L 0 nu;
          llfo_shift (LLBang (LLExs (llfo_neg nu)))]).
      f_equal. apply eq_sym.
      unfold llfo_shift. simpl. f_equal.
      rewrite llfo_rewrite_neg. f_equal.
      f_equal.
      f_equal.
      apply llfo_rewrite_ext, rew_q_shift. }
  exact (llfo_rotate dall).
Defined.

Lemma llfo_negative_rel_absurd : forall L X n k
    (R : language_rel L k) v,
  @llfo_negative L X n (LLRel R v) -> False.
Proof. intros L X n k R v H. inversion H. Qed.

Lemma llfo_negative_nrel_absurd : forall L X n k
    (R : language_rel L k) v,
  @llfo_negative L X n (LLNRel R v) -> False.
Proof. intros L X n k R v H. inversion H. Qed.

Lemma llfo_negative_one_absurd : forall L X n,
  @llfo_negative L X n LLOne -> False.
Proof. intros L X n H. inversion H. Qed.

Lemma llfo_negative_tensor_absurd : forall L X n
    (phi psi : llfo_semiformula L X n),
  llfo_negative n (LLTensor phi psi) -> False.
Proof. intros L X n phi psi H. inversion H. Qed.

Lemma llfo_negative_zero_absurd : forall L X n,
  @llfo_negative L X n LLZero -> False.
Proof. intros L X n H. inversion H. Qed.

Lemma llfo_negative_plus_absurd : forall L X n
    (phi psi : llfo_semiformula L X n),
  llfo_negative n (LLPlus phi psi) -> False.
Proof. intros L X n phi psi H. inversion H. Qed.

Lemma llfo_negative_bang_absurd : forall L X n
    (phi : llfo_semiformula L X n),
  llfo_negative n (LLBang phi) -> False.
Proof. intros L X n phi H. inversion H. Qed.

Lemma llfo_negative_exs_absurd : forall L X n
    (phi : llfo_semiformula L X (S n)),
  llfo_negative n (LLExs phi) -> False.
Proof. intros L X n phi H. inversion H. Qed.

(** Generalizing the recursive bridge over a rewrite into propositions keeps
    the binder index abstract.  This is the Coq replacement for eliminating
    a [Prop]-valued negativity witness into the Type-valued derivation. *)
Program Fixpoint llfo_of_negative_rewrite {L n}
    (w : rew L nat n nat 0) (nu : llfo_semiproposition L n)
    (hnu : llfo_negative n nu) {measure (llfo_complexity nu)} :
    llfo_derivation L
      [llfo_neg (LLQuest (llfo_rewrite w nu)); llfo_rewrite w nu] := _.
Next Obligation.
  destruct nu; simpl in *.
  - destruct (llfo_negative_rel_absurd hnu).
  - destruct (llfo_negative_nrel_absurd hnu).
  - destruct (llfo_negative_one_absurd hnu).
  - exact (llfo_rotate (LLDFalsum
      (@LLDOfCourse L LLOne [] LLDOne
        (@llfo_sequent_is_quest_nil L)))).
  - destruct (llfo_negative_tensor_absurd hnu).
  - apply llfo_of_negative_par_step.
    + eapply llfo_of_negative_rewrite.
      * exact (proj1 (proj1 (llfo_negative_par_iff _ _) hnu)).
      * simpl. lia.
    + eapply llfo_of_negative_rewrite.
      * exact (proj2 (proj1 (llfo_negative_par_iff _ _) hnu)).
      * simpl. lia.
  - exact (llfo_rotate (LLDVerum [LLBang LLZero])).
  - destruct (llfo_negative_zero_absurd hnu).
  - apply llfo_of_negative_with_step.
    + eapply llfo_of_negative_rewrite.
      * exact (proj1 (proj1 (llfo_negative_with_iff _ _) hnu)).
      * simpl. lia.
    + eapply llfo_of_negative_rewrite.
      * exact (proj2 (proj1 (llfo_negative_with_iff _ _) hnu)).
      * simpl. lia.
  - destruct (llfo_negative_plus_absurd hnu).
  - destruct (llfo_negative_bang_absurd hnu).
  - exact (@LLDOfCourse L
      (llfo_neg (LLQuest (llfo_rewrite w nu)))
      [LLQuest (llfo_rewrite w nu)]
      (llfo_rotate (llfo_eta (LLQuest (llfo_rewrite w nu))))
      (@llfo_sequent_is_quest_singleton L (llfo_rewrite w nu))).
  - apply llfo_of_negative_all_step.
    eapply llfo_derivation_cast.
    + eapply llfo_of_negative_rewrite
        with (w := rew_comp (@rew_free L 0) (rew_q w)).
      * now apply (proj1 (llfo_negative_all_iff _) hnu).
      * simpl. lia.
    + rewrite llfo_rewrite_comp. reflexivity.
  - destruct (llfo_negative_exs_absurd hnu).
Defined.

Definition llfo_of_negative {L} (nu : llfo_proposition L)
    (hnu : llfo_negative 0 nu) :
    llfo_derivation L [llfo_neg (LLQuest nu); nu].
Proof.
  eapply llfo_derivation_cast.
  - exact (@llfo_of_negative_rewrite L 0 rew_id nu hnu).
  - now rewrite llfo_rewrite_id.
Defined.

Definition llfo_remove_quest {L nu Gamma}
    (hnu : llfo_negative 0 nu)
    (d : llfo_derivation L (LLQuest nu :: Gamma)) :
    llfo_derivation L (nu :: Gamma) :=
  llfo_inv_rotate (@LLDCut L (LLQuest nu) Gamma [nu]
    d (llfo_of_negative hnu)).

Definition llfo_negative_weakening {L nu Gamma}
    (hnu : llfo_negative 0 nu) (d : llfo_derivation L Gamma) :
    llfo_derivation L (nu :: Gamma) :=
  llfo_remove_quest hnu (@LLDWeakening L nu Gamma d).

Definition llfo_negative_contraction {L nu Gamma}
    (hnu : llfo_negative 0 nu)
    (d : llfo_derivation L (nu :: nu :: Gamma)) :
    llfo_derivation L (nu :: Gamma).
Proof.
  assert (dquests : llfo_derivation L
      (LLQuest nu :: LLQuest nu :: Gamma)).
  { eapply LLDExchange.
    - exact (LLDDereliction (llfo_rotate (LLDDereliction d))).
    - apply perm_skip.
      apply Permutation_sym, Permutation_cons_append. }
  exact (llfo_remove_quest hnu (LLDContraction dquests)).
Defined.

Fixpoint llfo_remove_quest_append_right {L} (Delta : llfo_sequent L) :
    forall Gamma,
    llfo_derivation L (Gamma ++ llfo_quest_sequent Delta) ->
    llfo_sequent_negative Delta ->
    llfo_derivation L (Gamma ++ Delta) :=
  match Delta as Delta0 return forall Gamma,
      llfo_derivation L (Gamma ++ llfo_quest_sequent Delta0) ->
      llfo_sequent_negative Delta0 ->
      llfo_derivation L (Gamma ++ Delta0) with
  | [] => fun Gamma d _ => d
  | nu :: Delta0 => fun Gamma d hDelta =>
      let hparts := proj1 (llfo_sequent_negative_cons nu Delta0) hDelta in
      let dfront := @LLDExchange L
        (Gamma ++ LLQuest nu :: llfo_quest_sequent Delta0)
        (LLQuest nu :: Gamma ++ llfo_quest_sequent Delta0) d
        (Permutation_sym
          (Permutation_middle Gamma (llfo_quest_sequent Delta0)
            (LLQuest nu))) in
      let dtail := @llfo_remove_quest_append_right L Delta0
        (LLQuest nu :: Gamma) dfront (proj2 hparts) in
      @LLDExchange L
        (nu :: Gamma ++ Delta0) (Gamma ++ nu :: Delta0)
        (llfo_remove_quest (proj1 hparts) dtail)
        (Permutation_middle Gamma Delta0 nu)
  end.

Definition llfo_remove_quest_tail {L phi Gamma}
    (d : llfo_derivation L (phi :: llfo_quest_sequent Gamma))
    (hGamma : llfo_sequent_negative Gamma) :
    llfo_derivation L (phi :: Gamma) :=
  @llfo_remove_quest_append_right L Gamma [phi] d hGamma.

Definition llfo_negative_of_course {L phi Gamma}
    (d : llfo_derivation L (phi :: Gamma))
    (hGamma : llfo_sequent_negative Gamma) :
    llfo_derivation L (LLBang phi :: Gamma) :=
  llfo_remove_quest_tail
    (@LLDOfCourse L phi (llfo_quest_sequent Gamma)
      (llfo_add_quest_tail d) (@llfo_quest_sequent_is_quest L Gamma))
    hGamma.

Fixpoint llfo_negative_comp_subset {L Gamma Delta}
    (c : @list_comp_subset (llfo_proposition L) Gamma Delta) :
    llfo_derivation L Gamma ->
    llfo_sequent_negative Delta ->
    llfo_derivation L Delta :=
  match c as c0 in list_comp_subset Gamma0 Delta0 return
      llfo_derivation L Gamma0 ->
      llfo_sequent_negative Delta0 ->
      llfo_derivation L Delta0 with
  | comp_subset_refl xs => fun d _ => d
  | @comp_subset_perm _ xs ys zs c0 p => fun d hzs =>
      let hys : llfo_sequent_negative ys := fun phi hphi =>
        hzs phi (@Permutation_in _ ys zs phi p hphi) in
      @LLDExchange L ys zs (llfo_negative_comp_subset c0 d hys) p
  | @comp_subset_add _ xs ys phi c0 => fun d hcons =>
      let hp := proj1 (llfo_sequent_negative_cons phi ys) hcons in
      llfo_negative_weakening (proj1 hp)
        (llfo_negative_comp_subset c0 d (proj2 hp))
  | @comp_subset_double _ xs ys phi c0 => fun d hcons =>
      let hp := proj1 (llfo_sequent_negative_cons phi ys) hcons in
      let hdouble : llfo_sequent_negative (phi :: phi :: ys) :=
        proj2 (llfo_sequent_negative_cons phi (phi :: ys))
          (conj (proj1 hp) hcons) in
      llfo_negative_contraction (proj1 hp)
        (llfo_negative_comp_subset c0 d hdouble)
  end.

Definition llfo_negative_wk {L}
    (eq_dec : forall phi psi : llfo_proposition L,
      {phi = psi} + {phi <> psi})
    {Gamma Delta} (d : llfo_derivation L Gamma)
    (hsub : incl Gamma Delta)
    (hDelta : llfo_sequent_negative Delta) :
    llfo_derivation L Delta :=
  llfo_negative_comp_subset
    (@list_incl_to_comp_subset (llfo_proposition L)
      eq_dec Gamma Delta hsub) d hDelta.
