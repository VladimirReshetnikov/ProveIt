(**
  Decoding and range theorems for bootstrapped sequents and proofs.

  This module begins the converse direction to [Proof.Typed].  It first
  isolates the representation-independent fact needed by every rule case:
  a raw formula-set context is exactly a pointwise quotation of some typed
  sequent.  An executable option decoder realizes the witness.
*)

From Stdlib Require Import Lists.List Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Calculus2 Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import Basic Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import
  Basic Functions Typed Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax Require Import Theory.
From Foundation.FirstOrder.Bootstrapping.Syntax.Proof Require Import Basic Typed.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Theorem boot_is_formula_set_has_quote : forall L EL Gamma,
  @boot_is_formula_set L EL Gamma ->
  exists Delta : first_order_sequent L,
    map (boot_typed_formula_quote EL) Delta = Gamma.
Proof.
  intros L EL Gamma H. induction H as [|code Gamma Hcode Hset IH].
  - exists []. reflexivity.
  - destruct (boot_is_semiformula_has_quote Hcode) as [p Hp].
    destruct IH as [Delta HDelta].
    exists (p :: Delta). simpl. unfold boot_typed_formula_quote at 1.
    now rewrite Hp, HDelta.
Qed.

Theorem boot_is_formula_set_quote_iff : forall L EL Gamma,
  @boot_is_formula_set L EL Gamma <->
  exists Delta : first_order_sequent L,
    map (boot_typed_formula_quote EL) Delta = Gamma.
Proof.
  intros; split.
  - apply boot_is_formula_set_has_quote.
  - intros [Delta <-]. apply boot_is_formula_set_quote.
Qed.

Lemma boot_formula_set_quote_unique : forall L EL
    (Gamma Delta : first_order_sequent L),
  map (boot_typed_formula_quote EL) Gamma =
  map (boot_typed_formula_quote EL) Delta -> Gamma = Delta.
Proof.
  intros L EL Gamma Delta H.
  apply boot_sequent_quote_injective with (EL := EL).
  unfold boot_sequent_quote. now rewrite H.
Qed.

Lemma boot_formula_set_quote_member : forall L EL
    (Delta : first_order_sequent L) code,
  In code (map (boot_typed_formula_quote EL) Delta) ->
  exists p : proposition L,
    In p Delta /\ boot_typed_formula_quote EL p = code.
Proof.
  intros L EL Delta code H.
  apply in_map_iff in H. destruct H as [p [Hcode Hp]].
  exists p. split; [assumption|now symmetry].
Qed.

Fixpoint boot_sequent_decode {L} (EL : language_encodable L)
    (Gamma : list nat) : option (first_order_sequent L) :=
  match Gamma with
  | [] => Some []
  | code :: rest =>
      match semiformula_decode EL boot_nat_encoding 0 code,
            boot_sequent_decode EL rest with
      | Some p, Some Delta => Some (p :: Delta)
      | _, _ => None
      end
  end.

Theorem boot_sequent_decode_quote : forall L EL
    (Delta : first_order_sequent L),
  boot_sequent_decode EL (map (boot_typed_formula_quote EL) Delta) =
  Some Delta.
Proof.
  intros L EL Delta. induction Delta as [|p Delta IH]; simpl.
  - reflexivity.
  - unfold boot_typed_formula_quote at 1.
    now rewrite semiformula_decode_code, IH.
Qed.

Theorem boot_sequent_decode_complete : forall L EL Gamma,
  @boot_is_formula_set L EL Gamma ->
  exists Delta : first_order_sequent L,
    boot_sequent_decode EL Gamma = Some Delta /\
    map (boot_typed_formula_quote EL) Delta = Gamma.
Proof.
  intros L EL Gamma H.
  destruct (boot_is_formula_set_has_quote H) as [Delta <-].
  exists Delta. split; [apply boot_sequent_decode_quote|reflexivity].
Qed.

Theorem boot_sequent_decode_some_iff : forall L EL Gamma Delta,
  @boot_is_formula_set L EL Gamma ->
  (@boot_sequent_decode L EL Gamma = Some Delta <->
   map (boot_typed_formula_quote EL) Delta = Gamma).
Proof.
  intros L EL Gamma Delta Hset.
  destruct (boot_is_formula_set_has_quote Hset) as [Theta HTheta].
  split.
  - intro Hdecode. rewrite <- HTheta in Hdecode.
    rewrite boot_sequent_decode_quote in Hdecode. injection Hdecode as ->.
    exact HTheta.
  - intro Hquote. rewrite <- Hquote. apply boot_sequent_decode_quote.
Qed.

(** Every recognized proof therefore has a uniquely decodable typed
    consequence sequent, independently of reconstruction of its rule tree. *)
Theorem boot_derivation_code_typed_consequence : forall L EL T ET Gamma code,
  @boot_derivation_code L EL T ET Gamma code ->
  exists Delta : first_order_sequent L,
    boot_sequent_decode EL Gamma = Some Delta /\
    boot_proof_conseq code = boot_sequent_quote EL Delta.
Proof.
  intros L EL T ET Gamma code H.
  destruct (boot_sequent_decode_complete
    (boot_derivation_code_formula_set H)) as [Delta [Hdecode Hquote]].
  exists Delta. split; [assumption|].
  rewrite (boot_derivation_code_conseq H).
  unfold boot_sequent_quote. now rewrite Hquote.
Qed.

(** * Recursive soundness *)

Theorem boot_derivation_code_sound : forall L EL T ET Gamma code,
  @boot_derivation_code L EL T ET Gamma code ->
  exists Delta : first_order_sequent L,
  exists d : first_order_derivation2 L T Delta,
    map (boot_typed_formula_quote EL) Delta = Gamma /\
    @boot_derivation2_quote L T Delta EL ET d = code.
Proof.
  intros L EL T ET Gamma code H.
  induction H as
      [Gamma p Hset Hp Hnp
      |Gamma Hset Hv
      |Gamma p q dp dq Hset Hand Hd1 IH1 Hd2 IH2
      |Gamma p q d Hset Hor Hd IH
      |Gamma p d Hset Hall Hpform Hd IH
      |Gamma p t d Hset Hex Hpform Hterm Hd IH
      |RawDelta Gamma d Hset Hsub Hd IH
      |Gamma d Hset Hd IH
      |Gamma p d1 d2 Hset Hpform Hd1 IH1 Hd2 IH2
      |Gamma p Hset Hp Hclass].
  - destruct (boot_is_formula_set_has_quote Hset) as [Delta HDelta].
    rewrite <- HDelta in Hp, Hnp.
    destruct (boot_formula_set_quote_member Hp) as [phi [Hphi Hquote]].
    assert (Hneg : In (semiformula_neg phi) Delta).
    { apply (proj1 (boot_sequent_quote_member_iff EL Delta _)).
      change (In (boot_typed_formula_quote EL
        (boot_typed_formula_neg phi))
        (map (boot_typed_formula_quote EL) Delta)).
      rewrite boot_typed_formula_quote_neg, Hquote. exact Hnp. }
    exists Delta.
    exists (FOD2Closed phi
      (generic_list_member_of_list_in Hphi)
      (generic_list_member_of_list_in Hneg)).
    split; [exact HDelta|].
    cbn [boot_derivation2_quote]. unfold boot_sequent_quote.
    now rewrite HDelta, Hquote.
  - destruct (boot_is_formula_set_has_quote Hset) as [Delta HDelta].
    assert (Hverum : In (Semiformula_verum 0) Delta).
    { apply (proj1 (boot_sequent_quote_member_iff EL Delta _)).
      rewrite HDelta. exact Hv. }
    exists Delta.
    exists (FOD2Verum (generic_list_member_of_list_in Hverum)).
    split; [exact HDelta|].
    cbn [boot_derivation2_quote]. unfold boot_sequent_quote.
    now rewrite HDelta.
  - destruct IH1 as [Delta1 [typed1 [HDelta1 Hcode1]]].
    destruct IH2 as [Delta2 [typed2 [HDelta2 Hcode2]]].
    pose proof (boot_derivation_code_formula_set Hd1) as Hchild1.
    pose proof (boot_derivation_code_formula_set Hd2) as Hchild2.
    apply boot_is_formula_set_cons_iff in Hchild1.
    apply boot_is_formula_set_cons_iff in Hchild2.
    destruct Hchild1 as [Hpcode _]. destruct Hchild2 as [Hqcode _].
    destruct (boot_is_semiformula_has_quote Hpcode) as [phi Hphi].
    destruct (boot_is_semiformula_has_quote Hqcode) as [psi Hpsi].
    destruct (boot_is_formula_set_has_quote Hset) as [Delta HDelta].
    assert (Hmember : In (Semiformula_and phi psi) Delta).
    { apply (proj1 (boot_sequent_quote_member_iff EL Delta _)). rewrite HDelta.
      change (In (boot_qq_and
        (boot_typed_formula_quote EL phi)
        (boot_typed_formula_quote EL psi)) Gamma).
      unfold boot_typed_formula_quote. now rewrite Hphi, Hpsi. }
    assert (Heq1 : Delta1 = phi :: Delta).
    { apply boot_formula_set_quote_unique with (EL := EL).
      rewrite HDelta1. simpl. unfold boot_typed_formula_quote at 1.
      now rewrite Hphi, HDelta. }
    assert (Heq2 : Delta2 = psi :: Delta).
    { apply boot_formula_set_quote_unique with (EL := EL).
      rewrite HDelta2. simpl. unfold boot_typed_formula_quote at 1.
      now rewrite Hpsi, HDelta. }
    assert (HC1 : @boot_derivation2_quote L T (phi :: Delta) EL ET
        (first_order_derivation2_cast typed1 Heq1) = dp).
    { rewrite boot_derivation2_quote_cast. exact Hcode1. }
    assert (HC2 : @boot_derivation2_quote L T (psi :: Delta) EL ET
        (first_order_derivation2_cast typed2 Heq2) = dq).
    { rewrite boot_derivation2_quote_cast. exact Hcode2. }
    exists Delta.
    exists (FOD2And (generic_list_member_of_list_in Hmember)
      (first_order_derivation2_cast typed1 Heq1)
      (first_order_derivation2_cast typed2 Heq2)).
    split; [exact HDelta|].
    change (boot_and_intro (boot_sequent_quote EL Delta)
      (boot_typed_formula_quote EL phi)
      (boot_typed_formula_quote EL psi)
      (@boot_derivation2_quote L T (phi :: Delta) EL ET
        (first_order_derivation2_cast typed1 Heq1))
      (@boot_derivation2_quote L T (psi :: Delta) EL ET
        (first_order_derivation2_cast typed2 Heq2)) =
      boot_and_intro (boot_nat_list_code Gamma) p q dp dq).
    unfold boot_sequent_quote.
    rewrite HDelta. unfold boot_typed_formula_quote at 1 2.
    rewrite Hphi, Hpsi.
    now rewrite HC1, HC2.
  - destruct IH as [Delta1 [typed [HDelta1 Hcode]]].
    pose proof (boot_derivation_code_formula_set Hd) as Hchild.
    apply boot_is_formula_set_cons_iff in Hchild.
    destruct Hchild as [Hpcode Hrest].
    apply boot_is_formula_set_cons_iff in Hrest.
    destruct Hrest as [Hqcode _].
    destruct (boot_is_semiformula_has_quote Hpcode) as [phi Hphi].
    destruct (boot_is_semiformula_has_quote Hqcode) as [psi Hpsi].
    destruct (boot_is_formula_set_has_quote Hset) as [Delta HDelta].
    assert (Hmember : In (Semiformula_or phi psi) Delta).
    { apply (proj1 (boot_sequent_quote_member_iff EL Delta _)). rewrite HDelta.
      change (In (boot_qq_or
        (boot_typed_formula_quote EL phi)
        (boot_typed_formula_quote EL psi)) Gamma).
      unfold boot_typed_formula_quote. now rewrite Hphi, Hpsi. }
    assert (Heq : Delta1 = phi :: psi :: Delta).
    { apply boot_formula_set_quote_unique with (EL := EL).
      rewrite HDelta1. simpl. unfold boot_typed_formula_quote at 1 2.
      now rewrite Hphi, Hpsi, HDelta. }
    assert (HC : @boot_derivation2_quote L T (phi :: psi :: Delta) EL ET
        (first_order_derivation2_cast typed Heq) = d).
    { rewrite boot_derivation2_quote_cast. exact Hcode. }
    exists Delta.
    exists (FOD2Or (generic_list_member_of_list_in Hmember)
      (first_order_derivation2_cast typed Heq)).
    split; [exact HDelta|].
    change (boot_or_intro (boot_sequent_quote EL Delta)
      (boot_typed_formula_quote EL phi)
      (boot_typed_formula_quote EL psi)
      (@boot_derivation2_quote L T (phi :: psi :: Delta) EL ET
        (first_order_derivation2_cast typed Heq)) =
      boot_or_intro (boot_nat_list_code Gamma) p q d).
    unfold boot_sequent_quote.
    rewrite HDelta. unfold boot_typed_formula_quote at 1 2.
    rewrite Hphi, Hpsi.
    now rewrite HC.
  - destruct (boot_is_semiformula_has_quote Hpform) as [phi Hphi].
    destruct IH as [Delta1 [typed [HDelta1 Hcode]]].
    destruct (boot_is_formula_set_has_quote Hset) as [Delta HDelta].
    assert (Hmember : In (Semiformula_all phi) Delta).
    { apply (proj1 (boot_sequent_quote_member_iff EL Delta _)). rewrite HDelta.
      change (In (boot_qq_all (boot_typed_formula_quote EL phi)) Gamma).
      unfold boot_typed_formula_quote. now rewrite Hphi. }
    assert (Heq : Delta1 =
        @semiformula_free L 0 phi :: first_order_sequent_shift Delta).
    { pose proof (boot_formula_free_code_quote EL phi) as Hfree.
      unfold boot_typed_formula_quote in Hfree.
      apply boot_formula_set_quote_unique with (EL := EL).
      rewrite HDelta1. simpl. rewrite <- Hphi, Hfree.
      rewrite boot_sequent_shift_quote. now rewrite HDelta. }
    assert (HC : @boot_derivation2_quote L T
        (@semiformula_free L 0 phi :: first_order_sequent_shift Delta)
        EL ET (first_order_derivation2_cast typed Heq) = d).
    { rewrite boot_derivation2_quote_cast. exact Hcode. }
    exists Delta.
    exists (FOD2All (generic_list_member_of_list_in Hmember)
      (first_order_derivation2_cast typed Heq)).
    split; [exact HDelta|].
    change (boot_all_intro (boot_sequent_quote EL Delta)
      (boot_typed_formula_quote EL phi)
      (@boot_derivation2_quote L T
        (@semiformula_free L 0 phi :: first_order_sequent_shift Delta)
        EL ET (first_order_derivation2_cast typed Heq)) =
      boot_all_intro (boot_nat_list_code Gamma) p d).
    unfold boot_sequent_quote.
    rewrite HDelta. unfold boot_typed_formula_quote at 1.
    rewrite Hphi. now rewrite HC.
  - destruct (boot_is_semiformula_has_quote Hpform) as [phi Hphi].
    destruct (boot_is_semiterm_has_quote Hterm) as [term Htermq].
    destruct IH as [Delta1 [typed [HDelta1 Hcode]]].
    destruct (boot_is_formula_set_has_quote Hset) as [Delta HDelta].
    assert (Hmember : In (Semiformula_exists phi) Delta).
    { apply (proj1 (boot_sequent_quote_member_iff EL Delta _)). rewrite HDelta.
      change (In (boot_qq_exists (boot_typed_formula_quote EL phi)) Gamma).
      unfold boot_typed_formula_quote. now rewrite Hphi. }
    assert (Hdecode : semiterm_decode EL boot_nat_encoding 0 t = Some term).
    { rewrite <- Htermq. apply semiterm_decode_code. }
    assert (Heq : Delta1 =
        semiformula_substitute (fun _ : Fin.t 1 => term) phi :: Delta).
    { apply boot_formula_set_quote_unique with (EL := EL).
      rewrite HDelta1. simpl. rewrite Hdecode.
      unfold boot_typed_formula_quote at 1.
      rewrite <- Hphi, boot_formula_subst_code_quote, HDelta. reflexivity. }
    assert (HC : @boot_derivation2_quote L T
        (semiformula_substitute (fun _ : Fin.t 1 => term) phi :: Delta)
        EL ET (first_order_derivation2_cast typed Heq) = d).
    { rewrite boot_derivation2_quote_cast. exact Hcode. }
    exists Delta.
    exists (FOD2Exists (generic_list_member_of_list_in Hmember) term
      (first_order_derivation2_cast typed Heq)).
    split; [exact HDelta|].
    change (boot_exists_intro (boot_sequent_quote EL Delta)
      (boot_typed_formula_quote EL phi) (boot_typed_quote EL term)
      (@boot_derivation2_quote L T
        (semiformula_substitute (fun _ : Fin.t 1 => term) phi :: Delta)
        EL ET (first_order_derivation2_cast typed Heq)) =
      boot_exists_intro (boot_nat_list_code Gamma) p t d).
    unfold boot_sequent_quote.
    rewrite HDelta. unfold boot_typed_formula_quote at 1,
      boot_typed_quote. rewrite Hphi, Htermq.
    now rewrite HC.
  - destruct IH as [Delta [typed [HDelta Hcode]]].
    destruct (boot_is_formula_set_has_quote Hset) as [Target HTarget].
    assert (Hincl : GenericCalculus.generic_list_subset Delta Target).
    { intros phi Hphi. apply generic_list_member_of_list_in.
      apply (proj1 (boot_sequent_quote_member_iff EL Target _)). rewrite HTarget.
      apply Hsub. rewrite <- HDelta.
      apply (proj2 (boot_sequent_quote_member_iff EL Delta _)).
      now apply boot_list_in_of_generic_list_member. }
    exists Target. exists (FOD2Weakening typed Hincl).
    split; [exact HTarget|].
    cbn [boot_derivation2_quote]. unfold boot_sequent_quote.
    now rewrite HTarget, Hcode.
  - destruct IH as [Delta [typed [HDelta Hcode]]].
    exists (first_order_sequent_shift Delta). exists (FOD2Shift typed).
    split.
    + rewrite boot_sequent_shift_quote. now rewrite HDelta.
    + cbn [boot_derivation2_quote]. rewrite Hcode.
      unfold boot_sequent_quote. rewrite boot_sequent_shift_quote, HDelta.
      reflexivity.
  - destruct (boot_is_semiformula_has_quote Hpform) as [phi Hphi].
    destruct IH1 as [Delta1 [typed1 [HDelta1 Hcode1]]].
    destruct IH2 as [Delta2 [typed2 [HDelta2 Hcode2]]].
    destruct (boot_is_formula_set_has_quote Hset) as [Delta HDelta].
    assert (Heq1 : Delta1 = phi :: Delta).
    { apply boot_formula_set_quote_unique with (EL := EL).
      rewrite HDelta1. simpl. unfold boot_typed_formula_quote at 1.
      now rewrite Hphi, HDelta. }
    assert (Hnegq : boot_formula_neg_code EL 0 p =
        boot_typed_formula_quote EL (semiformula_neg phi)).
    { rewrite <- Hphi. symmetry.
      change (boot_typed_formula_quote EL (boot_typed_formula_neg phi) =
        boot_formula_neg_code EL 0 (boot_typed_formula_quote EL phi)).
      apply boot_typed_formula_quote_neg. }
    assert (Heq2 : Delta2 = semiformula_neg phi :: Delta).
    { apply boot_formula_set_quote_unique with (EL := EL).
      rewrite HDelta2. simpl. now rewrite Hnegq, HDelta. }
    assert (HC1 : @boot_derivation2_quote L T (phi :: Delta) EL ET
        (first_order_derivation2_cast typed1 Heq1) = d1).
    { rewrite boot_derivation2_quote_cast. exact Hcode1. }
    assert (HC2 : @boot_derivation2_quote L T
        (semiformula_neg phi :: Delta) EL ET
        (first_order_derivation2_cast typed2 Heq2) = d2).
    { rewrite boot_derivation2_quote_cast. exact Hcode2. }
    exists Delta.
    exists (FOD2Cut
      (first_order_derivation2_cast typed1 Heq1)
      (first_order_derivation2_cast typed2 Heq2)).
    split; [exact HDelta|].
    change (boot_cut_rule (boot_sequent_quote EL Delta)
      (boot_typed_formula_quote EL phi)
      (@boot_derivation2_quote L T (phi :: Delta) EL ET
        (first_order_derivation2_cast typed1 Heq1))
      (@boot_derivation2_quote L T (semiformula_neg phi :: Delta) EL ET
        (first_order_derivation2_cast typed2 Heq2)) =
      boot_cut_rule (boot_nat_list_code Gamma) p d1 d2).
    unfold boot_sequent_quote.
    rewrite HDelta. unfold boot_typed_formula_quote at 1. rewrite Hphi.
    now rewrite HC1, HC2.
  - destruct (boot_is_formula_set_has_quote Hset) as [Delta HDelta].
    apply boot_theory_classifier_formula_spec in Hclass.
    destruct Hclass as [sigma [HT Hsigma]].
    rewrite <- HDelta in Hp.
    rewrite <- Hsigma in Hp.
    apply boot_sequent_quote_member_iff in Hp.
    exists Delta.
    exists (FOD2Axiom sigma HT (generic_list_member_of_list_in Hp)).
    split; [exact HDelta|].
    cbn [boot_derivation2_quote]. unfold boot_sequent_quote.
    now rewrite HDelta, Hsigma.
Qed.

Corollary boot_derivation_sound : forall L EL T ET code,
  @boot_derivation L EL T ET code ->
  exists Delta : first_order_sequent L,
  exists d : first_order_derivation2 L T Delta,
    @boot_derivation2_quote L T Delta EL ET d = code.
Proof.
  intros L EL T ET code [Gamma H].
  destruct (boot_derivation_code_sound H) as [Delta [d [_ Hcode]]].
  now exists Delta, d.
Qed.

Theorem boot_proof_sound : forall L EL T ET code formula,
  @boot_proof L EL T ET code formula ->
  exists p : proposition L,
  exists d : first_order_derivation2 L T [p],
    boot_typed_formula_quote EL p = formula /\
    @boot_derivation2_quote L T [p] EL ET d = code.
Proof.
  intros L EL T ET code formula H.
  pose proof (boot_derivation_code_formula_set H) as Hset.
  apply boot_is_formula_set_cons_iff in Hset.
  destruct Hset as [Hformula _].
  destruct (boot_is_semiformula_has_quote Hformula) as [p Hp].
  destruct (boot_derivation_code_sound H) as [Delta [d [HDelta Hcode]]].
  assert (Heq : Delta = [p]).
  { apply boot_formula_set_quote_unique with (EL := EL).
    rewrite HDelta. simpl. unfold boot_typed_formula_quote at 1.
    now rewrite Hp. }
  exists p.
  exists (first_order_derivation2_cast d Heq).
  split.
  - unfold boot_typed_formula_quote. exact Hp.
  - rewrite boot_derivation2_quote_cast. exact Hcode.
Qed.

Corollary boot_provable_sound : forall L EL T ET formula,
  @boot_provable L EL T ET formula ->
  exists p : proposition L,
    boot_typed_formula_quote EL p = formula /\
    first_order_derivable2 T [p].
Proof.
  intros L EL T ET formula [code H].
  destruct (boot_proof_sound H) as [p [d [Hp _]]].
  exists p. split; [exact Hp|now constructor].
Qed.

Corollary boot_provable_quote_iff : forall L EL T ET
    (p : proposition L),
  @boot_provable L EL T ET (boot_typed_formula_quote EL p) <->
  first_order_derivable2 T [p].
Proof.
  intros L EL T ET p; split.
  - intro H. destruct (boot_provable_sound H) as [q [Hq Hder]].
    apply boot_typed_formula_quote_injective in Hq. now subst q.
  - apply boot_derivable2_quote_provable.
Qed.
