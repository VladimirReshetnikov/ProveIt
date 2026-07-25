(* ===================================================================== *)
(*  PAHFOrdinalCodeMulCore.v                                            *)
(*                                                                       *)
(*  Sound multiplication-core reduction for ordinal-code term graphs.   *)
(*                                                                       *)
(*  The existentially bound core has the exact Lean statement.  The     *)
(*  unbound Coq open-core record currently asks for an invalid reverse   *)
(*  implication, so this module exposes the sound forward interface and  *)
(*  identifies the one genuine arithmetic kernel needed by both forms.  *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol Calculus.
From PAHF Require Import PAHF PAHFOrdinalCode
  PAHFTranslatedOperations PAHFOrdinalCodeTermOperations.

Import ListNotations.
Import PA PA.Term PA.Formula.

Definition mulTermSubst_core
    (out left right : term) (n : nat) : term :=
  match n with
  | 0 => right
  | 1 => left
  | 2 => out
  | S (S (S k)) => tVar (S (S (S k)))
  end.

(** Term-parametric reverse translation of the HF multiplication graph. *)
Definition hfMulGraphTermAt_core
    (out left right : term) : formula :=
  subst (mulTermSubst_core out left right)
    (hfMulGraphAt 2 1 0).

Lemma subst_hfMulGraphTermAt_core : forall sigma out left right,
  subst sigma (hfMulGraphTermAt_core out left right) =
    hfMulGraphTermAt_core
      (Term.subst sigma out)
      (Term.subst sigma left)
      (Term.subst sigma right).
Proof.
  intros sigma out left right.
  unfold hfMulGraphTermAt_core.
  rewrite subst_comp.
  apply subst_ext_free.
  intros n hn.
  unfold hfMulGraphAt in hn.
  destruct (hfFormulaAt_free (mulGraphAt 2 1 0)
    (fun k => k) n hn) as [m [hm hnEq]].
  simpl in hnEq.
  subst n.
  destruct (mulGraphAt_free m 2 1 0 hm) as [hout | [hleft | hright]].
  - subst m. reflexivity.
  - subst m. reflexivity.
  - subst m. reflexivity.
Qed.

Lemma rename_hfMulGraphTermAt_core : forall r out left right,
  rename r (hfMulGraphTermAt_core out left right) =
    hfMulGraphTermAt_core
      (Term.rename r out)
      (Term.rename r left)
      (Term.rename r right).
Proof.
  intros r out left right.
  rename_from_subst subst_hfMulGraphTermAt_core.
Qed.

Lemma hfMulGraphAt_eq_termAt_core : forall out left right,
  hfMulGraphAt out left right =
    hfMulGraphTermAt_core (tVar out) (tVar left) (tVar right).
Proof.
  intros out left right.
  set (r := fun n =>
    match n with
    | 0 => right
    | 1 => left
    | 2 => out
    | S (S (S k)) => S (S (S k))
    end).
  assert (hsubst :
      mulTermSubst_core (tVar out) (tVar left) (tVar right) =
        (fun n => tVar (r n))).
  {
    apply functional_extensionality.
    intros [|[|[|n]]]; reflexivity.
  }
  assert (hsource : Fol.rename r (mulGraphAt 2 1 0) =
      mulGraphAt out left right).
  {
    rewrite rename_mulGraphAt.
    unfold r.
    reflexivity.
  }
  unfold hfMulGraphTermAt_core.
  rewrite hsubst.
  rewrite subst_var_rename.
  unfold hfMulGraphAt.
  rewrite <- hsource.
  apply hfFormulaAt_id_rename.
Qed.

Lemma compositeMulCoreAt_normalForm_core : forall codedOut,
  compositeMulCoreAt codedOut =
    pAnd
      (pEq (tVar 0) (tVar (codedOut + 3)))
      (hfMulGraphTermAt_core (tVar 0) (tVar 1) (tVar 2)).
Proof.
  intro codedOut.
  rewrite <- hfMulGraphAt_eq_termAt_core.
  unfold compositeMulCoreAt, hfMulGraphAt.
  cbn [hfFormulaAt].
  set (r := compositeMulCoreSlotMap codedOut).
  assert (hmul :
      hfFormulaAt r mulGraph =
      hfFormulaAt (fun n : nat => n) mulGraph).
  {
    apply hfFormulaAt_ext_free.
    intros n hn.
    destruct (mulGraph_free n hn) as [-> | [-> | ->]];
      reflexivity.
  }
  rewrite hmul.
  unfold r, compositeMulCoreSlotMap, mulGraph.
  replace (codedOut + 0 + 3) with (codedOut + 3) by lia.
  reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* Corrected interfaces and reductions.                                  *)

(** The genuine arithmetic kernel at arbitrary term parameters. *)
Definition PAOrdinalCodeMulTermCompatibility : Prop :=
  forall (G : list formula)
    (leftRaw leftCode rightRaw rightCode out : term),
    BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
    BProv Ax_s G (ordinalCodeGraphTermAt rightRaw rightCode) ->
    BProv Ax_s G
      (iffForm
        (hfMulGraphTermAt_core out leftCode rightCode)
        (ordinalCodeGraphTermAt (tMul leftRaw rightRaw) out)).

(** Sound half of the currently over-strong unbound open-core interface. *)
Definition PAOrdinalCodeMulOpenCoreForwardCompatibility : Prop :=
  forall (G : list formula) (leftRaw rightRaw : term) (codedOut : nat),
    BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw (tVar 1)) ->
    BProv Ax_s G
      (ordinalCodeGraphTermAt rightRaw (tVar 2)) ->
    BProv Ax_s G
      (pImp
        (compositeMulCoreAt codedOut)
        (ordinalCodeGraphTermAt
          (tMul leftRaw rightRaw) (tVar (codedOut + 3)))).

(** Forget the unsound reverse half of the historical open-core interface.
    Keeping this projection named is useful at compatibility boundaries: the
    structural term proof below needs only this forward implication, while
    older callers may still package it as an [iffForm]. *)
Definition PAOrdinalCodeMulOpenCoreForwardCompatibility_of_open
    (hopen : PAOrdinalCodeMulOpenCoreCompatibility) :
  PAOrdinalCodeMulOpenCoreForwardCompatibility :=
  fun G leftRaw rightRaw codedOut hleft hright =>
    BProv_andE1 Ax_s G _ _
      (hopen G leftRaw rightRaw codedOut hleft hright).

Record PAOrdinalCodeMulCoreProofsCorrected : Prop := {
  pa_mul_open_core_forward : PAOrdinalCodeMulOpenCoreForwardCompatibility;
  pa_mul_bound_core_exact : PAOrdinalCodeMulBoundCoreCompatibility
}.

Theorem PAOrdinalCodeMulOpenCoreForwardCompatibility_of_term :
  PAOrdinalCodeMulTermCompatibility ->
  PAOrdinalCodeMulOpenCoreForwardCompatibility.
Proof.
  intros hterm G leftRaw rightRaw codedOut hleft hright.
  set (core := compositeMulCoreAt codedOut).
  set (target := ordinalCodeGraphTermAt
    (tMul leftRaw rightRaw) (tVar (codedOut + 3))).
  set (C := core :: G).
  assert (hcore : BProv Ax_s C core).
  { apply BProv_ass. unfold C. simpl. now left. }
  assert (hcore' : BProv Ax_s C
      (pAnd
        (pEq (tVar 0) (tVar (codedOut + 3)))
        (hfMulGraphTermAt_core (tVar 0) (tVar 1) (tVar 2)))).
  {
    unfold core in hcore.
    rewrite compositeMulCoreAt_normalForm_core in hcore.
    exact hcore.
  }
  assert (houtEq : BProv Ax_s C
      (pEq (tVar 0) (tVar (codedOut + 3)))).
  { exact (BProv_andE1 Ax_s C _ _ hcore'). }
  assert (hmul : BProv Ax_s C
      (hfMulGraphTermAt_core (tVar 0) (tVar 1) (tVar 2))).
  { exact (BProv_andE2 Ax_s C _ _ hcore'). }
  pose proof (hterm C
    leftRaw (tVar 1) rightRaw (tVar 2) (tVar 0)
    (BProv_context_cons Ax_s G core _ hleft)
    (BProv_context_cons Ax_s G core _ hright)) as hcompat.
  assert (hmulForward : BProv Ax_s C
      (pImp
        (hfMulGraphTermAt_core (tVar 0) (tVar 1) (tVar 2))
        (ordinalCodeGraphTermAt
          (tMul leftRaw rightRaw) (tVar 0)))).
  { unfold iffForm in hcompat; exact (BProv_andE1 Ax_s C _ _ hcompat). }
  assert (hlocal : BProv Ax_s C
      (ordinalCodeGraphTermAt (tMul leftRaw rightRaw) (tVar 0))).
  { exact (BProv_mp Ax_s C _ _ hmulForward hmul). }
  assert (hresult : BProv Ax_s C target).
  {
    unfold target.
    exact (BProv_ordinalCodeGraphTermAt_congr_coded
      Ax_s C (tMul leftRaw rightRaw)
      (tVar 0) (tVar (codedOut + 3)) houtEq hlocal).
  }
  unfold C in hresult.
  exact (BProv_impI Ax_s G core target hresult).
Qed.

(** The existentially bound multiplication core is exactly reducible to
    the term-parametric multiplication kernel. *)
Theorem PAOrdinalCodeMulBoundCoreCompatibility_of_term :
  PAOrdinalCodeMulTermCompatibility ->
  PAOrdinalCodeMulBoundCoreCompatibility.
Proof.
  intros hterm G leftRaw rightRaw codedOut hleft hright.
  set (core := compositeMulCoreAt codedOut).
  set (coreEx := pEx core).
  set (target := ordinalCodeGraphTermAt
    (tMul leftRaw rightRaw) (tVar (codedOut + 2))).
  assert (hforward : BProv Ax_s G (pImp coreEx target)).
  {
    set (C := coreEx :: G).
    assert (hcoreEx : BProv Ax_s C coreEx).
    { apply BProv_ass. unfold C. simpl. now left. }
    set (D := core :: map (rename S) C).
    assert (hopened : BProv Ax_s D (rename S target)).
    {
      assert (hcore : BProv Ax_s D core).
      { apply BProv_ass. unfold D. simpl. now left. }
      assert (hcore' : BProv Ax_s D
          (pAnd
            (pEq (tVar 0) (tVar (codedOut + 3)))
            (hfMulGraphTermAt_core (tVar 0) (tVar 1) (tVar 2)))).
      {
        unfold core in hcore.
        rewrite compositeMulCoreAt_normalForm_core in hcore.
        exact hcore.
      }
      assert (houtEq : BProv Ax_s D
          (pEq (tVar 0) (tVar (codedOut + 3)))).
      { exact (BProv_andE1 Ax_s D _ _ hcore'). }
      assert (hmul : BProv Ax_s D
          (hfMulGraphTermAt_core (tVar 0) (tVar 1) (tVar 2))).
      { exact (BProv_andE2 Ax_s D _ _ hcore'). }
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
        G _ hleft S) as hleftRen.
      rewrite rename_ordinalCodeGraphTermAt in hleftRen.
      assert (hleftD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename S leftRaw) (tVar 1))).
      {
        cbn [Term.rename] in hleftRen.
        unfold D, C.
        exact (BProv_context_cons Ax_s
          (rename S coreEx :: map (rename S) G)
          core _
          (BProv_context_cons Ax_s (map (rename S) G)
            (rename S coreEx) _ hleftRen)).
      }
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
        G _ hright S) as hrightRen.
      rewrite rename_ordinalCodeGraphTermAt in hrightRen.
      assert (hrightD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename S rightRaw) (tVar 2))).
      {
        cbn [Term.rename] in hrightRen.
        unfold D, C.
        exact (BProv_context_cons Ax_s
          (rename S coreEx :: map (rename S) G)
          core _
          (BProv_context_cons Ax_s (map (rename S) G)
            (rename S coreEx) _ hrightRen)).
      }
      pose proof (hterm D
        (Term.rename S leftRaw) (tVar 1)
        (Term.rename S rightRaw) (tVar 2) (tVar 0)
        hleftD hrightD) as hcompat.
      assert (hmulForward : BProv Ax_s D
          (pImp
            (hfMulGraphTermAt_core (tVar 0) (tVar 1) (tVar 2))
            (ordinalCodeGraphTermAt
              (tMul (Term.rename S leftRaw) (Term.rename S rightRaw))
              (tVar 0)))).
      { unfold iffForm in hcompat; exact (BProv_andE1 Ax_s D _ _ hcompat). }
      assert (hlocal : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (tMul (Term.rename S leftRaw) (Term.rename S rightRaw))
            (tVar 0))).
      { exact (BProv_mp Ax_s D _ _ hmulForward hmul). }
      assert (hresult : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (tMul (Term.rename S leftRaw) (Term.rename S rightRaw))
            (tVar (codedOut + 3)))).
      {
        exact (BProv_ordinalCodeGraphTermAt_congr_coded
          Ax_s D _ (tVar 0) (tVar (codedOut + 3)) houtEq hlocal).
      }
      unfold target.
      rewrite rename_ordinalCodeGraphTermAt.
      cbn [Term.rename].
      replace (S (codedOut + 2)) with (codedOut + 3) by lia.
      exact hresult.
    }
    assert (htargetC : BProv Ax_s C target).
    {
      unfold D in hopened.
      exact (BProv_exE_of_sentences Ax_s C core target
        sentence_ax_s hcoreEx hopened).
    }
    unfold C in htargetC.
    exact (BProv_impI Ax_s G coreEx target htargetC).
  }
  assert (hreverse : BProv Ax_s G (pImp target coreEx)).
  {
    set (C := target :: G).
    assert (htarget : BProv Ax_s C target).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hleftC : BProv Ax_s C
        (ordinalCodeGraphTermAt leftRaw (tVar 0))).
    { exact (BProv_context_cons Ax_s G target _ hleft). }
    assert (hrightC : BProv Ax_s C
        (ordinalCodeGraphTermAt rightRaw (tVar 1))).
    { exact (BProv_context_cons Ax_s G target _ hright). }
    set (out := tVar (codedOut + 2)).
    pose proof (hterm C leftRaw (tVar 0) rightRaw (tVar 1) out
      hleftC hrightC) as hcompat.
    assert (hmulReverse : BProv Ax_s C
        (pImp target
          (hfMulGraphTermAt_core out (tVar 0) (tVar 1)))).
    {
      unfold iffForm in hcompat.
      unfold target, out.
      exact (BProv_andE2 Ax_s C _ _ hcompat).
    }
    assert (hmul : BProv Ax_s C
        (hfMulGraphTermAt_core out (tVar 0) (tVar 1))).
    { exact (BProv_mp Ax_s C _ _ hmulReverse htarget). }
    assert (heq : BProv Ax_s C (pEq out out)).
    { exact (BProv_eqRefl Ax_s C out). }
    assert (hcoreEx : BProv Ax_s C coreEx).
    {
      unfold coreEx, core.
      apply (BProv_exI Ax_s C _ out).
      cbn [subst].
      rewrite compositeMulCoreAt_normalForm_core.
      cbn [subst].
      rewrite subst_hfMulGraphTermAt_core.
      simpl.
      unfold out in *.
      replace (codedOut + 3) with (S (codedOut + 2)) by lia.
      cbn [instTerm].
      exact (BProv_andI Ax_s C _ _ heq hmul).
    }
    unfold C in hcoreEx.
    exact (BProv_impI Ax_s G target coreEx hcoreEx).
  }
  exact (PAHFProofCalculus.BProv_PA_iffForm_intro Ax_s G _ _ hforward hreverse).
Qed.

Definition PAOrdinalCodeMulCoreProofsCorrected_of_term
    (hterm : PAOrdinalCodeMulTermCompatibility) :
  PAOrdinalCodeMulCoreProofsCorrected :=
  {| pa_mul_open_core_forward :=
       PAOrdinalCodeMulOpenCoreForwardCompatibility_of_term hterm;
     pa_mul_bound_core_exact :=
       PAOrdinalCodeMulBoundCoreCompatibility_of_term hterm |}.

(** Any inhabitant of the historical record yields the corrected package;
    the converse deliberately does not claim the invalid open reverse. *)
Definition PAOrdinalCodeMulCoreProofsCorrected_of_historical
    (P : PAOrdinalCodeMulCoreProofs) :
  PAOrdinalCodeMulCoreProofsCorrected.
Proof.
  constructor.
  - exact (PAOrdinalCodeMulOpenCoreForwardCompatibility_of_open
      (pa_mul_open_core P)).
  - exact (pa_mul_bound_core P).
Defined.
