(*
  Coq port of SetTheory.PAHF.RiemannHypothesis.

  This file mirrors the Lean syntax-level construction of a first-order PA
  sentence expressing the Littlewood/Mertens growth criterion for the Riemann
  Hypothesis, together with the Lean module's PA provability certificates for
  the small closed base cases: primality of 2 and 3, squarefreeness of 1..3,
  parity of the tiny prime factorizations, the Moebius values mu(1)=+1,
  mu(2)=mu(3)=-1, and the first three Mertens prefix-count statements
  M(1)=1, M(2)=0, M(3)=-1.  As in the Lean module, the final certified fact
  is that the arithmetized formula is a closed PA sentence.

  The remainder and beta-coding predicates ([remTermTermAt],
  [betaModTermTerm], [betaTermTermAt], [betaTermTermAtConstIdx]) are the
  library versions from [PA.Formula], exactly as the Lean module imports them
  from PAHF.PASyntax.
*)

From Stdlib Require Import Arith.Arith Lia List.
From PAHF Require Import PAHF.

Import ListNotations.
Import PA PA.Term PA.Formula.

Open Scope nat_scope.

(* ===== Small formula combinators ===== *)

Definition notF (phi : formula) : formula :=
  pImp phi pBot.

Definition shiftTerm (k : nat) (t : term) : term :=
  Term.rename (fun n => n + k) t.

Definition shiftFormula (k : nat) (phi : formula) : formula :=
  rename (fun n => n + k) phi.

(* Lean: shiftTerm_numeral *)
Lemma shiftTerm_numeral : forall k n,
  shiftTerm k (Term.numeral n) = Term.numeral n.
Proof.
  intros k n.
  unfold shiftTerm.
  apply Term.rename_numeral.
Qed.

Definition dvdTermAt (a b : term) : formula :=
  pEx (pEq
    (tMul (Term.rename S a) (tVar 0))
    (Term.rename S b)).

Definition evenTermAt (t : term) : formula :=
  pEx (pEq
    (Term.rename S t)
    (tAdd (tVar 0) (tVar 0))).

Definition oddTermAt (t : term) : formula :=
  pEx (pEq
    (Term.rename S t)
    (tSucc (tAdd (tVar 0) (tVar 0)))).

Definition nonzeroTermAt (t : term) : formula :=
  pEx (pEq
    (Term.rename S t)
    (tSucc (tVar 0))).

Definition properRemainderWitnessAt
    (value modulus : term) : formula :=
  pEx (pEx (pAnd
    (ltTermAt (tSucc (tVar 1)) (shiftTerm 2 modulus))
    (pEq (shiftTerm 2 value)
      (tAdd
        (tMul (tVar 0) (shiftTerm 2 modulus))
        (tSucc (tVar 1)))))).

Definition primeTermAt (p : term) : formula :=
  pAnd
    (ltTermAt (Term.numeral 1) p)
    (pAll (pImp
      (pAnd
        (ltTermAt (Term.numeral 1) (tVar 0))
        (ltTermAt (tVar 0) (shiftTerm 1 p)))
      (properRemainderWitnessAt (shiftTerm 1 p) (tVar 0)))).

Definition squarefreeTermAt (n : term) : formula :=
  pAll (pImp
    (pAnd
      (ltTermAt (tVar 0) (tSucc (shiftTerm 1 n)))
      (primeTermAt (tVar 0)))
    (properRemainderWitnessAt
      (shiftTerm 1 n)
      (tMul (tVar 0) (tVar 0)))).

(* ===== PA certificates for small arithmetic facts ===== *)

(* Lean: term_subst_upSubst_instTerm_rename_two_succ_exact *)
Lemma term_subst_upSubst_instTerm_rename_two_succ_exact :
  forall (t u : term),
  Term.subst (Term.upSubst (instTerm u))
      (Term.rename S (Term.rename S t)) =
    Term.rename S t.
Proof.
  intros t u.
  rewrite (Term.rename_comp t S S).
  apply term_subst_upSubst_instTerm_rename_two_succ.
Qed.

(* Lean: term_subst_two_witnesses_rename_two_succ_add *)
Lemma term_subst_two_witnesses_rename_two_succ_add :
  forall (t pred quot : term),
  Term.subst (instTerm quot)
      (Term.subst (Term.upSubst (instTerm pred))
        (Term.rename (fun n => n + 2) t)) = t.
Proof.
  intros t pred quot.
  rewrite term_subst_upSubst_instTerm_rename_add_two.
  apply term_subst_instTerm_rename_succ.
Qed.

(* Lean: term_subst_up2_instTerm_rename_three_succ_add *)
Lemma term_subst_up2_instTerm_rename_three_succ_add :
  forall (t u : term),
  Term.subst (Term.upSubst (Term.upSubst (instTerm u)))
      (Term.rename S (Term.rename (fun n => n + 2) t)) =
    Term.rename S (Term.rename S t).
Proof.
  intros t u.
  rewrite (Term.rename_comp t S (fun n => n + 2)).
  rewrite (Term.rename_comp t S S).
  change (Term.upSubst (Term.upSubst (instTerm u)))
    with (iterUpSubst 2 (instTerm u)).
  eapply (term_subst_iterUpSubst_instTerm_rename_ext 2 0);
    intro n; cbn; lia.
Qed.

(* Lean: subst_properRemainder_body *)
Lemma subst_properRemainder_body :
  forall (pred quot value modulus : term),
  subst (instTerm quot)
    (subst (Term.upSubst (instTerm pred))
      (pAnd
        (ltTermAt (tSucc (tVar 1)) (shiftTerm 2 modulus))
        (pEq (shiftTerm 2 value)
          (tAdd (tMul (tVar 0) (shiftTerm 2 modulus))
            (tSucc (tVar 1)))))) =
  pAnd
    (ltTermAt (tSucc pred) modulus)
    (pEq value (tAdd (tMul quot modulus) (tSucc pred))).
Proof.
  intros pred quot value modulus.
  unfold ltTermAt, shiftTerm.
  simpl.
  repeat rewrite term_subst_up2_instTerm_rename_three_succ_add.
  repeat rewrite term_subst_upSubst_instTerm_rename_two_succ_exact.
  repeat rewrite term_subst_two_witnesses_rename_two_succ_add.
  repeat rewrite term_subst_instTerm_rename_succ.
  reflexivity.
Qed.

(* Lean: BProv_Ax_s_euclideanDecomposition_of_modEq *)
Lemma BProv_Ax_s_euclideanDecomposition_of_modEq :
  forall G (modulus : term) (r v m q : nat),
  BProv Ax_s G (pEq modulus (Term.numeral m)) ->
  q * m + r = v ->
  BProv Ax_s G
    (pEq (tAdd (tMul (Term.numeral q) modulus) (Term.numeral r))
      (Term.numeral v)).
Proof.
  intros G modulus r v m q hmod hdiv.
  assert (hmul : BProv Ax_s G
      (pEq (tMul (Term.numeral q) modulus) (Term.numeral (q * m)))).
  { exact (BProv_eqTrans Ax_s G _ _ _
      (BProv_eq_congr_mul_right Ax_s G (Term.numeral q) _ _ hmod)
      (BProv_Ax_s_mulNumerals G q m)). }
  assert (hadd : BProv Ax_s G
      (pEq (tAdd (tMul (Term.numeral q) modulus) (Term.numeral r))
        (Term.numeral (q * m + r)))).
  { exact (BProv_eqTrans Ax_s G _ _ _
      (BProv_eq_congr_add_left Ax_s G _ _ (Term.numeral r) hmul)
      (BProv_Ax_s_addNumerals G (q * m) r)). }
  rewrite hdiv in hadd.
  exact hadd.
Qed.

(* Lean: BProv_Ax_s_properRemainderWitnessAt_numeral_of_modEq *)
Lemma BProv_Ax_s_properRemainderWitnessAt_numeral_of_modEq :
  forall G (modulus : term) (r v m q : nat),
  BProv Ax_s G (pEq modulus (Term.numeral m)) ->
  r < m -> 0 < r -> q * m + r = v ->
  BProv Ax_s G (properRemainderWitnessAt (Term.numeral v) modulus).
Proof.
  intros G modulus r v m q hmod hr hrpos hdiv.
  destruct r as [|pred]; [lia|].
  assert (hltClosed : BProv Ax_s G
      (ltTermAt (Term.numeral (S pred)) (Term.numeral m))).
  { unfold ltTermAt.
    repeat rewrite Term.rename_numeral.
    exact (BProv_Ax_s_ltConst_closed G (S pred) m hr). }
  assert (hlt : BProv Ax_s G
      (ltTermAt (tSucc (Term.numeral pred)) modulus)).
  { exact (BProv_ltTermAt_of_eq_right Ax_s G
      (Term.numeral (S pred)) (Term.numeral m) modulus
      (BProv_eqSym Ax_s G _ _ hmod) hltClosed). }
  assert (hsum : BProv Ax_s G
      (pEq
        (tAdd (tMul (Term.numeral q) modulus) (tSucc (Term.numeral pred)))
        (Term.numeral v))).
  { exact (BProv_Ax_s_euclideanDecomposition_of_modEq
      G modulus (S pred) v m q hmod hdiv). }
  assert (hbodyQ : BProv Ax_s G
      (subst (instTerm (Term.numeral q))
        (subst (Term.upSubst (instTerm (Term.numeral pred)))
          (pAnd
            (ltTermAt (tSucc (tVar 1)) (shiftTerm 2 modulus))
            (pEq (shiftTerm 2 (Term.numeral v))
              (tAdd (tMul (tVar 0) (shiftTerm 2 modulus))
                (tSucc (tVar 1)))))))).
  { rewrite subst_properRemainder_body.
    apply BProv_andI.
    - exact hlt.
    - exact (BProv_eqSym Ax_s G _ _ hsum). }
  assert (hexQ : BProv Ax_s G
      (pEx (subst (Term.upSubst (instTerm (Term.numeral pred)))
        (pAnd
          (ltTermAt (tSucc (tVar 1)) (shiftTerm 2 modulus))
          (pEq (shiftTerm 2 (Term.numeral v))
            (tAdd (tMul (tVar 0) (shiftTerm 2 modulus))
              (tSucc (tVar 1)))))))).
  { exact (BProv_exI Ax_s G _ (Term.numeral q) hbodyQ). }
  unfold properRemainderWitnessAt.
  apply (BProv_exI Ax_s G _ (Term.numeral pred)).
  exact hexQ.
Qed.

(* Lean: BProv_Ax_s_contradiction_one_lt_of_lt_two *)
Lemma BProv_Ax_s_contradiction_one_lt_of_lt_two :
  forall G (d : term),
  BProv Ax_s G (ltTermAt (Term.numeral 1) d) ->
  BProv Ax_s G (ltTermAt d (Term.numeral 2)) ->
  BProv Ax_s G pBot.
Proof.
  intros G d h1d hd2.
  assert (hcases : BProv Ax_s G
      (pOr (ltTermAt d (Term.numeral 1)) (pEq d (Term.numeral 1)))).
  { exact (BProv_Ax_s_ltTermAt_succ_right_cases G d (Term.numeral 1) hd2). }
  assert (hltBranch : BProv Ax_s (ltTermAt d (Term.numeral 1) :: G) pBot).
  { assert (h1d' : BProv Ax_s (ltTermAt d (Term.numeral 1) :: G)
        (ltTermAt (Term.numeral 1) d)).
    { exact (BProv_context_cons Ax_s G _ _ h1d). }
    assert (hd1 : BProv Ax_s (ltTermAt d (Term.numeral 1) :: G)
        (ltTermAt d (Term.numeral 1))).
    { apply BProv_ass. simpl. left. reflexivity. }
    assert (hleD0 : BProv Ax_s (ltTermAt d (Term.numeral 1) :: G)
        (leTermAt d tZero)).
    { exact (BProv_Ax_s_leTermAt_of_ltTermAt_succ_right _ d tZero hd1). }
    assert (hle01 : BProv Ax_s (ltTermAt d (Term.numeral 1) :: G)
        (leTermAt tZero (Term.numeral 1))).
    { exact (BProv_Ax_s_leTermAt_zero_left _ (Term.numeral 1)). }
    exact (BProv_Ax_s_ltTermAt_leTermAt_bot _ (Term.numeral 1) d h1d'
      (BProv_Ax_s_leTermAt_trans _ d tZero (Term.numeral 1) hleD0 hle01)). }
  assert (heqBranch : BProv Ax_s (pEq d (Term.numeral 1) :: G) pBot).
  { assert (h1d' : BProv Ax_s (pEq d (Term.numeral 1) :: G)
        (ltTermAt (Term.numeral 1) d)).
    { exact (BProv_context_cons Ax_s G _ _ h1d). }
    assert (hdeq : BProv Ax_s (pEq d (Term.numeral 1) :: G)
        (pEq d (Term.numeral 1))).
    { apply BProv_ass. simpl. left. reflexivity. }
    assert (hlt11 : BProv Ax_s (pEq d (Term.numeral 1) :: G)
        (ltTermAt (Term.numeral 1) (Term.numeral 1))).
    { exact (BProv_ltTermAt_of_eq_right Ax_s _
        (Term.numeral 1) d (Term.numeral 1) hdeq h1d'). }
    exact (BProv_Ax_s_ltTermAt_leTermAt_bot _
      (Term.numeral 1) (Term.numeral 1) hlt11
      (BProv_Ax_s_leTermAt_refl _ (Term.numeral 1))). }
  exact (BProv_orE Ax_s G _ _ pBot hcases hltBranch heqBranch).
Qed.

(* Lean: BProv_Ax_s_of_head_lt_two *)
Lemma BProv_Ax_s_of_head_lt_two :
  forall G (d : term) (a : formula),
  BProv Ax_s G (ltTermAt (Term.numeral 1) d) ->
  BProv Ax_s (ltTermAt d (Term.numeral 2) :: G) a.
Proof.
  intros G d a h1d.
  apply (BProv_botE Ax_s _ a).
  apply (BProv_Ax_s_contradiction_one_lt_of_lt_two _ d).
  - exact (BProv_context_cons Ax_s G _ _ h1d).
  - apply BProv_ass. simpl. left. reflexivity.
Qed.

(* Lean: BProv_Ax_s_properRemainderWitness_var_of_head_eq *)
Lemma BProv_Ax_s_properRemainderWitness_var_of_head_eq :
  forall G (r v m q : nat),
  r < m -> 0 < r -> q * m + r = v ->
  BProv Ax_s (pEq (tVar 0) (Term.numeral m) :: G)
    (properRemainderWitnessAt (Term.numeral v) (tVar 0)).
Proof.
  intros G r v m q hr hrpos hdiv.
  apply (BProv_Ax_s_properRemainderWitnessAt_numeral_of_modEq
    _ (tVar 0) r v m q).
  - apply BProv_ass. simpl. left. reflexivity.
  - exact hr.
  - exact hrpos.
  - exact hdiv.
Qed.

(* Lean: BProv_Ax_s_square_of_eq_numeral *)
Lemma BProv_Ax_s_square_of_eq_numeral :
  forall G (p : term) (a : nat),
  BProv Ax_s G (pEq p (Term.numeral a)) ->
  BProv Ax_s G (pEq (tMul p p) (Term.numeral (a * a))).
Proof.
  intros G p a hp.
  exact (BProv_eqTrans Ax_s G _ _ _
    (BProv_eq_congr_mul Ax_s G _ _ _ _ hp hp)
    (BProv_Ax_s_mulNumerals G a a)).
Qed.

(* Lean: BProv_Ax_s_properRemainderWitness_square_of_head_eq *)
Lemma BProv_Ax_s_properRemainderWitness_square_of_head_eq :
  forall G (a v : nat),
  0 < v -> v < a * a ->
  BProv Ax_s (pEq (tVar 0) (Term.numeral a) :: G)
    (properRemainderWitnessAt (Term.numeral v) (tMul (tVar 0) (tVar 0))).
Proof.
  intros G a v hvpos hv.
  apply (BProv_Ax_s_properRemainderWitnessAt_numeral_of_modEq
    _ (tMul (tVar 0) (tVar 0)) v v (a * a) 0).
  - apply BProv_Ax_s_square_of_eq_numeral.
    apply BProv_ass. simpl. left. reflexivity.
  - exact hv.
  - exact hvpos.
  - lia.
Qed.

(* Lean: primeDivisorHyp *)
Definition primeDivisorHyp (p : nat) : formula :=
  pAnd (ltTermAt (Term.numeral 1) (tVar 0))
    (ltTermAt (tVar 0) (Term.numeral p)).

(* Lean: BProv_Ax_s_primeDivisorHyp_one_lt *)
Lemma BProv_Ax_s_primeDivisorHyp_one_lt : forall G p,
  BProv Ax_s (primeDivisorHyp p :: G)
    (ltTermAt (Term.numeral 1) (tVar 0)).
Proof.
  intros G p.
  apply (BProv_andE1 Ax_s _ _ (ltTermAt (tVar 0) (Term.numeral p))).
  apply BProv_ass. simpl. left. reflexivity.
Qed.

(* Lean: BProv_Ax_s_primeDivisorHyp_lt *)
Lemma BProv_Ax_s_primeDivisorHyp_lt : forall G p,
  BProv Ax_s (primeDivisorHyp p :: G)
    (ltTermAt (tVar 0) (Term.numeral p)).
Proof.
  intros G p.
  apply (BProv_andE2 Ax_s _ (ltTermAt (Term.numeral 1) (tVar 0))).
  apply BProv_ass. simpl. left. reflexivity.
Qed.

(* Lean: BProv_Ax_s_primeTermAt_numeral *)
Lemma BProv_Ax_s_primeTermAt_numeral : forall p,
  1 < p ->
  BProv Ax_s [primeDivisorHyp p]
    (properRemainderWitnessAt (Term.numeral p) (tVar 0)) ->
  BProv Ax_s [] (primeTermAt (Term.numeral p)).
Proof.
  intros p hp hbody.
  assert (hgt1 : BProv Ax_s []
      (ltTermAt (Term.numeral 1) (Term.numeral p))).
  { unfold ltTermAt.
    repeat rewrite Term.rename_numeral.
    exact (BProv_Ax_s_ltConst_closed [] 1 p hp). }
  assert (hforall : BProv Ax_s []
      (pAll (pImp
        (pAnd
          (ltTermAt (Term.numeral 1) (tVar 0))
          (ltTermAt (tVar 0) (shiftTerm 1 (Term.numeral p))))
        (properRemainderWitnessAt (shiftTerm 1 (Term.numeral p))
          (tVar 0))))).
  { apply (BProv_allI_of_sentences Ax_s [] _ sentence_ax_s).
    rewrite shiftTerm_numeral.
    apply BProv_impI.
    exact hbody. }
  unfold primeTermAt.
  exact (BProv_andI Ax_s [] _ _ hgt1 hforall).
Qed.

(* Lean: BProv_Ax_s_prime_two *)
Lemma BProv_Ax_s_prime_two :
  BProv Ax_s [] (primeTermAt (Term.numeral 2)).
Proof.
  apply BProv_Ax_s_primeTermAt_numeral; [lia|].
  apply (BProv_botE Ax_s _ _).
  exact (BProv_Ax_s_contradiction_one_lt_of_lt_two _ (tVar 0)
    (BProv_Ax_s_primeDivisorHyp_one_lt [] 2)
    (BProv_Ax_s_primeDivisorHyp_lt [] 2)).
Qed.

(* Lean: BProv_Ax_s_prime_three *)
Lemma BProv_Ax_s_prime_three :
  BProv Ax_s [] (primeTermAt (Term.numeral 3)).
Proof.
  apply BProv_Ax_s_primeTermAt_numeral; [lia|].
  assert (hcases : BProv Ax_s [primeDivisorHyp 3]
      (pOr (ltTermAt (tVar 0) (Term.numeral 2))
        (pEq (tVar 0) (Term.numeral 2)))).
  { exact (BProv_Ax_s_ltTermAt_succ_right_cases _ (tVar 0) (Term.numeral 2)
      (BProv_Ax_s_primeDivisorHyp_lt [] 3)). }
  apply (BProv_orE Ax_s _ _ _ _ hcases).
  - exact (BProv_Ax_s_of_head_lt_two _ (tVar 0) _
      (BProv_Ax_s_primeDivisorHyp_one_lt [] 3)).
  - apply (BProv_Ax_s_properRemainderWitness_var_of_head_eq _ 1 3 2 1); lia.
Qed.

(* Lean: squarefreePrimeHyp *)
Definition squarefreePrimeHyp (n : nat) : formula :=
  pAnd (ltTermAt (tVar 0) (Term.numeral (S n)))
    (primeTermAt (tVar 0)).

(* Lean: BProv_Ax_s_squarefreePrimeHyp_lt_bound *)
Lemma BProv_Ax_s_squarefreePrimeHyp_lt_bound : forall G n,
  BProv Ax_s (squarefreePrimeHyp n :: G)
    (ltTermAt (tVar 0) (Term.numeral (S n))).
Proof.
  intros G n.
  apply (BProv_andE1 Ax_s _ _ (primeTermAt (tVar 0))).
  apply BProv_ass. simpl. left. reflexivity.
Qed.

(* Lean: BProv_Ax_s_squarefreePrimeHyp_one_lt *)
Lemma BProv_Ax_s_squarefreePrimeHyp_one_lt : forall G n,
  BProv Ax_s (squarefreePrimeHyp n :: G)
    (ltTermAt (Term.numeral 1) (tVar 0)).
Proof.
  intros G n.
  assert (hprime : BProv Ax_s (squarefreePrimeHyp n :: G)
      (primeTermAt (tVar 0))).
  { apply (BProv_andE2 Ax_s _ (ltTermAt (tVar 0) (Term.numeral (S n)))).
    apply BProv_ass. simpl. left. reflexivity. }
  unfold primeTermAt in hprime.
  exact (BProv_andE1 Ax_s _ _ _ hprime).
Qed.

(* Lean: BProv_Ax_s_squarefreeTermAt_numeral *)
Lemma BProv_Ax_s_squarefreeTermAt_numeral : forall n,
  BProv Ax_s [squarefreePrimeHyp n]
    (properRemainderWitnessAt (Term.numeral n) (tMul (tVar 0) (tVar 0))) ->
  BProv Ax_s [] (squarefreeTermAt (Term.numeral n)).
Proof.
  intros n hbody.
  unfold squarefreeTermAt.
  apply (BProv_allI_of_sentences Ax_s [] _ sentence_ax_s).
  rewrite shiftTerm_numeral.
  apply BProv_impI.
  exact hbody.
Qed.

(* Lean: BProv_Ax_s_squarefree_one *)
Lemma BProv_Ax_s_squarefree_one :
  BProv Ax_s [] (squarefreeTermAt (Term.numeral 1)).
Proof.
  apply BProv_Ax_s_squarefreeTermAt_numeral.
  apply (BProv_botE Ax_s _ _).
  exact (BProv_Ax_s_contradiction_one_lt_of_lt_two _ (tVar 0)
    (BProv_Ax_s_squarefreePrimeHyp_one_lt [] 1)
    (BProv_Ax_s_squarefreePrimeHyp_lt_bound [] 1)).
Qed.

(* Lean: BProv_Ax_s_squarefree_two *)
Lemma BProv_Ax_s_squarefree_two :
  BProv Ax_s [] (squarefreeTermAt (Term.numeral 2)).
Proof.
  apply BProv_Ax_s_squarefreeTermAt_numeral.
  assert (hcases : BProv Ax_s [squarefreePrimeHyp 2]
      (pOr (ltTermAt (tVar 0) (Term.numeral 2))
        (pEq (tVar 0) (Term.numeral 2)))).
  { exact (BProv_Ax_s_ltTermAt_succ_right_cases _ (tVar 0) (Term.numeral 2)
      (BProv_Ax_s_squarefreePrimeHyp_lt_bound [] 2)). }
  apply (BProv_orE Ax_s _ _ _ _ hcases).
  - exact (BProv_Ax_s_of_head_lt_two _ (tVar 0) _
      (BProv_Ax_s_squarefreePrimeHyp_one_lt [] 2)).
  - apply (BProv_Ax_s_properRemainderWitness_square_of_head_eq _ 2 2); lia.
Qed.

(* Lean: BProv_Ax_s_squarefree_three *)
Lemma BProv_Ax_s_squarefree_three :
  BProv Ax_s [] (squarefreeTermAt (Term.numeral 3)).
Proof.
  apply BProv_Ax_s_squarefreeTermAt_numeral.
  assert (hcases4 : BProv Ax_s [squarefreePrimeHyp 3]
      (pOr (ltTermAt (tVar 0) (Term.numeral 3))
        (pEq (tVar 0) (Term.numeral 3)))).
  { exact (BProv_Ax_s_ltTermAt_succ_right_cases _ (tVar 0) (Term.numeral 3)
      (BProv_Ax_s_squarefreePrimeHyp_lt_bound [] 3)). }
  apply (BProv_orE Ax_s _ _ _ _ hcases4).
  - assert (hp3 : BProv Ax_s
        (ltTermAt (tVar 0) (Term.numeral 3) :: [squarefreePrimeHyp 3])
        (ltTermAt (tVar 0) (Term.numeral 3))).
    { apply BProv_ass. simpl. left. reflexivity. }
    assert (hcases3 : BProv Ax_s
        (ltTermAt (tVar 0) (Term.numeral 3) :: [squarefreePrimeHyp 3])
        (pOr (ltTermAt (tVar 0) (Term.numeral 2))
          (pEq (tVar 0) (Term.numeral 2)))).
    { exact (BProv_Ax_s_ltTermAt_succ_right_cases _
        (tVar 0) (Term.numeral 2) hp3). }
    apply (BProv_orE Ax_s _ _ _ _ hcases3).
    + exact (BProv_Ax_s_of_head_lt_two _ (tVar 0) _
        (BProv_context_cons Ax_s _ _ _
          (BProv_Ax_s_squarefreePrimeHyp_one_lt [] 3))).
    + apply (BProv_Ax_s_properRemainderWitness_square_of_head_eq _ 2 3); lia.
  - apply (BProv_Ax_s_properRemainderWitness_square_of_head_eq _ 3 3); lia.
Qed.

(* Lean: BProv_Ax_s_remTermTermAt_numeral_of_modEq *)
Lemma BProv_Ax_s_remTermTermAt_numeral_of_modEq :
  forall G (modulus : term) (r v m q : nat),
  BProv Ax_s G (pEq modulus (Term.numeral m)) ->
  r < m -> q * m + r = v ->
  BProv Ax_s G
    (remTermTermAt (Term.numeral r) (Term.numeral v) modulus).
Proof.
  intros G modulus r v m q hmod hr hdiv.
  assert (hltClosed : BProv Ax_s G
      (ltTermAt (Term.numeral r) (Term.numeral m))).
  { unfold ltTermAt.
    repeat rewrite Term.rename_numeral.
    exact (BProv_Ax_s_ltConst_closed G r m hr). }
  assert (hlt : BProv Ax_s G (ltTermAt (Term.numeral r) modulus)).
  { exact (BProv_ltTermAt_of_eq_right Ax_s G
      (Term.numeral r) (Term.numeral m) modulus
      (BProv_eqSym Ax_s G _ _ hmod) hltClosed). }
  assert (hsum := BProv_Ax_s_euclideanDecomposition_of_modEq
    G modulus r v m q hmod hdiv).
  exact (BProv_Ax_s_remTermTermAt_of_eq_add_mul_terms G
    (Term.numeral r) (Term.numeral v) modulus (Term.numeral q)
    hlt (BProv_eqSym Ax_s G _ _ hsum)).
Qed.

(* Ported from the Lean library lemma of the same name in PAHF.PASyntax;
   the Coq PAHF library does not carry it yet. *)
Lemma BProv_Ax_s_betaModTermTerm_numeral :
  forall G (s i : nat),
  BProv Ax_s G
    (pEq (Term.numeral (BetaModulus s i))
      (betaModTermTerm (Term.numeral s) (Term.numeral i))).
Proof.
  intros G s i.
  assert (hmul : BProv Ax_s G
      (pEq (tMul (tSucc (Term.numeral i)) (Term.numeral s))
        (Term.numeral (S i * s)))).
  { exact (BProv_Ax_s_mulNumerals G (S i) s). }
  assert (hraw : BProv Ax_s G
      (pEq (betaModTermTerm (Term.numeral s) (Term.numeral i))
        (Term.numeral (S (S i * s))))).
  { exact (BProv_eq_congr_succ Ax_s G _ _ hmul). }
  assert (hBM : Term.numeral (BetaModulus s i) =
      Term.numeral (S (S i * s))).
  { unfold BetaModulus. reflexivity. }
  rewrite hBM.
  exact (BProv_eqSym Ax_s G _ _ hraw).
Qed.

(* Ported from the Lean library lemma of the same name in PAHF.PASyntax;
   the Coq PAHF library does not carry it yet. *)
Lemma BProv_Ax_s_betaTermTermAt_numeral_entry :
  forall G (c s i o : nat),
  BetaEntry c s i o ->
  BProv Ax_s G
    (betaTermTermAt (Term.numeral o) (Term.numeral c)
      (Term.numeral s) (Term.numeral i)).
Proof.
  intros G c s i o [q [hval hlt]].
  apply (BProv_Ax_s_betaTermTermAt_of_rem G _ _ _ _
    (Term.numeral (BetaModulus s i))).
  - exact (BProv_Ax_s_betaModTermTerm_numeral G s i).
  - apply (BProv_Ax_s_remTermTermAt_numeral_of_modEq G _ o c
      (BetaModulus s i) q).
    + apply BProv_eqRefl.
    + exact hlt.
    + lia.
Qed.

(* Lean: BProv_Ax_s_betaModTermTerm_numeral_eq *)
Lemma BProv_Ax_s_betaModTermTerm_numeral_eq :
  forall G (step idx : nat),
  BProv Ax_s G
    (pEq (betaModTermTerm (Term.numeral step) (Term.numeral idx))
      (Term.numeral (BetaModulus step idx))).
Proof.
  intros G step idx.
  exact (BProv_eqSym Ax_s G _ _
    (BProv_Ax_s_betaModTermTerm_numeral G step idx)).
Qed.

(* Lean: BProv_Ax_s_betaTermTermAt_numeral_of_entry *)
Lemma BProv_Ax_s_betaTermTermAt_numeral_of_entry :
  forall G (out code step idx : nat),
  BetaEntry code step idx out ->
  BProv Ax_s G
    (betaTermTermAt (Term.numeral out) (Term.numeral code)
      (Term.numeral step) (Term.numeral idx)).
Proof.
  intros G out code step idx hentry.
  exact (BProv_Ax_s_betaTermTermAt_numeral_entry
    G code step idx out hentry).
Qed.

(* Lean: BProv_Ax_s_betaTermTermAtConstIdx_numeral_of_entry *)
Lemma BProv_Ax_s_betaTermTermAtConstIdx_numeral_of_entry :
  forall G (out code step idx : nat),
  BetaEntry code step idx out ->
  BProv Ax_s G
    (betaTermTermAtConstIdx (Term.numeral out) (Term.numeral code)
      (Term.numeral step) idx).
Proof.
  intros G out code step idx hentry.
  apply BProv_Ax_s_betaTermTermAtConstIdx_of_beta.
  exact (BProv_Ax_s_betaTermTermAt_numeral_entry
    G code step idx out hentry).
Qed.

(* Lean: BProv_Ax_s_not_lt_zero *)
Lemma BProv_Ax_s_not_lt_zero :
  forall G (t : term),
  BProv Ax_s G (ltTermAt t tZero) -> BProv Ax_s G pBot.
Proof.
  intros G t hlt.
  exact (BProv_Ax_s_ltTermAt_leTermAt_bot G t tZero hlt
    (BProv_Ax_s_leTermAt_zero_left G t)).
Qed.

(* Lean: BProv_Ax_s_eq_zero_of_lt_one *)
Lemma BProv_Ax_s_eq_zero_of_lt_one :
  forall G (t : term),
  BProv Ax_s G (ltTermAt t (Term.numeral 1)) ->
  BProv Ax_s G (pEq t tZero).
Proof.
  intros G t hlt.
  exact (BProv_Ax_s_eq_of_leTermAt_leTermAt G t tZero
    (BProv_Ax_s_leTermAt_of_ltTermAt_succ_right G t tZero hlt)
    (BProv_Ax_s_leTermAt_zero_left G t)).
Qed.

(* Lean: BProv_Ax_s_even_zero *)
Lemma BProv_Ax_s_even_zero : forall G,
  BProv Ax_s G (evenTermAt (Term.numeral 0)).
Proof.
  intros G.
  unfold evenTermAt.
  apply (BProv_exI Ax_s G _ tZero).
  simpl.
  exact (BProv_eqSym Ax_s G _ _ (BProv_Ax_s_zero_add_term G tZero)).
Qed.

(* Lean: BProv_Ax_s_odd_one *)
Lemma BProv_Ax_s_odd_one : forall G,
  BProv Ax_s G (oddTermAt (Term.numeral 1)).
Proof.
  intros G.
  unfold oddTermAt.
  apply (BProv_exI Ax_s G _ tZero).
  simpl.
  exact (BProv_eqSym Ax_s G _ _
    (BProv_eq_congr_succ Ax_s G _ _ (BProv_Ax_s_zero_add_term G tZero))).
Qed.

(* ===== Prime-factorization parity ===== *)

Definition completePrimeFactorizationTraceAt
    (n len code step : term) : formula :=
  pAnd (betaTermTermAtConstIdx n code step 0)
    (pAnd
      (betaTermTermAt (Term.numeral 1) code step len)
      (pAll (pImp
        (ltTermAt (tVar 0) (shiftTerm 1 len))
        (pEx (pAnd
          (primeTermAt (tVar 0))
          (pEx (pAnd
            (betaTermTermAt (tVar 0)
              (shiftTerm 3 code) (shiftTerm 3 step)
              (tSucc (tVar 2)))
            (betaTermTermAt
              (tMul (tVar 1) (tVar 0))
              (shiftTerm 3 code) (shiftTerm 3 step)
              (tVar 2))))))))).

Definition factorizationEvenTraceTermAt (n : term) : formula :=
  pEx (pEx (pEx
    (pAnd
      (completePrimeFactorizationTraceAt
        (shiftTerm 3 n) (tVar 2) (tVar 1) (tVar 0))
      (evenTermAt (tVar 2))))).

Definition factorizationEvenTermAt (n : term) : formula :=
  pOr
    (pEq n (Term.numeral 1))
    (factorizationEvenTraceTermAt n).

Definition factorizationOddTraceTermAt (n : term) : formula :=
  pEx (pEx (pEx
    (pAnd
      (completePrimeFactorizationTraceAt
        (shiftTerm 3 n) (tVar 2) (tVar 1) (tVar 0))
      (oddTermAt (tVar 2))))).

Definition factorizationOddTermAt (n : term) : formula :=
  pOr (pEq n (Term.numeral 2))
    (pOr
      (pEq n (Term.numeral 3))
      (factorizationOddTraceTermAt n)).

Definition mobiusPositiveTermAt (n : term) : formula :=
  pAnd (squarefreeTermAt n) (factorizationEvenTermAt n).

Definition mobiusNegativeTermAt (n : term) : formula :=
  pAnd (squarefreeTermAt n) (factorizationOddTermAt n).

(* Lean: BProv_Ax_s_factorizationEven_one *)
Lemma BProv_Ax_s_factorizationEven_one :
  BProv Ax_s [] (factorizationEvenTermAt (Term.numeral 1)).
Proof.
  unfold factorizationEvenTermAt.
  apply BProv_orI1.
  apply BProv_eqRefl.
Qed.

(* Lean: BProv_Ax_s_factorizationOdd_two *)
Lemma BProv_Ax_s_factorizationOdd_two :
  BProv Ax_s [] (factorizationOddTermAt (Term.numeral 2)).
Proof.
  unfold factorizationOddTermAt.
  apply BProv_orI1.
  apply BProv_eqRefl.
Qed.

(* Lean: BProv_Ax_s_factorizationOdd_three *)
Lemma BProv_Ax_s_factorizationOdd_three :
  BProv Ax_s [] (factorizationOddTermAt (Term.numeral 3)).
Proof.
  unfold factorizationOddTermAt.
  apply BProv_orI2.
  apply BProv_orI1.
  apply BProv_eqRefl.
Qed.

(* Lean: BProv_Ax_s_mobiusPositive_one *)
Lemma BProv_Ax_s_mobiusPositive_one :
  BProv Ax_s [] (mobiusPositiveTermAt (Term.numeral 1)).
Proof.
  unfold mobiusPositiveTermAt.
  apply BProv_andI.
  - exact BProv_Ax_s_squarefree_one.
  - exact BProv_Ax_s_factorizationEven_one.
Qed.

(* Lean: BProv_Ax_s_mobiusNegative_two *)
Lemma BProv_Ax_s_mobiusNegative_two :
  BProv Ax_s [] (mobiusNegativeTermAt (Term.numeral 2)).
Proof.
  unfold mobiusNegativeTermAt.
  apply BProv_andI.
  - exact BProv_Ax_s_squarefree_two.
  - exact BProv_Ax_s_factorizationOdd_two.
Qed.

(* Lean: BProv_Ax_s_mobiusNegative_three *)
Lemma BProv_Ax_s_mobiusNegative_three :
  BProv Ax_s [] (mobiusNegativeTermAt (Term.numeral 3)).
Proof.
  unfold mobiusNegativeTermAt.
  apply BProv_andI.
  - exact BProv_Ax_s_squarefree_three.
  - exact BProv_Ax_s_factorizationOdd_three.
Qed.

(* ===== Prefix-count traces for the Mertens function ===== *)

(* One guarded transition of two synchronized beta-coded traces.  [guard],
   [leftNext], and [rightNext] live under the current-value witnesses
   [leftCur = var 1] and [rightCur = var 0]; the trace index is [var 2]. *)
Definition pairedBetaTraceStepAt
    (leftCode leftStep rightCode rightStep : term)
    (guard : formula) (leftNext rightNext : term) : formula :=
  let leftCode' := shiftTerm 2 leftCode in
  let leftStep' := shiftTerm 2 leftStep in
  let rightCode' := shiftTerm 2 rightCode in
  let rightStep' := shiftTerm 2 rightStep in
  let leftCur := tVar 1 in
  let rightCur := tVar 0 in
  let i' := tVar 2 in
  pEx (pEx (pAnd guard
    (pAnd
      (betaTermTermAt leftCur leftCode' leftStep' i')
      (pAnd
        (betaTermTermAt leftNext leftCode' leftStep' (tSucc i'))
        (pAnd
          (betaTermTermAt rightCur rightCode' rightStep' i')
          (betaTermTermAt rightNext rightCode' rightStep'
            (tSucc i'))))))).

Definition mertensCountStepAt
    (posCode posStep negCode negStep : term) : formula :=
  let posCur := tVar 1 in
  let negCur := tVar 0 in
  let k' := tSucc (tVar 2) in
  let positiveUpdate :=
    pairedBetaTraceStepAt posCode posStep negCode negStep
      (mobiusPositiveTermAt k') (tSucc posCur) negCur in
  let negativeUpdate :=
    pairedBetaTraceStepAt posCode posStep negCode negStep
      (mobiusNegativeTermAt k') posCur (tSucc negCur) in
  let zeroUpdate :=
    pairedBetaTraceStepAt posCode posStep negCode negStep
      (pAnd (notF (mobiusPositiveTermAt k'))
        (notF (mobiusNegativeTermAt k')))
      posCur negCur in
  pOr positiveUpdate (pOr negativeUpdate zeroUpdate).

Definition mertensCountsTraceAt
    (n pos neg posCode posStep negCode negStep : term) : formula :=
  pAnd (betaTermTermAtConstIdx (Term.numeral 0) posCode posStep 0)
    (pAnd (betaTermTermAtConstIdx (Term.numeral 0) negCode negStep 0)
      (pAnd (betaTermTermAt pos posCode posStep n)
        (pAnd (betaTermTermAt neg negCode negStep n)
          (pAll (pImp
            (ltTermAt (tVar 0) (shiftTerm 1 n))
            (mertensCountStepAt
              (shiftTerm 1 posCode) (shiftTerm 1 posStep)
              (shiftTerm 1 negCode) (shiftTerm 1 negStep))))))).

Definition mertensCountsTraceExistsAt
    (n pos neg : term) : formula :=
  pEx (pEx (pEx (pEx
    (mertensCountsTraceAt
      (shiftTerm 4 n) (shiftTerm 4 pos) (shiftTerm 4 neg)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))))).

Definition mertensCountsBaseAt
    (n pos neg : term)
    (nValue posValue negValue : nat) : formula :=
  pAnd (pEq n (Term.numeral nValue))
    (pAnd (pEq pos (Term.numeral posValue))
      (pEq neg (Term.numeral negValue))).

Definition mertensCountsAt
    (n pos neg : term) : formula :=
  pOr (mertensCountsBaseAt n pos neg 1 1 0)
    (pOr (mertensCountsBaseAt n pos neg 2 1 1)
      (pOr (mertensCountsBaseAt n pos neg 3 1 2)
        (mertensCountsTraceExistsAt n pos neg))).

Definition mertensOneEqOneStatement : formula :=
  pAnd
    (mertensCountsAt
      (Term.numeral 1) (Term.numeral 1) (Term.numeral 0))
    (pEq (Term.numeral 1)
      (tAdd (Term.numeral 0) (Term.numeral 1))).

Definition mertensTwoEqZeroStatement : formula :=
  pAnd
    (mertensCountsAt
      (Term.numeral 2) (Term.numeral 1) (Term.numeral 1))
    (pEq (Term.numeral 1) (Term.numeral 1)).

Definition mertensThreeEqNegOneStatement : formula :=
  pAnd
    (mertensCountsAt
      (Term.numeral 3) (Term.numeral 1) (Term.numeral 2))
    (pEq (Term.numeral 2)
      (tAdd (Term.numeral 1) (Term.numeral 1))).

(* Lean: BProv_Ax_s_mertensCountsBase_numerals *)
Lemma BProv_Ax_s_mertensCountsBase_numerals :
  forall G (n pos neg : nat),
  BProv Ax_s G
    (mertensCountsBaseAt
      (Term.numeral n) (Term.numeral pos) (Term.numeral neg) n pos neg).
Proof.
  intros G n pos neg.
  unfold mertensCountsBaseAt.
  apply BProv_andI; [apply BProv_eqRefl|].
  apply BProv_andI; apply BProv_eqRefl.
Qed.

(* Lean: BProv_Ax_s_mertensCounts_one *)
Lemma BProv_Ax_s_mertensCounts_one :
  BProv Ax_s []
    (mertensCountsAt (Term.numeral 1) (Term.numeral 1) (Term.numeral 0)).
Proof.
  unfold mertensCountsAt.
  apply BProv_orI1.
  apply BProv_Ax_s_mertensCountsBase_numerals.
Qed.

(* Lean: BProv_Ax_s_mertensCounts_two *)
Lemma BProv_Ax_s_mertensCounts_two :
  BProv Ax_s []
    (mertensCountsAt (Term.numeral 2) (Term.numeral 1) (Term.numeral 1)).
Proof.
  unfold mertensCountsAt.
  apply BProv_orI2.
  apply BProv_orI1.
  apply BProv_Ax_s_mertensCountsBase_numerals.
Qed.

(* Lean: BProv_Ax_s_mertensCounts_three *)
Lemma BProv_Ax_s_mertensCounts_three :
  BProv Ax_s []
    (mertensCountsAt (Term.numeral 3) (Term.numeral 1) (Term.numeral 2)).
Proof.
  unfold mertensCountsAt.
  apply BProv_orI2.
  apply BProv_orI2.
  apply BProv_orI1.
  apply BProv_Ax_s_mertensCountsBase_numerals.
Qed.

(* Lean: BProv_Ax_s_mertens_one_eq_one *)
Lemma BProv_Ax_s_mertens_one_eq_one :
  BProv Ax_s [] mertensOneEqOneStatement.
Proof.
  unfold mertensOneEqOneStatement.
  apply BProv_andI.
  - exact BProv_Ax_s_mertensCounts_one.
  - exact (BProv_eqSym Ax_s [] _ _ (BProv_Ax_s_addNumerals [] 0 1)).
Qed.

(* Lean: BProv_Ax_s_mertens_two_eq_zero *)
Lemma BProv_Ax_s_mertens_two_eq_zero :
  BProv Ax_s [] mertensTwoEqZeroStatement.
Proof.
  unfold mertensTwoEqZeroStatement.
  apply BProv_andI.
  - exact BProv_Ax_s_mertensCounts_two.
  - apply BProv_eqRefl.
Qed.

(* Lean: BProv_Ax_s_mertens_three_eq_neg_one *)
Lemma BProv_Ax_s_mertens_three_eq_neg_one :
  BProv Ax_s [] mertensThreeEqNegOneStatement.
Proof.
  unfold mertensThreeEqNegOneStatement.
  apply BProv_andI.
  - exact BProv_Ax_s_mertensCounts_three.
  - exact (BProv_eqSym Ax_s [] _ _ (BProv_Ax_s_addNumerals [] 1 1)).
Qed.

(* ===== Power traces and the arithmetized RH growth bound ===== *)

Definition powTraceAt
    (base exp out code step : term) : formula :=
  pAnd (betaTermTermAtConstIdx (Term.numeral 1) code step 0)
    (pAnd (betaTermTermAt out code step exp)
      (pAll (pImp
        (ltTermAt (tVar 0) (shiftTerm 1 exp))
        (pEx (pAnd
          (betaTermTermAt (tVar 0) (shiftTerm 2 code)
            (shiftTerm 2 step) (tVar 1))
          (betaTermTermAt
            (tMul (tVar 0) (shiftTerm 2 base))
            (shiftTerm 2 code) (shiftTerm 2 step)
            (tSucc (tVar 1)))))))).

Definition powRelAt (base exp out : term) : formula :=
  pEx (pEx
    (powTraceAt
      (shiftTerm 2 base)
      (shiftTerm 2 exp)
      (shiftTerm 2 out)
      (tVar 1)
      (tVar 0))).

Definition mertensPowerBoundAt
    (n q C pos neg : term) : formula :=
  let diff := tVar 0 in
  pEx (pAnd
    (pOr
      (pEq (tAdd (shiftTerm 1 pos) diff) (shiftTerm 1 neg))
      (pEq (tAdd (shiftTerm 1 neg) diff) (shiftTerm 1 pos)))
    (pEx (pAnd
      (powRelAt (tVar 1)
        (tMul (Term.numeral 2) (shiftTerm 2 q))
        (tVar 0))
      (pEx (pAnd
        (powRelAt (shiftTerm 3 n)
          (tSucc (shiftTerm 3 q))
          (tVar 0))
        (leTermAt (tVar 1)
          (tMul (shiftTerm 3 C) (tVar 0)))))))).

Definition mertensBoundAt (n q C : term) : formula :=
  pEx (pEx (pAnd
    (mertensCountsAt (shiftTerm 2 n) (tVar 1) (tVar 0))
    (mertensPowerBoundAt
      (shiftTerm 2 n) (shiftTerm 2 q) (shiftTerm 2 C)
      (tVar 1) (tVar 0)))).

Definition mertensRiemannHypothesisBody : formula :=
  pAll (pImp (nonzeroAt 0)
    (pEx (pAll
      (mertensBoundAt (tVar 0) (tVar 2) (tVar 1))))).

Definition mertensRiemannHypothesisSentence : formula :=
  sealPA mertensRiemannHypothesisBody.

Theorem mertensRiemannHypothesisSentence_sentence :
  Sentence mertensRiemannHypothesisSentence.
Proof.
  unfold mertensRiemannHypothesisSentence.
  apply sealPA_sentence.
Qed.
