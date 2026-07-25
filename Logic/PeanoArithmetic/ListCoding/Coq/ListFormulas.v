(**
  First-order PA formulae for the canonical list coding from [ListCode].

  A beta table is used only as a finite certificate for following the
  strictly decreasing tail codes.  The public code of a list is the single,
  canonical number [PAListCode.listCode xs]; beta parameters never form part
  of that public code.
*)

From Stdlib Require Import
  List Arith Lia Bool PeanoNat
  Sorting.Permutation Sorting.Sorted.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.

Import ListNotations.

Module PAListFormulas.

Import PA.
Import PAListCode.
Import PAListRepresentability.

Definition pairTerm (a b : term) : term :=
  tAdd (tMul (tAdd a b) (tAdd a b)) a.

Definition nodeTerm (head tail : term) : term :=
  tSucc (pairTerm head tail).

Lemma eval_pairTerm : forall e a b,
  Term.eval natModel e (pairTerm a b) =
    polynomialPair (Term.eval natModel e a) (Term.eval natModel e b).
Proof. reflexivity. Qed.

Lemma eval_nodeTerm : forall e a b,
  Term.eval natModel e (nodeTerm a b) =
    S (polynomialPair (Term.eval natModel e a)
      (Term.eval natModel e b)).
Proof. reflexivity. Qed.

Definition pAnd3 (a b c : formula) : formula :=
  pAnd a (pAnd b c).

Definition pAnd4 (a b c d : formula) : formula :=
  pAnd a (pAnd b (pAnd c d)).

Definition pAnd5 (a b c d f : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d f))).

Definition pAnd6 (a b c d f g : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd f g)))).

Definition pEx3 (body : formula) : formula := pEx (pEx (pEx body)).
Definition pEx4 (body : formula) : formula := pEx (pEx (pEx (pEx body))).

(** One constructor edge in a beta-certified tail trace. *)
Definition listStepTermAt
    (cur next head code step index : term) : formula :=
  pAnd3
    (Formula.betaTermTermAt cur code step index)
    (Formula.betaTermTermAt next code step (tSucc index))
    (pEq cur (nodeTerm head next)).

(** [listTraceFromTermAt p start len code step] follows [len] constructor
    edges, starting with tail code [p] at beta index [start], and ends at
    the empty-list code zero. *)
Definition listTraceFromTermAt
    (p start len code step : term) : formula :=
  pAnd3
    (Formula.betaTermTermAt p code step start)
    (Formula.betaTermTermAt tZero code step (tAdd start len))
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 len))
        (pEx3
          (listStepTermAt
            (tVar 2) (tVar 1) (tVar 0)
            (liftTerm 4 code) (liftTerm 4 step)
            (tAdd (liftTerm 4 start) (tVar 3)))))).

Definition ListTraceFrom
    (p start len code step : nat) : Prop :=
  Formula.BetaEntry code step start p /\
  Formula.BetaEntry code step (start + len) 0 /\
  forall i, i < len ->
    exists cur next head,
      Formula.BetaEntry code step (start + i) cur /\
      Formula.BetaEntry code step (S (start + i)) next /\
      cur = S (polynomialPair head next).

(** Discharges every [eval_liftTerm_sconsN] goal uniformly: after the
    rename/extensionality step the goal is [sconsN-env (i + N) = e i], and
    normalizing [i + N] to [S (S (... i))] lets [scons] reduce away.  The
    arity-generic statement is [eval_liftTerm] in [Representability]. *)
Ltac solve_eval_liftTerm :=
  intros; unfold liftTerm; rewrite Term.eval_rename;
  apply Term.eval_ext; let i := fresh "i" in intro i;
  repeat rewrite Nat.add_succ_r; rewrite Nat.add_0_r; reflexivity.

Lemma eval_liftTerm_scons : forall x e t,
  Term.eval natModel (scons nat x e) (liftTerm 1 t) =
  Term.eval natModel e t.
Proof. solve_eval_liftTerm. Qed.

Lemma eval_liftTerm_scons2 : forall a b e t,
  Term.eval natModel (scons nat a (scons nat b e)) (liftTerm 2 t) =
  Term.eval natModel e t.
Proof. solve_eval_liftTerm. Qed.

Lemma eval_liftTerm_scons3 : forall a b c e t,
  Term.eval natModel (scons nat a (scons nat b (scons nat c e)))
    (liftTerm 3 t) = Term.eval natModel e t.
Proof. solve_eval_liftTerm. Qed.

Lemma eval_liftTerm_scons4 : forall a b c d e t,
  Term.eval natModel
    (scons nat a (scons nat b (scons nat c (scons nat d e))))
    (liftTerm 4 t) =
  Term.eval natModel e t.
Proof. solve_eval_liftTerm. Qed.

Lemma eval_liftTerm_scons5 : forall a b c d f e t,
  Term.eval natModel
    (scons nat a (scons nat b (scons nat c (scons nat d (scons nat f e)))))
    (liftTerm 5 t) = Term.eval natModel e t.
Proof. solve_eval_liftTerm. Qed.

Lemma eval_liftTerm_scons6 : forall a b c d f g e t,
  Term.eval natModel
    (scons nat a (scons nat b (scons nat c
      (scons nat d (scons nat f (scons nat g e))))))
    (liftTerm 6 t) = Term.eval natModel e t.
Proof. solve_eval_liftTerm. Qed.

Lemma eval_liftTerm_scons7 : forall a b c d f g h e t,
  Term.eval natModel
    (scons nat a (scons nat b (scons nat c (scons nat d
      (scons nat f (scons nat g (scons nat h e)))))))
    (liftTerm 7 t) = Term.eval natModel e t.
Proof. solve_eval_liftTerm. Qed.

Lemma listStepTermAt_nat : forall e cur next head code step index,
  Formula.Sat natModel e
    (listStepTermAt cur next head code step index) <->
  Formula.BetaEntry
      (Term.eval natModel e code) (Term.eval natModel e step)
      (Term.eval natModel e index) (Term.eval natModel e cur) /\
  Formula.BetaEntry
      (Term.eval natModel e code) (Term.eval natModel e step)
      (S (Term.eval natModel e index)) (Term.eval natModel e next) /\
  Term.eval natModel e cur =
    S (polynomialPair (Term.eval natModel e head)
      (Term.eval natModel e next)).
Proof.
  intros. unfold listStepTermAt, pAnd3.
  cbn [Formula.Sat].
  rewrite !Formula.betaTermTermAt_nat_entry.
  rewrite eval_nodeTerm. reflexivity.
Qed.

Lemma listTraceFromTermAt_nat : forall e p start len code step,
  Formula.Sat natModel e
    (listTraceFromTermAt p start len code step) <->
  ListTraceFrom
    (Term.eval natModel e p) (Term.eval natModel e start)
    (Term.eval natModel e len) (Term.eval natModel e code)
    (Term.eval natModel e step).
Proof.
  intros e p start len code step.
  unfold listTraceFromTermAt, ListTraceFrom, pAnd3.
  cbn [Formula.Sat].
  rewrite !Formula.betaTermTermAt_nat_entry.
  split.
  - intros [hstart [hend hall]].
    split; [exact hstart |]. split.
    + replace (Term.eval natModel e start + Term.eval natModel e len)
        with (Term.eval natModel e (tAdd start len)) by reflexivity.
      exact hend.
    + intros i hi.
      assert (hlt : Formula.Sat natModel (scons nat i e)
          (Formula.ltTermAt (tVar 0) (liftTerm 1 len))).
      {
        apply (proj2 (Formula.ltTermAt_nat _ _ _)).
        simpl. rewrite eval_liftTerm_scons. exact hi.
      }
      destruct (hall i hlt) as [cur [next [head hbody]]].
      pose proof (proj1 (listStepTermAt_nat
        (scons nat head (scons nat next (scons nat cur (scons nat i e))))
        (tVar 2) (tVar 1) (tVar 0)
        (liftTerm 4 code) (liftTerm 4 step)
        (tAdd (liftTerm 4 start) (tVar 3))) hbody) as hs.
      simpl in hs.
      repeat rewrite eval_liftTerm_scons4 in hs.
      exists cur, next, head.
      replace (Term.eval natModel e start + i)
        with (Term.eval natModel e start + i) by reflexivity.
      exact hs.
  - intros [hstart [hend hall]].
    split; [exact hstart |]. split.
    + change (Formula.BetaEntry
        (Term.eval natModel e code) (Term.eval natModel e step)
        (Term.eval natModel e start + Term.eval natModel e len) 0).
      exact hend.
    + intros i hlt.
      pose proof (proj1 (Formula.ltTermAt_nat
        (scons nat i e) (tVar 0) (liftTerm 1 len)) hlt) as hi.
      simpl in hi. rewrite eval_liftTerm_scons in hi.
      destruct (hall i hi) as [cur [next [head hs]]].
      exists cur, next, head.
      apply (proj2 (listStepTermAt_nat
        (scons nat head (scons nat next (scons nat cur (scons nat i e))))
        (tVar 2) (tVar 1) (tVar 0)
        (liftTerm 4 code) (liftTerm 4 step)
        (tAdd (liftTerm 4 start) (tVar 3)))).
      simpl.
      repeat rewrite eval_liftTerm_scons4.
      exact hs.
Qed.

(** A trace beginning at index zero. *)
Definition listTraceTermAt (p len code step : term) : formula :=
  listTraceFromTermAt p tZero len code step.

Definition ListTrace (p len code step : nat) : Prop :=
  ListTraceFrom p 0 len code step.

Lemma listTraceTermAt_nat : forall e p len code step,
  Formula.Sat natModel e (listTraceTermAt p len code step) <->
  ListTrace
    (Term.eval natModel e p) (Term.eval natModel e len)
    (Term.eval natModel e code) (Term.eval natModel e step).
Proof.
  intros. unfold listTraceTermAt, ListTrace.
  rewrite listTraceFromTermAt_nat. simpl. reflexivity.
Qed.

(** A trace is an exact finite traversal of constructor codes.  The final
    conjunct records every intermediate tail code; it is the key fact used
    by the [nth] formula below. *)
Lemma ListTraceFrom_sound : forall len p start code step,
  ListTraceFrom p start len code step ->
  exists xs,
    length xs = len /\
    p = listCode xs /\
    forall i, i <= len ->
      Formula.BetaEntry code step (start + i)
        (listCode (skipn i xs)).
Proof.
  induction len as [|len IH]; intros p start code step htrace.
  - destruct htrace as [hstart [hend _]].
    assert (hp : p = 0).
    {
      apply (Formula.BetaEntry_functional code step start).
      - exact hstart.
      - replace start with (start + 0) by lia. exact hend.
    }
    exists []. split; [reflexivity |]. split.
    + exact hp.
    + intros i hi. assert (i = 0) by lia. subst i. simpl.
      rewrite hp in hstart.
      replace (start + 0) with start by lia. exact hstart.
  - destruct htrace as [hstart [hend hall]].
    destruct (hall 0 ltac:(lia)) as
      [cur [next [head [hcur [hnext hnode]]]]].
    assert (hpcur : p = cur).
    {
      apply (Formula.BetaEntry_functional code step start).
      - exact hstart.
      - replace start with (start + 0) by lia. exact hcur.
    }
    assert (hsub : ListTraceFrom next (S start) len code step).
    {
      split.
      - replace (S start) with (S (start + 0)) by lia. exact hnext.
      - split.
        + replace (S start + len) with (start + S len) by lia.
          exact hend.
        + intros i hi.
          destruct (hall (S i) ltac:(lia)) as
            [cur' [next' [head' [hc [hn heq]]]]].
          exists cur', next', head'.
          replace (S start + i) with (start + S i) by lia.
          replace (S (S start + i)) with (S (start + S i)) by lia.
          repeat split; assumption.
    }
    destruct (IH next (S start) code step hsub) as
      [xs [hlen [hnextCode hentries]]].
    assert (hpcode : p = listCode (head :: xs)).
    { simpl. rewrite <- hnextCode, <- hnode, <- hpcur. reflexivity. }
    exists (head :: xs). split.
    + simpl. now rewrite hlen.
    + split.
      * exact hpcode.
      * intros i hi. destruct i as [|i].
        -- change (Formula.BetaEntry code step (start + 0)
             (listCode (head :: xs))). rewrite <- hpcode.
           replace (start + 0) with start by lia. exact hstart.
        -- simpl skipn. specialize (hentries i ltac:(lia)).
           replace (start + S i) with (S start + i) by lia.
           exact hentries.
Qed.

Corollary ListTrace_sound : forall p len code step,
  ListTrace p len code step ->
  exists xs,
    length xs = len /\
    p = listCode xs /\
    forall i, i <= len ->
      Formula.BetaEntry code step i (listCode (skipn i xs)).
Proof.
  intros p len code step h.
  destruct (ListTraceFrom_sound len p 0 code step h) as
    [xs [hlen [hp hentries]]].
  exists xs. repeat split; try assumption.
Qed.

Lemma listCode_skipn_le : forall xs i,
  listCode (skipn i xs) <= listCode xs.
Proof.
  intros xs i. revert xs. induction i as [|i IH]; intros xs.
  - simpl. lia.
  - destruct xs as [|x xs].
    + simpl. lia.
    + simpl skipn. specialize (IH xs).
      pose proof (listCode_tail_lt x xs). lia.
Qed.

Lemma skipn_step : forall (xs : list nat) i,
  i < length xs ->
  exists head tail,
    skipn i xs = head :: tail /\
    skipn (S i) xs = tail.
Proof.
  intros xs i hi.
  destruct (skipn i xs) as [|head tail] eqn:hskip.
  - pose proof (length_skipn i xs).
    rewrite hskip in H. simpl in H. lia.
  - exists head, tail. split; [reflexivity |].
    pose proof (skipn_skipn 1 i xs) as h.
    rewrite hskip in h. simpl in h.
    replace (1 + i) with (S i) in h by lia. symmetry. exact h.
Qed.

Lemma ListTrace_complete : forall xs,
  exists code step,
    ListTrace (listCode xs) (length xs) code step /\
    forall i, i <= length xs ->
      Formula.BetaEntry code step i (listCode (skipn i xs)).
Proof.
  intro xs.
  set (n := length xs).
  set (scale := S (listCode xs)).
  set (step := Formula.betaFact n * scale).
  destruct (Formula.beta_entries_exist_through_mul_betaFact
    n scale (fun i => listCode (skipn i xs))) as [code hcode].
  {
    intros i hi. unfold Formula.BetaModulus.
    pose proof (listCode_skipn_le xs i).
    pose proof (Formula.betaFact_pos n).
    unfold step, scale. nia.
  }
  exists code, step. split.
  - unfold ListTrace, ListTraceFrom. split.
    + replace (listCode xs) with (listCode (skipn 0 xs)) by reflexivity.
      apply hcode. unfold n. lia.
    + split.
      * change (Formula.BetaEntry code step (length xs) 0).
        specialize (hcode (length xs) ltac:(unfold n; lia)).
        rewrite skipn_all in hcode. exact hcode.
      * intros i hi.
        destruct (skipn_step xs i hi) as
          [head [tail [hcurCode hnextCode]]].
        exists (listCode (skipn i xs)),
          (listCode (skipn (S i) xs)), head.
        split.
        -- replace (0 + i) with i by lia. apply hcode. unfold n. lia.
        -- split.
           ++ replace (S (0 + i)) with (S i) by lia.
              apply hcode. unfold n. lia.
           ++ rewrite hcurCode, hnextCode. reflexivity.
  - intros i hi. apply hcode. unfold n. exact hi.
Qed.

(** Length and validity formulae.  Quantifier order is beta step, beta code,
    then length in the innermost displayed body. *)
Definition hasLengthTermAt (v n : term) : formula :=
  pEx (pEx
    (listTraceTermAt
      (liftTerm 2 v) (liftTerm 2 n) (tVar 0) (tVar 1))).

Definition validCodeTermAt (v : term) : formula :=
  pEx (hasLengthTermAt (liftTerm 1 v) (tVar 0)).

Definition nthElementTermAt (v k m : term) : formula :=
  pEx4
    (pAnd3
      (listTraceTermAt
        (liftTerm 4 v) (tVar 3) (tVar 1) (tVar 2))
      (Formula.ltTermAt (liftTerm 4 k) (tVar 3))
      (Formula.betaTermTermAt
        (nodeTerm (liftTerm 4 m) (tVar 0))
        (tVar 1) (tVar 2) (liftTerm 4 k))).

(** The four witnesses above, from innermost to outermost, are the tail
    code at position [k], the beta code, the beta step, and the length. *)

Lemma hasLengthTermAt_nat : forall e v n,
  Formula.Sat natModel e (hasLengthTermAt v n) <->
  HasLength (Term.eval natModel e v) (Term.eval natModel e n).
Proof.
  intros e v n. unfold hasLengthTermAt.
  cbn [Formula.Sat]. split.
  - intros [step [code htrace]].
    apply (proj1 (listTraceTermAt_nat
      (scons nat code (scons nat step e))
      (liftTerm 2 v) (liftTerm 2 n) (tVar 0) (tVar 1))) in htrace.
    simpl in htrace. repeat rewrite eval_liftTerm_scons2 in htrace.
    destruct (ListTrace_sound _ _ _ _ htrace) as
      [xs [hlen [hv _]]].
    exists xs. split.
    + apply decode_some_iff_listCode. symmetry. exact hv.
    + exact hlen.
  - intros [xs [hdecode hlen]].
    destruct (ListTrace_complete xs) as [code [step [htrace _]]].
    exists step, code.
    apply (proj2 (listTraceTermAt_nat
      (scons nat code (scons nat step e))
      (liftTerm 2 v) (liftTerm 2 n) (tVar 0) (tVar 1))).
    simpl. repeat rewrite eval_liftTerm_scons2.
    apply decode_some_iff_listCode in hdecode.
    rewrite <- hdecode, <- hlen. exact htrace.
Qed.

Lemma validCodeTermAt_nat : forall e v,
  Formula.Sat natModel e (validCodeTermAt v) <->
  ValidCode (Term.eval natModel e v).
Proof.
  intros e v. unfold validCodeTermAt. cbn [Formula.Sat].
  split.
  - intros [n hn].
    apply (proj1 (hasLengthTermAt_nat
      (scons nat n e) (liftTerm 1 v) (tVar 0))) in hn.
    simpl in hn. rewrite eval_liftTerm_scons in hn.
    exact (HasLength_valid _ _ hn).
  - intros [xs hdecode]. exists (length xs).
    apply (proj2 (hasLengthTermAt_nat
      (scons nat (length xs) e) (liftTerm 1 v) (tVar 0))).
    simpl. rewrite eval_liftTerm_scons. exists xs. now split.
Qed.

Lemma nthElementTermAt_nat : forall e v k m,
  Formula.Sat natModel e (nthElementTermAt v k m) <->
  NthElement (Term.eval natModel e v)
    (Term.eval natModel e k) (Term.eval natModel e m).
Proof.
  intros e v k m. unfold nthElementTermAt, pEx4, pAnd3.
  cbn [Formula.Sat]. split.
  - intros [len [step [code [tail [htrace [hlt hentry]]]]]].
    apply (proj1 (listTraceTermAt_nat
      (scons nat tail (scons nat code (scons nat step (scons nat len e))))
      (liftTerm 4 v) (tVar 3) (tVar 1) (tVar 2))) in htrace.
    simpl in htrace. repeat rewrite eval_liftTerm_scons4 in htrace.
    apply (proj1 (Formula.ltTermAt_nat _ _ _)) in hlt.
    simpl in hlt. repeat rewrite eval_liftTerm_scons4 in hlt.
    apply (proj1 (Formula.betaTermTermAt_nat_entry _ _ _ _ _)) in hentry.
    simpl in hentry. repeat rewrite eval_liftTerm_scons4 in hentry.
    destruct (ListTrace_sound _ _ _ _ htrace) as
      [xs [hlen [hv hentries]]].
    assert (hk : Term.eval natModel e k < length xs) by lia.
    destruct (skipn_step xs (Term.eval natModel e k) hk) as
      [head [rest [hskip _]]].
    specialize (hentries (Term.eval natModel e k) ltac:(lia)).
    assert (heq := Formula.BetaEntry_functional code step
      (Term.eval natModel e k) _ _ hentries hentry).
    rewrite hskip in heq. simpl in heq.
    inversion heq as [hpair].
    destruct (polynomialPair_injective head (listCode rest)
      (Term.eval natModel e m) tail hpair) as [hhead _].
    exists xs. split.
    + apply decode_some_iff_listCode. symmetry. exact hv.
    + rewrite <- hd_error_skipn, hskip. simpl. now rewrite hhead.
  - intros [xs [hdecode hnth]].
    apply decode_some_iff_listCode in hdecode.
    assert (hk : Term.eval natModel e k < length xs).
    { apply nth_error_Some. rewrite hnth. discriminate. }
    destruct (skipn_step xs (Term.eval natModel e k) hk) as
      [head [rest [hskip hskipS]]].
    assert (hhead : head = Term.eval natModel e m).
    {
      rewrite <- hd_error_skipn, hskip in hnth. simpl in hnth.
      inversion hnth. reflexivity.
    }
    destruct (ListTrace_complete xs) as
      [code [step [htrace hentries]]].
    exists (length xs), step, code, (listCode rest).
    split.
    + apply (proj2 (listTraceTermAt_nat
        (scons nat (listCode rest)
          (scons nat code (scons nat step (scons nat (length xs) e))))
        (liftTerm 4 v) (tVar 3) (tVar 1) (tVar 2))).
      simpl. repeat rewrite eval_liftTerm_scons4.
      rewrite <- hdecode. exact htrace.
    + split.
      * apply (proj2 (Formula.ltTermAt_nat _ _ _)).
        simpl. repeat rewrite eval_liftTerm_scons4. exact hk.
      * apply (proj2 (Formula.betaTermTermAt_nat_entry _ _ _ _ _)).
        simpl. repeat rewrite eval_liftTerm_scons4.
        specialize (hentries (Term.eval natModel e k) ltac:(lia)).
        rewrite hskip in hentries. simpl in hentries.
        rewrite <- hhead. exact hentries.
Qed.

(** Elementary consequences of the two projection predicates. *)
Lemma HasLength_decode : forall v n xs,
  decode v = Some xs -> (HasLength v n <-> length xs = n).
Proof.
  intros v n xs hdecode. split.
  - intros [ys [hy hlen]].
    pose proof (decode_functional v ys xs hy hdecode). subst ys. exact hlen.
  - intro hlen. exists xs. now split.
Qed.

Lemma NthElement_decode : forall v k m xs,
  decode v = Some xs -> (NthElement v k m <-> nth_error xs k = Some m).
Proof.
  intros v k m xs hdecode. split.
  - intros [ys [hy hnth]].
    pose proof (decode_functional v ys xs hy hdecode). subst ys. exact hnth.
  - intro hnth. exists xs. now split.
Qed.

Definition singletonTermAt (v m : term) : formula :=
  pAnd
    (hasLengthTermAt v (Term.numeral 1))
    (nthElementTermAt v tZero m).

Lemma singletonTermAt_nat : forall e v m,
  Formula.Sat natModel e (singletonTermAt v m) <->
  SingletonCode (Term.eval natModel e v) (Term.eval natModel e m).
Proof.
  intros e v m. unfold singletonTermAt.
  cbn [Formula.Sat]. rewrite hasLengthTermAt_nat, nthElementTermAt_nat.
  split.
  - intros [[xs [hdecode hlen]] hnth].
    apply (NthElement_decode _ _ _ xs hdecode) in hnth.
    destruct xs as [|x xs]; simpl in hlen; try lia.
    destruct xs as [|y ys]; simpl in hlen; try lia.
    simpl in hnth. inversion hnth. subst x. exact hdecode.
  - intro hdecode. split.
    + exists [Term.eval natModel e m]. split; [exact hdecode | reflexivity].
    + exists [Term.eval natModel e m]. split; [exact hdecode | reflexivity].
Qed.

(** Position-wise characterization of append. *)
Definition ConcatPosition (v t u : nat) : Prop :=
  exists nt nu,
    HasLength t nt /\ HasLength u nu /\ HasLength v (nt + nu) /\
    (forall i m, i < nt -> NthElement t i m -> NthElement v i m) /\
    (forall i m, i < nu -> NthElement u i m ->
      NthElement v (nt + i) m).

Definition concatTermAt (v t u : term) : formula :=
  pEx (pEx
    (pAnd5
      (hasLengthTermAt (liftTerm 2 t) (tVar 1))
      (hasLengthTermAt (liftTerm 2 u) (tVar 0))
      (hasLengthTermAt (liftTerm 2 v) (tAdd (tVar 1) (tVar 0)))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 2))
          (pAll
            (pImp
              (nthElementTermAt (liftTerm 4 t) (tVar 1) (tVar 0))
              (nthElementTermAt (liftTerm 4 v) (tVar 1) (tVar 0))))))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 1))
          (pAll
            (pImp
              (nthElementTermAt (liftTerm 4 u) (tVar 1) (tVar 0))
              (nthElementTermAt (liftTerm 4 v)
                (tAdd (tVar 3) (tVar 1)) (tVar 0)))))))).

Lemma concatTermAt_position : forall e v t u,
  Formula.Sat natModel e (concatTermAt v t u) <->
  ConcatPosition (Term.eval natModel e v)
    (Term.eval natModel e t) (Term.eval natModel e u).
Proof.
  intros e v t u. unfold concatTermAt, ConcatPosition, pAnd5.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn.
  setoid_rewrite eval_liftTerm_scons2.
  setoid_rewrite eval_liftTerm_scons4.
  split.
  - intros [nt [nu [ht [hu [hv [hleft hright]]]]]].
    exists nt, nu. repeat split; try assumption.
    + intros i m hi hm. exact (hleft i hi m hm).
    + intros i m hi hm. exact (hright i hi m hm).
  - intros [nt [nu [ht [hu [hv [hleft hright]]]]]].
    exists nt, nu. repeat split; try assumption.
    + intros i hi m hm. exact (hleft i m hi hm).
    + intros i hi m hm. exact (hright i m hi hm).
Qed.

Lemma nth_error_exists_of_lt {A : Type} : forall (xs : list A) i,
  i < length xs -> exists m, nth_error xs i = Some m.
Proof.
  intros xs i hi. destruct (nth_error xs i) as [m|] eqn:h.
  - now exists m.
  - apply nth_error_None in h. lia.
Qed.

Lemma ConcatPosition_iff : forall v t u,
  ConcatPosition v t u <-> ConcatenationCode v t u.
Proof.
  intros v t u. split.
  - intros [nt [nu [ht [hu [hv [hleft hright]]]]]].
    destruct ht as [ys [ht hnty]].
    destruct hu as [zs [hu hnuz]].
    destruct hv as [xs [hv hnvx]].
    exists xs, ys, zs. repeat split; try assumption.
    apply nth_error_ext. intro j.
    assert (hlen : length xs = length ys + length zs) by lia.
    destruct (lt_dec j (length xs)) as [hjx | hjx].
    + destruct (lt_dec j (length ys)) as [hjy | hjy].
      * destruct (nth_error_exists_of_lt ys j hjy) as [m hm].
        assert (htnth : NthElement t j m).
        { apply (NthElement_decode t j m ys ht). exact hm. }
        specialize (hleft j m ltac:(lia) htnth).
        apply (NthElement_decode v j m xs hv) in hleft.
        rewrite hleft. rewrite nth_error_app1 by exact hjy.
        symmetry. exact hm.
      * set (q := j - length ys).
        assert (hq : q < length zs) by (unfold q; lia).
        destruct (nth_error_exists_of_lt zs q hq) as [m hm].
        assert (hunth : NthElement u q m).
        { apply (NthElement_decode u q m zs hu). exact hm. }
        specialize (hright q m ltac:(lia) hunth).
        assert (hindex : nt + q = j) by (unfold q; lia).
        rewrite hindex in hright.
        apply (NthElement_decode v j m xs hv) in hright.
        rewrite hright. symmetry.
        rewrite nth_error_app2 by lia. unfold q. exact hm.
    + assert (hxnone : nth_error xs j = None).
      { apply nth_error_None. lia. }
      assert (happnone : nth_error (ys ++ zs) j = None).
      { apply nth_error_None. rewrite app_length. lia. }
      now rewrite hxnone, happnone.
  - intros [xs [ys [zs [hv [ht [hu hcat]]]]]].
    exists (length ys), (length zs). repeat split.
    + exists ys. now split.
    + exists zs. now split.
    + exists xs. split; [exact hv |]. subst xs. rewrite app_length. lia.
    + intros i m hi htnth.
      apply (NthElement_decode t i m ys ht) in htnth.
      apply (NthElement_decode v i m xs hv).
      subst xs. rewrite nth_error_app1 by exact hi. exact htnth.
    + intros i m hi hunth.
      apply (NthElement_decode u i m zs hu) in hunth.
      apply (NthElement_decode v (length ys + i) m xs hv).
      subst xs. rewrite nth_error_app2 by lia.
      replace (length ys + i - length ys) with i by lia. exact hunth.
Qed.

Lemma concatTermAt_nat : forall e v t u,
  Formula.Sat natModel e (concatTermAt v t u) <->
  ConcatenationCode (Term.eval natModel e v)
    (Term.eval natModel e t) (Term.eval natModel e u).
Proof.
  intros. rewrite concatTermAt_position. apply ConcatPosition_iff.
Qed.

(** Pairwise inequality of indexed elements. *)
Definition NoDupPosition (v : nat) : Prop :=
  exists n,
    HasLength v n /\
    forall i j m,
      i < n -> j < n -> i < j ->
      NthElement v i m -> ~ NthElement v j m.

Definition noDuplicatesTermAt (v : term) : formula :=
  pEx
    (pAnd
      (hasLengthTermAt (liftTerm 1 v) (tVar 0))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 1))
          (pAll
            (pImp (Formula.ltTermAt (tVar 0) (tVar 2))
              (pImp (Formula.ltTermAt (tVar 1) (tVar 0))
                (pAll
                  (pImp
                    (nthElementTermAt (liftTerm 4 v)
                      (tVar 2) (tVar 0))
                    (pNot
                      (nthElementTermAt (liftTerm 4 v)
                        (tVar 1) (tVar 0))))))))))).

Lemma noDuplicatesTermAt_position : forall e v,
  Formula.Sat natModel e (noDuplicatesTermAt v) <->
  NoDupPosition (Term.eval natModel e v).
Proof.
  intros e v. unfold noDuplicatesTermAt, NoDupPosition, pNot.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons.
  setoid_rewrite eval_liftTerm_scons4.
  split.
  - intros [n [hlen h]]. exists n. split; [exact hlen |].
    intros i j m hi hj hij hni hnj.
    exact (h i hi j hj hij m hni hnj).
  - intros [n [hlen h]]. exists n. split; [exact hlen |].
    intros i hi j hj hij m hni hnj.
    exact (h i j m hi hj hij hni hnj).
Qed.

Lemma NoDupPosition_iff : forall v,
  NoDupPosition v <-> NoDuplicatesCode v.
Proof.
  intro v. split.
  - intros [n [[xs [hdecode hlen]] hpos]].
    exists xs. split; [exact hdecode |].
    apply (proj2 (NoDup_nth_error xs)).
    intros i j hi heq.
    assert (hji : j < length xs).
    {
      apply nth_error_Some.
      rewrite <- heq. apply nth_error_Some. exact hi.
    }
    destruct (Nat.lt_trichotomy i j) as [hij | [hij | hij]]; [|exact hij|].
    + destruct (nth_error_exists_of_lt xs i hi) as [m hm].
      assert (hni : NthElement v i m).
      { apply (NthElement_decode v i m xs hdecode). exact hm. }
      assert (hnj : NthElement v j m).
      { apply (NthElement_decode v j m xs hdecode). now rewrite <- heq. }
      exfalso. exact (hpos i j m ltac:(lia) ltac:(lia) hij hni hnj).
    + destruct (nth_error_exists_of_lt xs j hji) as [m hm].
      assert (hnj : NthElement v j m).
      { apply (NthElement_decode v j m xs hdecode). exact hm. }
      assert (hni : NthElement v i m).
      { apply (NthElement_decode v i m xs hdecode). now rewrite heq. }
      exfalso. exact (hpos j i m ltac:(lia) ltac:(lia) hij hnj hni).
  - intros [xs [hdecode hnodup]].
    exists (length xs). split.
    + exists xs. now split.
    + intros i j m hi hj hij hni hnj.
      apply (NthElement_decode v i m xs hdecode) in hni.
      apply (NthElement_decode v j m xs hdecode) in hnj.
      pose proof (proj1 (NoDup_nth_error xs) hnodup i j hi) as heqidx.
      assert (i = j) by (apply heqidx; now rewrite hni, hnj).
      lia.
Qed.

Lemma noDuplicatesTermAt_nat : forall e v,
  Formula.Sat natModel e (noDuplicatesTermAt v) <->
  NoDuplicatesCode (Term.eval natModel e v).
Proof.
  intros. rewrite noDuplicatesTermAt_position. apply NoDupPosition_iff.
Qed.

(** Adjacent comparisons characterize nondecreasing finite lists. *)
Definition SortedPosition (v : nat) : Prop :=
  exists n,
    HasLength v n /\
    forall i a b,
      S i < n ->
      NthElement v i a -> NthElement v (S i) b -> a <= b.

Definition sortedTermAt (v : term) : formula :=
  pEx
    (pAnd
      (hasLengthTermAt (liftTerm 1 v) (tVar 0))
      (pAll
        (pImp (Formula.ltTermAt (tSucc (tVar 0)) (tVar 1))
          (pAll (pAll
            (pImp
              (nthElementTermAt (liftTerm 4 v) (tVar 2) (tVar 1))
              (pImp
                (nthElementTermAt (liftTerm 4 v)
                  (tSucc (tVar 2)) (tVar 0))
                (Formula.ltTermAt (tVar 1) (tSucc (tVar 0)))))))))).

Lemma sortedTermAt_position : forall e v,
  Formula.Sat natModel e (sortedTermAt v) <->
  SortedPosition (Term.eval natModel e v).
Proof.
  intros e v. unfold sortedTermAt, SortedPosition.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons.
  setoid_rewrite eval_liftTerm_scons4.
  split.
  - intros [n [hlen h]]. exists n. split; [exact hlen |].
    intros i a b hi hia hib. pose proof (h i hi a b hia hib). lia.
  - intros [n [hlen h]]. exists n. split; [exact hlen |].
    intros i hi a b hia hib. pose proof (h i a b hi hia hib). lia.
Qed.

Lemma locallySorted_nth_error : forall xs,
  LocallySorted le xs <->
  forall i a b,
    nth_error xs i = Some a ->
    nth_error xs (S i) = Some b -> a <= b.
Proof.
  induction xs as [|x xs IH].
  - split.
    + intros _ i a b h. destruct i; discriminate.
    + intros _. constructor.
  - destruct xs as [|y ys].
    + split.
      * intros _ i a b h1 h2. destruct i; discriminate.
      * intros _. constructor.
    + split.
      * intros h i a b h1 h2.
        inversion h as [| |a0 b0 l htail hxy]; subst.
        destruct i as [|i].
        -- simpl in h1, h2. inversion h1; inversion h2; subst. exact hxy.
        -- simpl in h1, h2.
           apply (proj1 IH htail i a b h1 h2).
      * intro h. constructor.
        -- apply (proj2 IH). intros i a b h1 h2.
           apply (h (S i) a b); simpl; assumption.
        -- specialize (h 0 x y eq_refl eq_refl). exact h.
Qed.

Lemma SortedPosition_iff : forall v,
  SortedPosition v <-> SortedCode v.
Proof.
  intro v. split.
  - intros [n [[xs [hdecode hlen]] hpos]].
    exists xs. split; [exact hdecode |].
    unfold Nondecreasing. apply (proj2 (Sorted_LocallySorted_iff le xs)).
    apply (proj2 (locallySorted_nth_error xs)).
    intros i a b hia hib.
    assert (hi : S i < length xs).
    { apply nth_error_Some. rewrite hib. discriminate. }
    apply (hpos i a b ltac:(lia)).
    + apply (NthElement_decode v i a xs hdecode). exact hia.
    + apply (NthElement_decode v (S i) b xs hdecode). exact hib.
  - intros [xs [hdecode hsorted]].
    exists (length xs). split.
    + exists xs. now split.
    + intros i a b hi hia hib.
      apply (NthElement_decode v i a xs hdecode) in hia.
      apply (NthElement_decode v (S i) b xs hdecode) in hib.
      pose proof (proj1 (Sorted_LocallySorted_iff le xs) hsorted) as hlocal.
      exact (proj1 (locallySorted_nth_error xs) hlocal i a b hia hib).
Qed.

Lemma sortedTermAt_nat : forall e v,
  Formula.Sat natModel e (sortedTermAt v) <->
  SortedCode (Term.eval natModel e v).
Proof.
  intros. rewrite sortedTermAt_position. apply SortedPosition_iff.
Qed.

(** A substring is obtained by appending a prefix and a suffix. *)
Definition SubstringViaConcat (v w : nat) : Prop :=
  exists prefix suffix middle,
    ConcatenationCode middle prefix v /\
    ConcatenationCode w middle suffix.

Definition contiguousSubstringTermAt (v w : term) : formula :=
  pEx3
    (pAnd
      (concatTermAt (tVar 0) (tVar 2) (liftTerm 3 v))
      (concatTermAt (liftTerm 3 w) (tVar 0) (tVar 1))).

Lemma contiguousSubstringTermAt_via_concat : forall e v w,
  Formula.Sat natModel e (contiguousSubstringTermAt v w) <->
  SubstringViaConcat (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros e v w. unfold contiguousSubstringTermAt, SubstringViaConcat, pEx3.
  cbn [Formula.Sat]. setoid_rewrite concatTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons3. reflexivity.
Qed.

Lemma SubstringViaConcat_iff : forall v w,
  SubstringViaConcat v w <-> ContiguousSubstringCode v w.
Proof.
  intros v w. split.
  - intros [prefix [suffix [middle [hfirst hsecond]]]].
    destruct hfirst as
      [mid1 [pre [needle [hmid1 [hpre [hv hfirst]]]]]].
    destruct hsecond as
      [hay [mid2 [suf [hw [hmid2 [hsuf hsecond]]]]]].
    pose proof (decode_functional middle mid1 mid2 hmid1 hmid2) as hmid.
    subst mid2. exists needle, hay. repeat split; try assumption.
    exists pre, suf. subst mid1. rewrite app_assoc. exact hsecond.
  - intros [needle [hay [hv [hw [pre [suf heq]]]]]].
    exists (listCode pre), (listCode suf), (listCode (pre ++ needle)).
    split.
    + exists (pre ++ needle), pre, needle. repeat split.
      * apply decode_listCode.
      * apply decode_listCode.
      * exact hv.
    + exists hay, (pre ++ needle), suf. repeat split.
      * exact hw.
      * apply decode_listCode.
      * apply decode_listCode.
      * rewrite <- app_assoc. exact heq.
Qed.

Lemma contiguousSubstringTermAt_nat : forall e v w,
  Formula.Sat natModel e (contiguousSubstringTermAt v w) <->
  ContiguousSubstringCode (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros. rewrite contiguousSubstringTermAt_via_concat.
  apply SubstringViaConcat_iff.
Qed.

(** Prefix counts provide a first-order certificate for exact occurrence
    counts. *)
Definition OccurrencePosition (v n m : nat) : Prop :=
  exists len counts,
    HasLength v len /\
    HasLength counts (S len) /\
    NthElement counts 0 0 /\
    NthElement counts len n /\
    forall i x cur next,
      i < len ->
      NthElement v i x ->
      NthElement counts i cur ->
      NthElement counts (S i) next ->
      (x = m /\ next = S cur) \/ (x <> m /\ next = cur).

Definition occurrencesTermAt (v n m : term) : formula :=
  pEx (pEx
    (pAnd5
      (hasLengthTermAt (liftTerm 2 v) (tVar 1))
      (hasLengthTermAt (tVar 0) (tSucc (tVar 1)))
      (nthElementTermAt (tVar 0) tZero tZero)
      (nthElementTermAt (tVar 0) (tVar 1) (liftTerm 2 n))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 2))
          (pAll (pAll (pAll
            (pImp
              (nthElementTermAt (liftTerm 6 v) (tVar 3) (tVar 2))
              (pImp
                (nthElementTermAt (tVar 4) (tVar 3) (tVar 1))
                (pImp
                  (nthElementTermAt (tVar 4)
                    (tSucc (tVar 3)) (tVar 0))
                  (pOr
                    (pAnd
                      (pEq (tVar 2) (liftTerm 6 m))
                      (pEq (tVar 0) (tSucc (tVar 1))))
                    (pAnd
                      (pNot (pEq (tVar 2) (liftTerm 6 m)))
                      (pEq (tVar 0) (tVar 1)))))))))))))).

Lemma occurrencesTermAt_position : forall e v n m,
  Formula.Sat natModel e (occurrencesTermAt v n m) <->
  OccurrencePosition (Term.eval natModel e v)
    (Term.eval natModel e n) (Term.eval natModel e m).
Proof.
  intros e v n m. unfold occurrencesTermAt, OccurrencePosition, pAnd5, pNot.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons2.
  setoid_rewrite eval_liftTerm_scons6.
  split.
  - intros [len [counts [hv [hc [hzero [hend hstep]]]]]].
    exists len, counts. repeat split; try assumption.
    intros i x cur next hi hvi hci hcn.
    specialize (hstep i hi x cur next hvi hci hcn).
    destruct hstep as [[heq hnext] | [hne hnext]].
    + now left.
    + right. split; [intro heq; apply hne; now subst | exact hnext].
  - intros [len [counts [hv [hc [hzero [hend hstep]]]]]].
    exists len, counts. repeat split; try assumption.
    intros i hi x cur next hvi hci hcn.
    destruct (hstep i x cur next hi hvi hci hcn) as
      [[heq hnext] | [hne hnext]].
    + now left.
    + right. split; [intro heq; apply hne; exact heq | exact hnext].
Qed.

Definition prefixCounts (xs : list nat) (m : nat) : list nat :=
  map (fun i => count_occ Nat.eq_dec (firstn i xs) m)
    (seq 0 (S (length xs))).

Lemma prefixCounts_length : forall xs m,
  length (prefixCounts xs m) = S (length xs).
Proof. intros. unfold prefixCounts. rewrite map_length, seq_length. reflexivity. Qed.

Lemma prefixCounts_nth : forall xs m i,
  i <= length xs ->
  nth_error (prefixCounts xs m) i =
    Some (count_occ Nat.eq_dec (firstn i xs) m).
Proof.
  intros xs m i hi. unfold prefixCounts.
  rewrite nth_error_map, nth_error_seq.
  destruct (i <? S (length xs)) eqn:h.
  - simpl. now replace (0 + i) with i by lia.
  - apply Nat.ltb_ge in h. lia.
Qed.

Lemma count_occ_firstn_step : forall xs m i x,
  i < length xs -> nth_error xs i = Some x ->
  count_occ Nat.eq_dec (firstn (S i) xs) m =
    if Nat.eq_dec x m
    then S (count_occ Nat.eq_dec (firstn i xs) m)
    else count_occ Nat.eq_dec (firstn i xs) m.
Proof.
  induction xs as [|y ys IH]; intros m i x hi hnth; [simpl in hi; lia |].
  destruct i as [|i].
  - simpl in hnth. inversion hnth; subst x. simpl.
    destruct (Nat.eq_dec y m); reflexivity.
  - simpl in hnth. simpl firstn. simpl count_occ.
    specialize (IH m i x ltac:(simpl in hi; lia) hnth).
    destruct (Nat.eq_dec y m); destruct (Nat.eq_dec x m);
      simpl in *; lia.
Qed.

Lemma OccurrencePosition_iff : forall v n m,
  OccurrencePosition v n m <-> OccurrencesCode v n m.
Proof.
  intros v n m. split.
  - intros [len [counts
      [[xs [hv hlen]] [[cs [hc hclen]] [hzero [hend hstep]]]]]].
    exists xs. split; [exact hv |].
    assert (hinv : forall i, i <= length xs ->
      nth_error cs i =
        Some (count_occ Nat.eq_dec (firstn i xs) m)).
    {
      intros i hi. induction i as [|i IHi].
      - apply (NthElement_decode counts 0 0 cs hc) in hzero.
        simpl. exact hzero.
      - assert (hil : i < length xs) by lia.
        specialize (IHi ltac:(lia)).
        destruct (nth_error_exists_of_lt xs i hil) as [x hx].
        assert (hcsnext : S i < length cs) by lia.
        destruct (nth_error_exists_of_lt cs (S i) hcsnext) as [next hn].
        assert (hvi : NthElement v i x).
        { apply (NthElement_decode v i x xs hv). exact hx. }
        assert (hci : NthElement counts i
          (count_occ Nat.eq_dec (firstn i xs) m)).
        { apply (NthElement_decode counts i _ cs hc). exact IHi. }
        assert (hcn : NthElement counts (S i) next).
        { apply (NthElement_decode counts (S i) next cs hc). exact hn. }
        destruct (hstep i x _ next ltac:(lia) hvi hci hcn) as
          [[hxm hnext] | [hxm hnext]].
        + subst x next. rewrite (count_occ_firstn_step xs m i m hil hx).
          destruct (Nat.eq_dec m m); [exact hn | contradiction].
        + subst next. rewrite (count_occ_firstn_step xs m i x hil hx).
          destruct (Nat.eq_dec x m); [contradiction | exact hn].
    }
    apply (NthElement_decode counts len n cs hc) in hend.
    specialize (hinv (length xs) ltac:(lia)).
    rewrite firstn_all in hinv. rewrite hlen in hinv.
    rewrite hend in hinv. inversion hinv. reflexivity.
  - intros [xs [hv hcount]].
    set (cs := prefixCounts xs m).
    set (counts := listCode cs).
    exists (length xs), counts. repeat split.
    + exists xs. now split.
    + exists cs. split.
      * unfold counts. apply decode_listCode.
      * unfold cs. apply prefixCounts_length.
    + exists cs. split.
      * unfold counts. apply decode_listCode.
      * unfold cs. apply prefixCounts_nth. lia.
    + exists cs. split.
      * unfold counts. apply decode_listCode.
      * unfold cs. rewrite prefixCounts_nth by lia.
        rewrite firstn_all, hcount. reflexivity.
    + intros i x cur next hi hvi hci hcn.
      apply (NthElement_decode v i x xs hv) in hvi.
      apply (NthElement_decode counts i cur cs
        ltac:(unfold counts; apply decode_listCode)) in hci.
      apply (NthElement_decode counts (S i) next cs
        ltac:(unfold counts; apply decode_listCode)) in hcn.
      unfold cs in hci, hcn.
      rewrite prefixCounts_nth in hci by lia.
      rewrite prefixCounts_nth in hcn by lia.
      assert (hcur : cur = count_occ Nat.eq_dec (firstn i xs) m).
      { inversion hci. reflexivity. }
      assert (hnext : next = count_occ Nat.eq_dec (firstn (S i) xs) m).
      { inversion hcn. reflexivity. }
      pose proof (count_occ_firstn_step xs m i x hi hvi) as hstep.
      destruct (Nat.eq_dec x m) as [heq | hne].
      * left. split; [exact heq |]. subst x.
        destruct (Nat.eq_dec m m) in hstep; [|contradiction].
        rewrite hcur, hnext. exact hstep.
      * right. split; [exact hne |].
        destruct (Nat.eq_dec x m) in hstep; [contradiction |].
        rewrite hcur, hnext. exact hstep.
Qed.

Lemma occurrencesTermAt_nat : forall e v n m,
  Formula.Sat natModel e (occurrencesTermAt v n m) <->
  OccurrencesCode (Term.eval natModel e v)
    (Term.eval natModel e n) (Term.eval natModel e m).
Proof.
  intros. rewrite occurrencesTermAt_position. apply OccurrencePosition_iff.
Qed.

(** Equality of all multiplicities characterizes permutations. *)
Definition PermutationByCounts (v w : nat) : Prop :=
  ValidCode v /\ ValidCode w /\
  forall m n, OccurrencesCode v n m <-> OccurrencesCode w n m.

Definition permutationTermAt (v w : term) : formula :=
  pAnd3
    (validCodeTermAt v)
    (validCodeTermAt w)
    (pAll (pAll
      (pIff
        (occurrencesTermAt (liftTerm 2 v) (tVar 0) (tVar 1))
        (occurrencesTermAt (liftTerm 2 w) (tVar 0) (tVar 1))))).

Lemma permutationTermAt_counts : forall e v w,
  Formula.Sat natModel e (permutationTermAt v w) <->
  PermutationByCounts (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros e v w. unfold permutationTermAt, PermutationByCounts, pAnd3, pIff.
  cbn [Formula.Sat].
  setoid_rewrite validCodeTermAt_nat.
  setoid_rewrite occurrencesTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons2.
  split.
  - intros [hv [hw h]]. split; [exact hv |]. split; [exact hw |].
    intros mm nn. specialize (h mm nn). tauto.
  - intros [hv [hw h]]. split; [exact hv |]. split; [exact hw |].
    intros mm nn. specialize (h mm nn). tauto.
Qed.

Lemma PermutationByCounts_iff : forall v w,
  PermutationByCounts v w <-> PermutationCode v w.
Proof.
  intros v w. split.
  - intros [[xs hv] [[ys hw] hcounts]].
    exists xs, ys. repeat split; try assumption.
    apply (proj2 (Permutation_count_occ Nat.eq_dec xs ys)). intro m.
    set (n := count_occ Nat.eq_dec xs m).
    assert (hocv : OccurrencesCode v n m).
    { exists xs. split; [exact hv | reflexivity]. }
    apply (proj1 (hcounts m n)) in hocv.
    destruct hocv as [ys' [hwy hcount]].
    pose proof (decode_functional w ys' ys hwy hw). subst ys'.
    exact (eq_sym hcount).
  - intros [xs [ys [hv [hw hperm]]]].
    split; [now exists xs |]. split; [now exists ys |].
    intros m n. split.
    + intros [xs' [hv' hcount]].
      pose proof (decode_functional v xs' xs hv' hv). subst xs'.
      exists ys. split; [exact hw |].
      rewrite <- hcount. symmetry.
      exact (proj1 (Permutation_count_occ Nat.eq_dec xs ys) hperm m).
    + intros [ys' [hw' hcount]].
      pose proof (decode_functional w ys' ys hw' hw). subst ys'.
      exists xs. split; [exact hv |].
      rewrite <- hcount.
      exact (proj1 (Permutation_count_occ Nat.eq_dec xs ys) hperm m).
Qed.

Lemma permutationTermAt_nat : forall e v w,
  Formula.Sat natModel e (permutationTermAt v w) <->
  PermutationCode (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros. rewrite permutationTermAt_counts. apply PermutationByCounts_iff.
Qed.

(** Prefix concatenations certify flattening of a coded list of coded
    lists. *)
Definition FlattenPosition (v w : nat) : Prop :=
  exists len prefixes,
    HasLength w len /\
    HasLength prefixes (S len) /\
    NthElement prefixes 0 0 /\
    NthElement prefixes len v /\
    forall i inner prev next,
      i < len ->
      NthElement w i inner ->
      NthElement prefixes i prev ->
      NthElement prefixes (S i) next ->
      ConcatenationCode next prev inner.

Definition flattenTermAt (v w : term) : formula :=
  pEx (pEx
    (pAnd5
      (hasLengthTermAt (liftTerm 2 w) (tVar 1))
      (hasLengthTermAt (tVar 0) (tSucc (tVar 1)))
      (nthElementTermAt (tVar 0) tZero tZero)
      (nthElementTermAt (tVar 0) (tVar 1) (liftTerm 2 v))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 2))
          (pAll (pAll (pAll
            (pImp
              (nthElementTermAt (liftTerm 6 w) (tVar 3) (tVar 2))
              (pImp
                (nthElementTermAt (tVar 4) (tVar 3) (tVar 1))
                (pImp
                  (nthElementTermAt (tVar 4)
                    (tSucc (tVar 3)) (tVar 0))
                  (concatTermAt (tVar 0) (tVar 1) (tVar 2)))))))))))).

Lemma flattenTermAt_position : forall e v w,
  Formula.Sat natModel e (flattenTermAt v w) <->
  FlattenPosition (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros e v w. unfold flattenTermAt, FlattenPosition, pAnd5.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite concatTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons2.
  setoid_rewrite eval_liftTerm_scons6.
  split.
  - intros [len [prefixes [hw [hp [hz [he hs]]]]]].
    exists len, prefixes. repeat split; try assumption.
    intros i inner prev next hi hwi hpi hpn.
    exact (hs i hi inner prev next hwi hpi hpn).
  - intros [len [prefixes [hw [hp [hz [he hs]]]]]].
    exists len, prefixes. repeat split; try assumption.
    intros i hi inner prev next hwi hpi hpn.
    exact (hs i inner prev next hi hwi hpi hpn).
Qed.

Lemma decodeCodes_exists_of_valid : forall codes,
  Forall ValidCode codes -> exists xss, decodeCodes codes = Some xss.
Proof.
  intros codes h. induction h as [|c codes hc hcodes IH].
  - exists []. reflexivity.
  - destruct hc as [xs hdecode]. destruct IH as [xss hxss].
    exists (xs :: xss). simpl. now rewrite hdecode, hxss.
Qed.

Lemma decodeCodes_nth : forall codes xss i xs,
  decodeCodes codes = Some xss ->
  nth_error xss i = Some xs ->
  exists c, nth_error codes i = Some c /\ decode c = Some xs.
Proof.
  induction codes as [|c codes IH]; intros xss i xs hdecode hnth.
  - simpl in hdecode. inversion hdecode; subst xss. destruct i; discriminate.
  - simpl in hdecode.
    destruct (decode c) as [ys|] eqn:hc; try discriminate.
    destruct (decodeCodes codes) as [yss|] eqn:hcs; try discriminate.
    inversion hdecode; subst xss. destruct i as [|i].
    + simpl in hnth. inversion hnth; subst xs. exists c. now split.
    + simpl in hnth. destruct (IH yss i xs eq_refl hnth) as [d [hd hdx]].
      exists d. split; [exact hd | exact hdx].
Qed.

Lemma decodeCodes_length : forall codes xss,
  decodeCodes codes = Some xss -> length codes = length xss.
Proof.
  intros codes xss h. pose proof (decodeCodes_sound codes xss h) as hm.
  rewrite <- hm, map_length. reflexivity.
Qed.

Lemma concat_firstn_step : forall (xss : list (list nat)) i (xs : list nat),
  i < length xss -> nth_error xss i = Some xs ->
  concat (firstn (S i) xss) = concat (firstn i xss) ++ xs.
Proof.
  induction xss as [|ys yss IH]; intros i xs hi hnth;
    [simpl in hi; lia |].
  destruct i as [|i].
  - simpl in hnth. inversion hnth; subst xs. simpl. now rewrite app_nil_r.
  - simpl in hnth. rewrite !firstn_cons. rewrite !concat_cons.
    rewrite (IH i xs ltac:(simpl in hi; lia) hnth).
    apply app_assoc.
Qed.

Definition prefixFlats (xss : list (list nat)) : list nat :=
  map (fun i => listCode (concat (firstn i xss)))
    (seq 0 (S (length xss))).

Lemma prefixFlats_length : forall xss,
  length (prefixFlats xss) = S (length xss).
Proof. intro. unfold prefixFlats. rewrite map_length, seq_length. reflexivity. Qed.

Lemma prefixFlats_nth : forall xss i,
  i <= length xss ->
  nth_error (prefixFlats xss) i =
    Some (listCode (concat (firstn i xss))).
Proof.
  intros xss i hi. unfold prefixFlats.
  rewrite nth_error_map, nth_error_seq.
  destruct (i <? S (length xss)) eqn:h.
  - simpl. now replace (0 + i) with i by lia.
  - apply Nat.ltb_ge in h. lia.
Qed.

Lemma FlattenPosition_iff : forall v w,
  FlattenPosition v w <-> FlattenCode v w.
Proof.
  intros v w. split.
  - intros [len [prefixes
      [[codes [hw hlen]] [[ps [hp hplen]] [hzero [hend hstep]]]]]].
    assert (hvalid : Forall ValidCode codes).
    {
      apply Forall_forall. intros c hcIn.
      apply In_nth_error in hcIn. destruct hcIn as [i hci].
      assert (hi : i < len).
      { rewrite <- hlen. apply nth_error_Some. rewrite hci. discriminate. }
      destruct (nth_error_exists_of_lt ps i ltac:(lia)) as [prev hprev].
      destruct (nth_error_exists_of_lt ps (S i) ltac:(lia)) as [next hnext].
      assert (hwc : NthElement w i c).
      { apply (NthElement_decode w i c codes hw). exact hci. }
      assert (hpp : NthElement prefixes i prev).
      { apply (NthElement_decode prefixes i prev ps hp). exact hprev. }
      assert (hpn : NthElement prefixes (S i) next).
      { apply (NthElement_decode prefixes (S i) next ps hp). exact hnext. }
      pose proof (hstep i c prev next hi hwc hpp hpn) as hcat.
      exact (proj2 (proj2 (ConcatenationCode_valid _ _ _ hcat))).
    }
    destruct (decodeCodes_exists_of_valid codes hvalid) as [xss hxss].
    assert (hlens : length codes = length xss).
    { exact (decodeCodes_length codes xss hxss). }
    assert (hinv : forall i, i <= length xss ->
      NthElement prefixes i (listCode (concat (firstn i xss)))).
    {
      intros i hi. induction i as [|i IHi].
      - change (NthElement prefixes 0 0). exact hzero.
      - assert (hil : i < length xss) by lia.
        specialize (IHi ltac:(lia)).
        destruct (nth_error_exists_of_lt xss i hil) as [ys hys].
        destruct (decodeCodes_nth codes xss i ys hxss hys) as
          [c [hci hcdecode]].
        destruct (nth_error_exists_of_lt ps (S i) ltac:(lia)) as
          [next hnext].
        assert (hwc : NthElement w i c).
        { apply (NthElement_decode w i c codes hw). exact hci. }
        assert (hpn : NthElement prefixes (S i) next).
        { apply (NthElement_decode prefixes (S i) next ps hp). exact hnext. }
        pose proof (hstep i c (listCode (concat (firstn i xss))) next
          ltac:(lia) hwc IHi hpn) as hcat.
        destruct hcat as
          [out [pre [inner [hnextDecode [hpre [hinner hout]]]]]].
        pose proof (decode_functional _ pre (concat (firstn i xss))
          hpre (decode_listCode _)) as hpreEq. subst pre.
        pose proof (decode_functional _ inner ys hinner hcdecode) as hinnerEq.
        subst inner.
        assert (hnextCode : next =
          listCode (concat (firstn (S i) xss))).
        {
          apply eq_sym. apply listCode_decode in hnextDecode.
          rewrite <- hnextDecode, hout.
          f_equal. exact (concat_firstn_step xss i ys hil hys).
        }
        rewrite <- hnextCode.
        exact hpn.
    }
    specialize (hinv (length xss) ltac:(lia)).
    assert (hend' : NthElement prefixes (length xss) v).
    { rewrite <- hlens, hlen. exact hend. }
    apply (NthElement_decode prefixes _ _ ps hp) in hinv.
    apply (NthElement_decode prefixes _ _ ps hp) in hend'.
    rewrite hinv in hend'. inversion hend' as [hvcode].
    exists (concat xss), codes, xss. repeat split; try assumption.
    + rewrite firstn_all. apply decode_listCode.
  - intros [flat [codes [xss [hv [hw [hxss hflat]]]]]].
    set (ps := prefixFlats xss).
    set (prefixes := listCode ps).
    assert (hlens : length codes = length xss).
    { exact (decodeCodes_length codes xss hxss). }
    exists (length codes), prefixes. repeat split.
    + exists codes. now split.
    + exists ps. split.
      * unfold prefixes. apply decode_listCode.
      * unfold ps. rewrite prefixFlats_length. lia.
    + exists ps. split.
      * unfold prefixes. apply decode_listCode.
      * unfold ps. rewrite prefixFlats_nth by lia. reflexivity.
    + exists ps. split.
      * unfold prefixes. apply decode_listCode.
      * unfold ps. rewrite prefixFlats_nth by lia.
        rewrite hlens, firstn_all, <- hflat.
        apply listCode_decode in hv. now rewrite hv.
    + intros i inner prev next hi hwi hpi hpn.
      apply (NthElement_decode w i inner codes hw) in hwi.
      apply (NthElement_decode prefixes i prev ps
        ltac:(unfold prefixes; apply decode_listCode)) in hpi.
      apply (NthElement_decode prefixes (S i) next ps
        ltac:(unfold prefixes; apply decode_listCode)) in hpn.
      assert (hix : i < length xss) by lia.
      destruct (nth_error_exists_of_lt xss i hix) as [ys hys].
      destruct (decodeCodes_nth codes xss i ys hxss hys) as
        [c [hci hcdecode]].
      rewrite hci in hwi. inversion hwi; subst c.
      unfold ps in hpi, hpn.
      rewrite prefixFlats_nth in hpi by lia.
      rewrite prefixFlats_nth in hpn by lia.
      inversion hpi as [hprev]. inversion hpn as [hnext].
      subst prev next.
      exists (concat (firstn (S i) xss)),
        (concat (firstn i xss)), ys. repeat split.
      * apply decode_listCode.
      * apply decode_listCode.
      * exact hcdecode.
      * exact (concat_firstn_step xss i ys hix hys).
Qed.

Lemma flattenTermAt_nat : forall e v w,
  Formula.Sat natModel e (flattenTermAt v w) <->
  FlattenCode (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros. rewrite flattenTermAt_position. apply FlattenPosition_iff.
Qed.

(** A subsequence certificate alternates arbitrary gap lists with singleton
    lists containing the selected elements.  Flattening the certificate
    reconstructs the ambient list. *)
Definition SubsequenceByChunks (v w : nat) : Prop :=
  exists len chunks,
    HasLength v len /\
    HasLength chunks (2 * len + 1) /\
    FlattenCode w chunks /\
    forall i m c,
      i < len ->
      NthElement v i m ->
      NthElement chunks (2 * i + 1) c ->
      SingletonCode c m.

Definition subsequenceTermAt (v w : term) : formula :=
  pEx (pEx
    (pAnd4
      (hasLengthTermAt (liftTerm 2 v) (tVar 1))
      (hasLengthTermAt (tVar 0)
        (tSucc (tAdd (tVar 1) (tVar 1))))
      (flattenTermAt (liftTerm 2 w) (tVar 0))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 2))
          (pAll (pAll
            (pImp
              (nthElementTermAt (liftTerm 5 v) (tVar 2) (tVar 1))
              (pImp
                (nthElementTermAt (tVar 3)
                  (tSucc (tAdd (tVar 2) (tVar 2))) (tVar 0))
                (singletonTermAt (tVar 0) (tVar 1)))))))))).

Lemma subsequenceTermAt_chunks : forall e v w,
  Formula.Sat natModel e (subsequenceTermAt v w) <->
  SubsequenceByChunks (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros e v w. unfold subsequenceTermAt, SubsequenceByChunks, pAnd4.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite flattenTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite singletonTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons2.
  setoid_rewrite eval_liftTerm_scons5.
  split.
  - intros [len [chunks [hv [hc [hf h]]]]].
    exists len, chunks. split; [exact hv |]. split.
    + replace (len + (len + 0) + 1) with (S (len + len)) by lia. exact hc.
    + split; [exact hf |].
    intros i m c hi hvi hci.
    replace (i + (i + 0) + 1) with (S (i + i)) in hci by lia.
    exact (h i hi m c hvi hci).
  - intros [len [chunks [hv [hc [hf h]]]]].
    exists len, chunks. split; [exact hv |]. split.
    + replace (S (len + len)) with (len + (len + 0) + 1) by lia. exact hc.
    + split; [exact hf |].
    intros i hi m c hvi hci.
    apply (h i m c hi hvi).
    replace (i + (i + 0) + 1) with (S (i + i)) by lia. exact hci.
Qed.

Fixpoint weaveChunks (gaps : list (list nat)) (xs : list nat)
    : list (list nat) :=
  match gaps, xs with
  | gap :: gaps', x :: xs' => gap :: [x] :: weaveChunks gaps' xs'
  | gap :: _, [] => [gap]
  | _, _ => []
  end.

Lemma weaveChunks_length : forall gaps xs,
  length gaps = S (length xs) ->
  length (weaveChunks gaps xs) = 2 * length xs + 1.
Proof.
  intros gaps xs. revert gaps. induction xs as [|x xs IH]; intros gaps hlen.
  - destruct gaps as [|g gaps]; simpl in hlen; try lia.
    destruct gaps; simpl in hlen; try lia. reflexivity.
  - destruct gaps as [|g gaps]; simpl in hlen; try lia.
    simpl. rewrite (IH gaps ltac:(simpl in hlen; lia)). lia.
Qed.

Lemma weaveChunks_odd : forall gaps xs i x,
  length gaps = S (length xs) ->
  nth_error xs i = Some x ->
  nth_error (weaveChunks gaps xs) (2 * i + 1) = Some [x].
Proof.
  intros gaps xs. revert gaps. induction xs as [|y ys IH]; intros gaps i x hlen hnth;
    [destruct i; discriminate |].
  destruct gaps as [|g gaps]; simpl in hlen; try lia.
  destruct i as [|i].
  - simpl in hnth. inversion hnth; subst x. reflexivity.
  - simpl in hnth. simpl weaveChunks.
    replace (2 * S i + 1) with (S (S (2 * i + 1))) by lia.
    simpl nth_error. apply (IH gaps i x ltac:(lia) hnth).
Qed.

Lemma Subsequence_weave_decomposition : forall xs ys,
  Subsequence xs ys ->
  exists gaps,
    length gaps = S (length xs) /\
    ys = concat (weaveChunks gaps xs).
Proof.
  intros xs ys h. induction h as
    [ys | x xs ys hsub IH | y xs ys hsub IH].
  - exists [ys]. split; [reflexivity |]. simpl. now rewrite app_nil_r.
  - destruct IH as [gaps [hlen heq]].
    exists ([] :: gaps). split.
    + simpl. lia.
    + simpl weaveChunks. simpl concat. now rewrite <- heq.
  - destruct IH as [gaps [hlen heq]].
    destruct gaps as [|gap gaps]; simpl in hlen; try lia.
    exists ((y :: gap) :: gaps). split.
    + simpl. exact hlen.
    + destruct xs as [|x xs].
      * assert (hg0 : length gaps = 0) by (simpl in hlen; lia).
        apply length_zero_iff_nil in hg0. subst gaps.
        simpl in *. now rewrite <- heq.
      * simpl in *. now rewrite <- heq.
Qed.

Lemma Subsequence_prefix : forall prefix xs ys,
  Subsequence xs ys -> Subsequence xs (prefix ++ ys).
Proof.
  induction prefix as [|x prefix IH]; intros xs ys h; simpl.
  - exact h.
  - apply subsequence_skip. apply IH. exact h.
Qed.

Lemma Subsequence_of_odd_chunks : forall xs xss,
  length xss = 2 * length xs + 1 ->
  (forall i x, nth_error xs i = Some x ->
    nth_error xss (2 * i + 1) = Some [x]) ->
  Subsequence xs (concat xss).
Proof.
  induction xs as [|x xs IH]; intros xss hlen hodd.
  - constructor.
  - destruct xss as [|gap xss]; simpl in hlen; try lia.
    destruct xss as [|one rest]; simpl in hlen; try lia.
    assert (hone : one = [x]).
    { specialize (hodd 0 x eq_refl). simpl in hodd. inversion hodd. reflexivity. }
    subst one.
    assert (hrestLen : length rest = 2 * length xs + 1) by (simpl in hlen; lia).
    assert (hrestOdd : forall i y, nth_error xs i = Some y ->
      nth_error rest (2 * i + 1) = Some [y]).
    {
      intros i y hy. specialize (hodd (S i) y hy).
      replace (2 * S i + 1) with (S (S (2 * i + 1))) in hodd by lia.
      simpl in hodd. exact hodd.
    }
    pose proof (IH rest hrestLen hrestOdd) as hsub.
    simpl concat. apply Subsequence_prefix.
    apply subsequence_keep. exact hsub.
Qed.

Lemma SubsequenceByChunks_iff : forall v w,
  SubsequenceByChunks v w <-> SubsequenceCode v w.
Proof.
  intros v w. split.
  - intros [len [chunks
      [[xs [hv hlen]] [[codes [hc hcodesLen]]
        [[ys [codes' [xss [hw [hc' [hxss hflat]]]]]] hodd]]]]].
    pose proof (decode_functional chunks codes codes' hc hc') as hcodes.
    subst codes'.
    exists xs, ys. repeat split; try assumption.
    rewrite hflat.
    apply Subsequence_of_odd_chunks with (xss := xss).
    + rewrite <- (decodeCodes_length codes xss hxss), hcodesLen, hlen. lia.
    + intros i x hxi.
      destruct (nth_error_exists_of_lt xss (2 * i + 1)) as [piece hpiece].
      * assert (hix : i < length xs).
        { apply nth_error_Some. rewrite hxi. discriminate. }
        rewrite <- (decodeCodes_length codes xss hxss), hcodesLen. lia.
      * destruct (decodeCodes_nth codes xss (2 * i + 1) piece hxss hpiece)
          as [c0 [hc0 hdc0]].
        assert (hvi : NthElement v i x).
        { apply (NthElement_decode v i x xs hv). exact hxi. }
        assert (hci0 : NthElement chunks (2 * i + 1) c0).
        { apply (NthElement_decode chunks _ c0 codes hc). exact hc0. }
        assert (hilt : i < len).
        {
          assert (i < length xs).
          { apply nth_error_Some. rewrite hxi. discriminate. }
          lia.
        }
        pose proof (hodd i x c0 hilt hvi hci0) as hs.
        pose proof (decode_functional c0 piece [x] hdc0 hs) as hp.
        subst piece. exact hpiece.
  - intros [xs [ys [hv [hw hsub]]]].
    destruct (Subsequence_weave_decomposition xs ys hsub) as
      [gaps [hgaps hweave]].
    set (xss := weaveChunks gaps xs).
    set (codes := map listCode xss).
    set (chunks := listCode codes).
    exists (length xs), chunks. repeat split.
    + exists xs. now split.
    + exists codes. split.
      * unfold chunks. apply decode_listCode.
      * unfold codes. rewrite map_length. unfold xss.
        apply weaveChunks_length. exact hgaps.
    + exists ys, codes, xss. repeat split.
      * exact hw.
      * unfold chunks. apply decode_listCode.
      * unfold codes. apply decodeCodes_map_listCode.
      * unfold xss. exact hweave.
    + intros i m c hi hvi hci.
      apply (NthElement_decode v i m xs hv) in hvi.
      apply (NthElement_decode chunks (2 * i + 1) c codes
        ltac:(unfold chunks; apply decode_listCode)) in hci.
      unfold codes in hci. rewrite nth_error_map in hci.
      unfold xss in hci.
      rewrite (weaveChunks_odd gaps xs i m hgaps hvi) in hci.
      simpl in hci. inversion hci; subst c.
      change (decode (listCode [m]) = Some [m]). apply decode_listCode.
Qed.

Lemma subsequenceTermAt_nat : forall e v w,
  Formula.Sat natModel e (subsequenceTermAt v w) <->
  SubsequenceCode (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros. rewrite subsequenceTermAt_chunks. apply SubsequenceByChunks_iff.
Qed.

(** Lexicographic comparison of two individually coded lists. *)
Definition LexPosition (a b : nat) : Prop :=
  exists na nb,
    HasLength a na /\ HasLength b nb /\
    ((na <= nb /\
      forall i m, i < na -> NthElement a i m -> NthElement b i m) \/
     exists k x y,
       k < na /\ k < nb /\
       NthElement a k x /\ NthElement b k y /\ x < y /\
       forall i m, i < k -> NthElement a i m -> NthElement b i m).

Definition lexLeTermAt (a b : term) : formula :=
  pEx (pEx
    (pAnd3
      (hasLengthTermAt (liftTerm 2 a) (tVar 1))
      (hasLengthTermAt (liftTerm 2 b) (tVar 0))
      (pOr
        (pAnd
          (Formula.ltTermAt (tVar 1) (tSucc (tVar 0)))
          (pAll
            (pImp (Formula.ltTermAt (tVar 0) (tVar 2))
              (pAll
                (pImp
                  (nthElementTermAt (liftTerm 4 a) (tVar 1) (tVar 0))
                  (nthElementTermAt (liftTerm 4 b)
                    (tVar 1) (tVar 0)))))))
        (pEx (pEx (pEx
          (pAnd6
            (Formula.ltTermAt (tVar 2) (tVar 4))
            (Formula.ltTermAt (tVar 2) (tVar 3))
            (nthElementTermAt (liftTerm 5 a) (tVar 2) (tVar 1))
            (nthElementTermAt (liftTerm 5 b) (tVar 2) (tVar 0))
            (Formula.ltTermAt (tVar 1) (tVar 0))
            (pAll
              (pImp (Formula.ltTermAt (tVar 0) (tVar 3))
                (pAll
                  (pImp
                    (nthElementTermAt (liftTerm 7 a)
                      (tVar 1) (tVar 0))
                    (nthElementTermAt (liftTerm 7 b)
                      (tVar 1) (tVar 0))))))))))))).

Lemma lexLeTermAt_position : forall e a b,
  Formula.Sat natModel e (lexLeTermAt a b) <->
  LexPosition (Term.eval natModel e a) (Term.eval natModel e b).
Proof.
  intros e a b. unfold lexLeTermAt, LexPosition, pAnd3, pAnd6.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons2.
  setoid_rewrite eval_liftTerm_scons4.
  setoid_rewrite eval_liftTerm_scons5.
  setoid_rewrite eval_liftTerm_scons7.
  split.
  - intros [na [nb [ha [hb h]]]]. exists na, nb. repeat split; try assumption.
    destruct h as [[hle hp] | [k [x [y [hka [hkb [hax [hby [hxy hp]]]]]]]]].
    + left. split; [lia |]. intros i m hi hai. exact (hp i hi m hai).
    + right. exists k, x, y. repeat split; try assumption.
      intros i m hi hai. exact (hp i hi m hai).
  - intros [na [nb [ha [hb h]]]]. exists na, nb. repeat split; try assumption.
    destruct h as [[hle hp] | [k [x [y [hka [hkb [hax [hby [hxy hp]]]]]]]]].
    + left. split; [lia |]. intros i hi m hai. exact (hp i m hi hai).
    + right. exists k, x, y. repeat split; try assumption.
      intros i hi m hai. exact (hp i m hi hai).
Qed.

Definition LexIndex (xs ys : list nat) : Prop :=
  (length xs <= length ys /\
    forall i x, i < length xs ->
      nth_error xs i = Some x -> nth_error ys i = Some x) \/
  exists k x y,
    k < length xs /\ k < length ys /\
    nth_error xs k = Some x /\ nth_error ys k = Some y /\ x < y /\
    forall i z, i < k ->
      nth_error xs i = Some z -> nth_error ys i = Some z.

Lemma LexIndex_iff_LexLe : forall xs ys,
  LexIndex xs ys <-> LexLe xs ys.
Proof.
  induction xs as [|x xs IH]; intros ys.
  - split.
    + intros hignore. constructor.
    + intros hignore. left. split.
      * simpl. lia.
      * intros i z hi. simpl in hi. lia.
  - destruct ys as [|y ys].
    + split.
      * intros [[hlen _] | [k [a [b [hkx [hky _]]]]]]; simpl in *; lia.
      * intro h. inversion h.
    + split.
      * intros [[hlen hp] | [k [a [b [hkx [hky [hxa [hyb [hab hp]]]]]]]]].
        -- assert (hxy : x = y).
           { specialize (hp 0 x ltac:(simpl; lia) eq_refl).
             simpl in hp. inversion hp. reflexivity. }
           subst y. apply lexLe_head_eq. apply (proj1 (IH ys)).
           left. split; [simpl in hlen; lia |].
           intros i z hi hz. specialize (hp (S i) z ltac:(simpl; lia) hz).
           simpl in hp. exact hp.
        -- destruct k as [|k].
           ++ simpl in hxa, hyb. inversion hxa; inversion hyb; subst a b.
              apply lexLe_head_lt. exact hab.
           ++ assert (hxy : x = y).
              { specialize (hp 0 x ltac:(lia) eq_refl).
                simpl in hp. inversion hp. reflexivity. }
              subst y. apply lexLe_head_eq. apply (proj1 (IH ys)).
              right. exists k, a, b. split; [simpl in hkx; lia |].
              split; [simpl in hky; lia |]. split.
              ** simpl in hxa. exact hxa.
              ** split.
                 --- simpl in hyb. exact hyb.
                 --- split; [exact hab |]. intros i z hi hz.
                     specialize (hp (S i) z ltac:(lia) hz).
                     simpl in hp. exact hp.
      * intro h. inversion h as [| |x0 xs0 ys0 htail]; subst.
        -- right. exists 0, x, y. simpl. repeat split; try lia; reflexivity.
        -- apply (proj2 (IH ys)) in htail.
           destruct htail as [[hlen hp] |
             [k [a [b [hkx [hky [hxa [hyb [hab hp]]]]]]]]].
           ++ left. split; [simpl; lia |].
              intros i z hi hz. destruct i as [|i].
              ** simpl in hz. inversion hz; subst z. reflexivity.
              ** simpl in hz. simpl. apply hp; simpl in hi; try lia. exact hz.
           ++ right. exists (S k), a, b.
              split; [simpl; lia |]. split; [simpl; lia |]. split.
              ** simpl. exact hxa.
              ** split.
                 --- simpl. exact hyb.
                 --- split; [exact hab |].
                     intros i z hi hz. destruct i as [|i].
                     +++ simpl in hz. inversion hz; subst z. reflexivity.
                     +++ simpl in hz. simpl. apply hp; try lia. exact hz.
Qed.

Lemma LexPosition_iff : forall a b,
  LexPosition a b <->
  exists xs ys, decode a = Some xs /\ decode b = Some ys /\ LexLe xs ys.
Proof.
  intros a b. split.
  - intros [na [nb [[xs [ha hna]] [[ys [hb hnb]] h]]]].
    exists xs, ys. repeat split; try assumption.
    apply (proj1 (LexIndex_iff_LexLe xs ys)).
    destruct h as [[hle hp] | [k [x [y [hka [hkb [hax [hby [hxy hp]]]]]]]]].
    + left. split; [lia |]. intros i x hi hxi.
      assert (hai : NthElement a i x).
      { apply (NthElement_decode a i x xs ha). exact hxi. }
      apply (NthElement_decode b i x ys hb). apply hp; try lia. exact hai.
    + right. exists k, x, y. repeat split; try lia; try assumption.
      * apply (NthElement_decode a k x xs ha) in hax. exact hax.
      * apply (NthElement_decode b k y ys hb) in hby. exact hby.
      * intros i z hi hzi.
        assert (hai : NthElement a i z).
        { apply (NthElement_decode a i z xs ha). exact hzi. }
        apply (NthElement_decode b i z ys hb). apply hp; try lia. exact hai.
  - intros [xs [ys [ha [hb hlex]]]].
    exists (length xs), (length ys). repeat split.
    + exists xs. now split.
    + exists ys. now split.
    + apply (proj2 (LexIndex_iff_LexLe xs ys)) in hlex.
      destruct hlex as [[hlen hp] |
        [k [x [y [hkx [hky [hax [hby [hxy hp]]]]]]]]].
      * left. split; [exact hlen |]. intros i m hi hai.
        apply (NthElement_decode a i m xs ha) in hai.
        apply (NthElement_decode b i m ys hb). apply hp; assumption.
      * right. exists k, x, y. repeat split; try assumption.
        -- apply (NthElement_decode a k x xs ha). exact hax.
        -- apply (NthElement_decode b k y ys hb). exact hby.
        -- intros i m hi hai.
           apply (NthElement_decode a i m xs ha) in hai.
           apply (NthElement_decode b i m ys hb). apply hp; assumption.
Qed.

Lemma lexLeTermAt_nat : forall e a b,
  Formula.Sat natModel e (lexLeTermAt a b) <->
  exists xs ys,
    decode (Term.eval natModel e a) = Some xs /\
    decode (Term.eval natModel e b) = Some ys /\ LexLe xs ys.
Proof.
  intros. rewrite lexLeTermAt_position. apply LexPosition_iff.
Qed.

(** An outer list is lexicographically sorted when every entry is itself a
    valid list code and each adjacent decoded pair is in [LexLe]. *)
Definition LexSortedPosition (v : nat) : Prop :=
  exists n,
    HasLength v n /\
    (forall i c,
      i < n -> NthElement v i c -> ValidCode c) /\
    (forall i a b,
      S i < n ->
      NthElement v i a -> NthElement v (S i) b -> LexPosition a b).

Definition lexSortedTermAt (v : term) : formula :=
  pEx
    (pAnd3
      (hasLengthTermAt (liftTerm 1 v) (tVar 0))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 1))
          (pAll
            (pImp
              (nthElementTermAt (liftTerm 3 v) (tVar 1) (tVar 0))
              (validCodeTermAt (tVar 0))))))
      (pAll
        (pImp (Formula.ltTermAt (tSucc (tVar 0)) (tVar 1))
          (pAll (pAll
            (pImp
              (nthElementTermAt (liftTerm 4 v) (tVar 2) (tVar 1))
              (pImp
                (nthElementTermAt (liftTerm 4 v)
                  (tSucc (tVar 2)) (tVar 0))
                (lexLeTermAt (tVar 1) (tVar 0))))))))).

Lemma lexSortedTermAt_position : forall e v,
  Formula.Sat natModel e (lexSortedTermAt v) <->
  LexSortedPosition (Term.eval natModel e v).
Proof.
  intros e v. unfold lexSortedTermAt, LexSortedPosition, pAnd3.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite validCodeTermAt_nat.
  setoid_rewrite lexLeTermAt_position.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons.
  setoid_rewrite eval_liftTerm_scons3.
  setoid_rewrite eval_liftTerm_scons4.
  split.
  - intros [n [hlen [hvalid hadj]]].
    exists n. split; [exact hlen |]. split.
    + intros i c hi hci. exact (hvalid i hi c hci).
    + intros i a b hi hia hib. exact (hadj i hi a b hia hib).
  - intros [n [hlen [hvalid hadj]]].
    exists n. split; [exact hlen |]. split.
    + intros i hi c hci. exact (hvalid i c hi hci).
    + intros i hi a b hia hib. exact (hadj i a b hi hia hib).
Qed.

Lemma locallySorted_nth_error_gen : forall (A : Type) (R : A -> A -> Prop)
    (xs : list A),
  LocallySorted R xs <->
  forall i a b,
    nth_error xs i = Some a ->
    nth_error xs (S i) = Some b -> R a b.
Proof.
  intros A R xs. induction xs as [|x xs IH].
  - split.
    + intros _ i a b h. destruct i; discriminate.
    + intros _. constructor.
  - destruct xs as [|y ys].
    + split.
      * intros _ i a b h1 h2. destruct i; discriminate.
      * intros _. constructor.
    + split.
      * intros h i a b h1 h2.
        inversion h as [| |a0 b0 l htail hxy]; subst.
        destruct i as [|i].
        -- simpl in h1, h2. inversion h1; inversion h2; subst. exact hxy.
        -- simpl in h1, h2. apply (proj1 IH htail i a b h1 h2).
      * intro h. constructor.
        -- apply (proj2 IH). intros i a b h1 h2.
           apply (h (S i) a b); simpl; assumption.
        -- exact (h 0 x y eq_refl eq_refl).
Qed.

Lemma decodeCodes_nth_code : forall codes xss i c,
  decodeCodes codes = Some xss ->
  nth_error codes i = Some c ->
  exists xs, nth_error xss i = Some xs /\ decode c = Some xs.
Proof.
  induction codes as [|d codes IH]; intros xss i c hdecode hnth.
  - destruct i; discriminate.
  - simpl in hdecode.
    destruct (decode d) as [ys|] eqn:hd; try discriminate.
    destruct (decodeCodes codes) as [yss|] eqn:hcodes; try discriminate.
    inversion hdecode; subst xss. destruct i as [|i].
    + simpl in hnth. inversion hnth; subst c. exists ys. now split.
    + simpl in hnth. destruct (IH yss i c eq_refl hnth) as [zs [hzs hc]].
      exists zs. split; [exact hzs | exact hc].
Qed.

Lemma LexSortedPosition_iff : forall v,
  LexSortedPosition v <-> LexSortedCode v.
Proof.
  intro v. split.
  - intros [n [[codes [hv hlen]] [hvalid hadj]]].
    assert (hvalidCodes : Forall ValidCode codes).
    {
      apply Forall_forall. intros c hc.
      apply In_nth_error in hc. destruct hc as [i hci].
      apply (hvalid i c).
      - rewrite <- hlen. apply nth_error_Some. rewrite hci. discriminate.
      - apply (NthElement_decode v i c codes hv). exact hci.
    }
    destruct (decodeCodes_exists_of_valid codes hvalidCodes) as [xss hxss].
    exists codes, xss. repeat split; try assumption.
    unfold LexSortedLists.
    apply (proj2 (Sorted_LocallySorted_iff LexLe xss)).
    apply (proj2 (locallySorted_nth_error_gen _ LexLe xss)).
    intros i xs ys hxi hyi.
    destruct (decodeCodes_nth codes xss i xs hxss hxi)
      as [a [hai hda]].
    destruct (decodeCodes_nth codes xss (S i) ys hxss hyi)
      as [b [hbi hdb]].
    assert (hi : S i < n).
    {
      rewrite <- hlen, (decodeCodes_length codes xss hxss).
      apply nth_error_Some. rewrite hyi. discriminate.
    }
    assert (hpa : NthElement v i a).
    { apply (NthElement_decode v i a codes hv). exact hai. }
    assert (hpb : NthElement v (S i) b).
    { apply (NthElement_decode v (S i) b codes hv). exact hbi. }
    pose proof (hadj i a b hi hpa hpb) as hlex.
    apply (proj1 (LexPosition_iff a b)) in hlex.
    destruct hlex as [xs' [ys' [hda' [hdb' hle]]]].
    pose proof (decode_functional a xs xs' hda hda') as hxs. subst xs'.
    pose proof (decode_functional b ys ys' hdb hdb') as hys. subst ys'.
    exact hle.
  - intros [codes [xss [hv [hxss hsorted]]]].
    exists (length codes). split.
    + exists codes. now split.
    + split.
      * intros i c hi hci.
        apply (NthElement_decode v i c codes hv) in hci.
        pose proof (decodeCodes_entries_valid codes xss hxss) as hall.
        apply Forall_forall with (x := c) in hall.
        -- exact hall.
        -- apply nth_error_In with (n := i). exact hci.
      * intros i a b hi hia hib.
        apply (NthElement_decode v i a codes hv) in hia.
        apply (NthElement_decode v (S i) b codes hv) in hib.
        destruct (decodeCodes_nth_code codes xss i a hxss hia)
          as [xs [hxi hda]].
        destruct (decodeCodes_nth_code codes xss (S i) b hxss hib)
          as [ys [hyi hdb]].
        apply (proj2 (LexPosition_iff a b)).
        exists xs, ys. repeat split; try assumption.
        pose proof (proj1 (Sorted_LocallySorted_iff LexLe xss) hsorted)
          as hlocal.
        exact (proj1 (locallySorted_nth_error_gen _ LexLe xss)
          hlocal i xs ys hxi hyi).
Qed.

Lemma lexSortedTermAt_nat : forall e v,
  Formula.Sat natModel e (lexSortedTermAt v) <->
  LexSortedCode (Term.eval natModel e v).
Proof.
  intros. rewrite lexSortedTermAt_position. apply LexSortedPosition_iff.
Qed.

(** Exact lexicographic enumeration of the distinct permutations of a coded
    base list.  The final universal quantifier is deliberately unbounded:
    every valid coded permutation must occur in the outer list. *)
Definition AllPermutationsPosition (v w : nat) : Prop :=
  ValidCode v /\
  ValidCode w /\
  NoDuplicatesCode v /\
  LexSortedCode v /\
  (forall i p, NthElement v i p -> PermutationCode p w) /\
  (forall p,
    ValidCode p -> PermutationCode p w ->
    exists i, NthElement v i p).

Definition allPermutationsTermAt (v w : term) : formula :=
  pAnd6
    (validCodeTermAt v)
    (validCodeTermAt w)
    (noDuplicatesTermAt v)
    (lexSortedTermAt v)
    (pAll (pAll
      (pImp
        (nthElementTermAt (liftTerm 2 v) (tVar 1) (tVar 0))
        (permutationTermAt (tVar 0) (liftTerm 2 w)))))
    (pAll
      (pImp (validCodeTermAt (tVar 0))
        (pImp
          (permutationTermAt (tVar 0) (liftTerm 1 w))
          (pEx
            (nthElementTermAt (liftTerm 2 v) (tVar 0) (tVar 1)))))).

Lemma allPermutationsTermAt_position : forall e v w,
  Formula.Sat natModel e (allPermutationsTermAt v w) <->
  AllPermutationsPosition
    (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros e v w.
  unfold allPermutationsTermAt, AllPermutationsPosition, pAnd6.
  cbn [Formula.Sat].
  setoid_rewrite validCodeTermAt_nat.
  setoid_rewrite noDuplicatesTermAt_nat.
  setoid_rewrite lexSortedTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite permutationTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons.
  setoid_rewrite eval_liftTerm_scons2.
  reflexivity.
Qed.

Lemma NoDup_map_listCode : forall xss,
  NoDup xss -> NoDup (map listCode xss).
Proof.
  intros xss h. induction h as [|xs xss hnotin hnodup IH].
  - constructor.
  - simpl. constructor.
    + intro hin. apply in_map_iff in hin.
      destruct hin as [ys [hcode hin]].
      apply hnotin. apply listCode_injective in hcode. now subst ys.
    + exact IH.
Qed.

Lemma AllPermutationsPosition_iff : forall v w,
  AllPermutationsPosition v w <-> AllPermutationsCode v w.
Proof.
  intros v w. split.
  - intros [[codes hv] [[base hw]
      [hndup [hlex [hsound hcomplete]]]]].
    destruct hndup as [codes' [hv' hcodesNoDup]].
    destruct hlex as [codes'' [xss [hv'' [hxss hsorted]]]].
    pose proof (decode_functional v codes codes' hv hv') as hc'. subst codes'.
    pose proof (decode_functional v codes codes'' hv hv'') as hc''. subst codes''.
    exists codes, xss, base. split; [exact hv |].
    split; [exact hxss |]. split; [exact hw |].
    unfold CanonicalPermutations. split; [exact hsorted |]. split.
    + apply NoDup_map_inv with (f := listCode).
      rewrite (decodeCodes_sound codes xss hxss). exact hcodesNoDup.
    + intro ys. split.
      * intro hin.
        assert (hcodeIn : In (listCode ys) codes).
        {
          rewrite <- (decodeCodes_sound codes xss hxss).
          apply in_map. exact hin.
        }
        apply In_nth_error in hcodeIn. destruct hcodeIn as [i hcode].
        assert (hnth : NthElement v i (listCode ys)).
        { apply (NthElement_decode v i (listCode ys) codes hv). exact hcode. }
        destruct (hsound i (listCode ys) hnth) as
          [ys' [base' [hys' [hbase' hperm]]]].
        pose proof (decode_functional (listCode ys) ys ys'
          (decode_listCode ys) hys') as hys. subst ys'.
        pose proof (decode_functional w base base' hw hbase') as hb.
        subst base'. exact hperm.
      * intro hperm.
        assert (hpvalid : ValidCode (listCode ys)).
        { exists ys. apply decode_listCode. }
        assert (hpperm : PermutationCode (listCode ys) w).
        { exists ys, base. repeat split; try assumption. apply decode_listCode. }
        destruct (hcomplete (listCode ys) hpvalid hpperm) as [i hi].
        apply (NthElement_decode v i (listCode ys) codes hv) in hi.
        apply nth_error_In in hi.
        rewrite <- (decodeCodes_sound codes xss hxss) in hi.
        apply in_map_iff in hi. destruct hi as [ys' [hcode hin]].
        apply listCode_injective in hcode. now subst ys'.
  - intros [codes [xss [base [hv [hxss [hw hcanonical]]]]]].
    destruct hcanonical as [hsorted [hxssNoDup hiff]].
    repeat split.
    + now exists codes.
    + now exists base.
    + exists codes. split; [exact hv |].
      rewrite <- (decodeCodes_sound codes xss hxss).
      apply NoDup_map_listCode. exact hxssNoDup.
    + exists codes, xss. repeat split; assumption.
    + intros i p hip.
      apply (NthElement_decode v i p codes hv) in hip.
      destruct (decodeCodes_nth_code codes xss i p hxss hip)
        as [ys [hys hp]].
      exists ys, base. repeat split; try assumption.
      apply (proj1 (hiff ys)). apply nth_error_In in hys. exact hys.
    + intros p [ys hp] [ys' [base' [hp' [hw' hperm]]]].
      pose proof (decode_functional p ys ys' hp hp') as hys. subst ys'.
      pose proof (decode_functional w base base' hw hw') as hb. subst base'.
      assert (hin : In ys xss).
      { apply (proj2 (hiff ys)). exact hperm. }
      assert (hcodeIn : In (listCode ys) codes).
      {
        rewrite <- (decodeCodes_sound codes xss hxss).
        apply in_map. exact hin.
      }
      apply In_nth_error in hcodeIn. destruct hcodeIn as [i hi].
      exists i. apply (NthElement_decode v i p codes hv).
      apply listCode_decode in hp. now rewrite <- hp.
Qed.

Lemma allPermutationsTermAt_nat : forall e v w,
  Formula.Sat natModel e (allPermutationsTermAt v w) <->
  AllPermutationsCode
    (Term.eval natModel e v) (Term.eval natModel e w).
Proof.
  intros. rewrite allPermutationsTermAt_position.
  apply AllPermutationsPosition_iff.
Qed.

(** * Aggregate traces

    A scalar aggregate is certified by a canonically coded list of partial
    values.  The trace has one more entry than the input, starts at [base],
    and applies [combine] at every input position.  In particular, scalar
    results are never (incorrectly) required to be valid list codes. *)
Definition AggregatePosition
    (combine : nat -> nat -> nat) (base p v : nat) : Prop :=
  exists len trace,
    HasLength v len /\
    HasLength trace (S len) /\
    NthElement trace 0 base /\
    NthElement trace len p /\
    forall i x cur next,
      i < len ->
      NthElement v i x ->
      NthElement trace i cur ->
      NthElement trace (S i) next ->
      next = combine cur x.

Definition SumElementsPosition (p v : nat) : Prop :=
  AggregatePosition Nat.add 0 p v.

Definition ProductElementsPosition (p v : nat) : Prop :=
  AggregatePosition Nat.mul 1 p v.

Definition sumElementsTermAt (p v : term) : formula :=
  pEx (pEx
    (pAnd5
      (hasLengthTermAt (liftTerm 2 v) (tVar 1))
      (hasLengthTermAt (tVar 0) (tSucc (tVar 1)))
      (nthElementTermAt (tVar 0) tZero tZero)
      (nthElementTermAt (tVar 0) (tVar 1) (liftTerm 2 p))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 2))
          (pAll (pAll (pAll
            (pImp
              (nthElementTermAt (liftTerm 6 v) (tVar 3) (tVar 2))
              (pImp
                (nthElementTermAt (tVar 4) (tVar 3) (tVar 1))
                (pImp
                  (nthElementTermAt (tVar 4)
                    (tSucc (tVar 3)) (tVar 0))
                  (pEq (tVar 0) (tAdd (tVar 1) (tVar 2))))))))))))).

Definition productElementsTermAt (p v : term) : formula :=
  pEx (pEx
    (pAnd5
      (hasLengthTermAt (liftTerm 2 v) (tVar 1))
      (hasLengthTermAt (tVar 0) (tSucc (tVar 1)))
      (nthElementTermAt (tVar 0) tZero (tSucc tZero))
      (nthElementTermAt (tVar 0) (tVar 1) (liftTerm 2 p))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 2))
          (pAll (pAll (pAll
            (pImp
              (nthElementTermAt (liftTerm 6 v) (tVar 3) (tVar 2))
              (pImp
                (nthElementTermAt (tVar 4) (tVar 3) (tVar 1))
                (pImp
                  (nthElementTermAt (tVar 4)
                    (tSucc (tVar 3)) (tVar 0))
                  (pEq (tVar 0) (tMul (tVar 1) (tVar 2))))))))))))).

Lemma sumElementsTermAt_position : forall e p v,
  Formula.Sat natModel e (sumElementsTermAt p v) <->
  SumElementsPosition
    (Term.eval natModel e p) (Term.eval natModel e v).
Proof.
  intros e p v.
  unfold sumElementsTermAt, SumElementsPosition, AggregatePosition, pAnd5.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons2.
  setoid_rewrite eval_liftTerm_scons6.
  split.
  - intros [len [trace [hv [ht [hbase [hfinal hstep]]]]]].
    exists len, trace. repeat split; try assumption.
    intros i x cur next hi hvi hti htn.
    exact (hstep i hi x cur next hvi hti htn).
  - intros [len [trace [hv [ht [hbase [hfinal hstep]]]]]].
    exists len, trace. repeat split; try assumption.
    intros i hi x cur next hvi hti htn.
    exact (hstep i x cur next hi hvi hti htn).
Qed.

Lemma productElementsTermAt_position : forall e p v,
  Formula.Sat natModel e (productElementsTermAt p v) <->
  ProductElementsPosition
    (Term.eval natModel e p) (Term.eval natModel e v).
Proof.
  intros e p v.
  unfold productElementsTermAt, ProductElementsPosition,
    AggregatePosition, pAnd5.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons2.
  setoid_rewrite eval_liftTerm_scons6.
  split.
  - intros [len [trace [hv [ht [hbase [hfinal hstep]]]]]].
    exists len, trace. repeat split; try assumption.
    intros i x cur next hi hvi hti htn.
    exact (hstep i hi x cur next hvi hti htn).
  - intros [len [trace [hv [ht [hbase [hfinal hstep]]]]]].
    exists len, trace. repeat split; try assumption.
    intros i hi x cur next hvi hti htn.
    exact (hstep i x cur next hi hvi hti htn).
Qed.

Definition prefixFolds
    (combine : nat -> nat -> nat) (base : nat) (xs : list nat) : list nat :=
  map (fun i => fold_left combine (firstn i xs) base)
    (seq 0 (S (length xs))).

Lemma prefixFolds_length : forall combine base xs,
  length (prefixFolds combine base xs) = S (length xs).
Proof.
  intros. unfold prefixFolds. rewrite map_length, seq_length. reflexivity.
Qed.

Lemma prefixFolds_nth : forall combine base xs i,
  i <= length xs ->
  nth_error (prefixFolds combine base xs) i =
    Some (fold_left combine (firstn i xs) base).
Proof.
  intros combine base xs i hi. unfold prefixFolds.
  rewrite nth_error_map, nth_error_seq.
  destruct (i <? S (length xs)) eqn:h.
  - simpl. now replace (0 + i) with i by lia.
  - apply Nat.ltb_ge in h. lia.
Qed.

Lemma firstn_step_nth : forall (A : Type) (xs : list A) i x,
  i < length xs -> nth_error xs i = Some x ->
  firstn (S i) xs = firstn i xs ++ [x].
Proof.
  intros A xs. induction xs as [|y ys IH]; intros i x hi hnth;
    [simpl in hi; lia |].
  destruct i as [|i].
  - simpl in hnth. inversion hnth; subst x. reflexivity.
  - simpl in hnth |- *. f_equal.
    apply IH; [simpl in hi; lia | exact hnth].
Qed.

Lemma fold_left_firstn_step : forall
    (combine : nat -> nat -> nat) (base : nat) (xs : list nat) i x,
  i < length xs -> nth_error xs i = Some x ->
  fold_left combine (firstn (S i) xs) base =
    combine (fold_left combine (firstn i xs) base) x.
Proof.
  intros. rewrite (firstn_step_nth _ xs i x H H0), fold_left_app.
  reflexivity.
Qed.

Lemma AggregatePosition_iff : forall combine base p v,
  AggregatePosition combine base p v <->
  exists xs,
    decode v = Some xs /\ fold_left combine xs base = p.
Proof.
  intros combine base p v. split.
  - intros [len [trace
      [[xs [hv hlen]] [[ts [ht htlen]] [hbase [hfinal hstep]]]]]].
    exists xs. split; [exact hv |].
    assert (hinv : forall i, i <= length xs ->
      nth_error ts i = Some (fold_left combine (firstn i xs) base)).
    {
      intros i hi. induction i as [|i IHi].
      - apply (NthElement_decode trace 0 base ts ht) in hbase.
        simpl. exact hbase.
      - assert (hil : i < length xs) by lia.
        specialize (IHi ltac:(lia)).
        destruct (nth_error_exists_of_lt xs i hil) as [x hx].
        destruct (nth_error_exists_of_lt ts (S i) ltac:(lia)) as [next hn].
        assert (hvi : NthElement v i x).
        { apply (NthElement_decode v i x xs hv). exact hx. }
        assert (hti : NthElement trace i
          (fold_left combine (firstn i xs) base)).
        { apply (NthElement_decode trace i _ ts ht). exact IHi. }
        assert (htn : NthElement trace (S i) next).
        { apply (NthElement_decode trace (S i) next ts ht). exact hn. }
        pose proof (hstep i x _ next ltac:(lia) hvi hti htn) as hs.
        rewrite (fold_left_firstn_step combine base xs i x hil hx).
        now subst next.
    }
    apply (NthElement_decode trace len p ts ht) in hfinal.
    specialize (hinv (length xs) ltac:(lia)).
    rewrite firstn_all in hinv. rewrite hlen in hinv.
    rewrite hfinal in hinv. inversion hinv. reflexivity.
  - intros [xs [hv hfold]].
    set (ts := prefixFolds combine base xs).
    set (trace := listCode ts).
    exists (length xs), trace. repeat split.
    + exists xs. now split.
    + exists ts. split.
      * unfold trace. apply decode_listCode.
      * unfold ts. apply prefixFolds_length.
    + exists ts. split.
      * unfold trace. apply decode_listCode.
      * unfold ts. rewrite prefixFolds_nth by lia. reflexivity.
    + exists ts. split.
      * unfold trace. apply decode_listCode.
      * unfold ts. rewrite prefixFolds_nth by lia.
        rewrite firstn_all, hfold. reflexivity.
    + intros i x cur next hi hvi hti htn.
      apply (NthElement_decode v i x xs hv) in hvi.
      apply (NthElement_decode trace i cur ts
        ltac:(unfold trace; apply decode_listCode)) in hti.
      apply (NthElement_decode trace (S i) next ts
        ltac:(unfold trace; apply decode_listCode)) in htn.
      unfold ts in hti, htn.
      rewrite prefixFolds_nth in hti by lia.
      rewrite prefixFolds_nth in htn by lia.
      inversion hti; inversion htn; subst cur next.
      apply fold_left_firstn_step; assumption.
Qed.

Lemma fold_left_add_list_sum : forall xs base,
  fold_left Nat.add xs base = base + list_sum xs.
Proof.
  induction xs as [|x xs IH]; intro base; simpl.
  - lia.
  - rewrite IH. simpl. lia.
Qed.

Lemma fold_left_mul_natListProduct : forall xs base,
  fold_left Nat.mul xs base = base * natListProduct xs.
Proof.
  induction xs as [|x xs IH]; intro base; simpl.
  - lia.
  - rewrite IH. simpl. nia.
Qed.

Lemma SumElementsPosition_iff : forall p v,
  SumElementsPosition p v <-> SumElementsCode p v.
Proof.
  intros p v. unfold SumElementsPosition, SumElementsCode.
  rewrite AggregatePosition_iff. split.
  - intros [xs [hv h]]. exists xs. split; [exact hv |].
    rewrite fold_left_add_list_sum in h. simpl in h. exact h.
  - intros [xs [hv h]]. exists xs. split; [exact hv |].
    rewrite fold_left_add_list_sum. simpl. exact h.
Qed.

Lemma ProductElementsPosition_iff : forall p v,
  ProductElementsPosition p v <-> ProductElementsCode p v.
Proof.
  intros p v. unfold ProductElementsPosition, ProductElementsCode.
  rewrite AggregatePosition_iff. split.
  - intros [xs [hv h]]. exists xs. split; [exact hv |].
    rewrite fold_left_mul_natListProduct in h. simpl in h. lia.
  - intros [xs [hv h]]. exists xs. split; [exact hv |].
    rewrite fold_left_mul_natListProduct. simpl. lia.
Qed.

Lemma sumElementsTermAt_nat : forall e p v,
  Formula.Sat natModel e (sumElementsTermAt p v) <->
  SumElementsCode (Term.eval natModel e p) (Term.eval natModel e v).
Proof.
  intros. rewrite sumElementsTermAt_position. apply SumElementsPosition_iff.
Qed.

Lemma productElementsTermAt_nat : forall e p v,
  Formula.Sat natModel e (productElementsTermAt p v) <->
  ProductElementsCode (Term.eval natModel e p) (Term.eval natModel e v).
Proof.
  intros. rewrite productElementsTermAt_position.
  apply ProductElementsPosition_iff.
Qed.

(** Extrema are required to occur in the list.  The existential indexed
    occurrence is what makes both predicates false on the empty list. *)
Definition GreatestPosition (m v : nat) : Prop :=
  exists i,
    NthElement v i m /\
    forall j x, NthElement v j x -> x <= m.

Definition LeastPosition (m v : nat) : Prop :=
  exists i,
    NthElement v i m /\
    forall j x, NthElement v j x -> m <= x.

Definition greatestTermAt (m v : term) : formula :=
  pEx
    (pAnd
      (nthElementTermAt (liftTerm 1 v) (tVar 0) (liftTerm 1 m))
      (pAll (pAll
        (pImp
          (nthElementTermAt (liftTerm 3 v) (tVar 1) (tVar 0))
          (Formula.ltTermAt (tVar 0) (tSucc (liftTerm 3 m))))))).

Definition leastTermAt (m v : term) : formula :=
  pEx
    (pAnd
      (nthElementTermAt (liftTerm 1 v) (tVar 0) (liftTerm 1 m))
      (pAll (pAll
        (pImp
          (nthElementTermAt (liftTerm 3 v) (tVar 1) (tVar 0))
          (Formula.ltTermAt (liftTerm 3 m) (tSucc (tVar 0))))))).

Lemma greatestTermAt_position : forall e m v,
  Formula.Sat natModel e (greatestTermAt m v) <->
  GreatestPosition (Term.eval natModel e m) (Term.eval natModel e v).
Proof.
  intros e m v. unfold greatestTermAt, GreatestPosition.
  cbn [Formula.Sat].
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons.
  setoid_rewrite eval_liftTerm_scons3.
  split.
  - intros [i [hi hbound]]. exists i. split; [exact hi |].
    intros j x hj. pose proof (hbound j x hj). lia.
  - intros [i [hi hbound]]. exists i. split; [exact hi |].
    intros j x hj. pose proof (hbound j x hj). lia.
Qed.

Lemma leastTermAt_position : forall e m v,
  Formula.Sat natModel e (leastTermAt m v) <->
  LeastPosition (Term.eval natModel e m) (Term.eval natModel e v).
Proof.
  intros e m v. unfold leastTermAt, LeastPosition.
  cbn [Formula.Sat].
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons.
  setoid_rewrite eval_liftTerm_scons3.
  split.
  - intros [i [hi hbound]]. exists i. split; [exact hi |].
    intros j x hj. pose proof (hbound j x hj). lia.
  - intros [i [hi hbound]]. exists i. split; [exact hi |].
    intros j x hj. pose proof (hbound j x hj). lia.
Qed.

Lemma GreatestPosition_iff : forall m v,
  GreatestPosition m v <-> GreatestCode m v.
Proof.
  intros m v. split.
  - intros [i [[xs [hv hmi]] hbound]].
    exists xs. split; [exact hv |]. split.
    + apply nth_error_In in hmi. exact hmi.
    + apply Forall_forall. intros x hx.
      apply In_nth_error in hx. destruct hx as [j hx].
      apply hbound with (j := j).
      apply (NthElement_decode v j x xs hv). exact hx.
  - intros [xs [hv [hmin hbound]]].
    apply In_nth_error in hmin. destruct hmin as [i hmi].
    exists i. split.
    + apply (NthElement_decode v i m xs hv). exact hmi.
    + intros j x hj.
      apply (NthElement_decode v j x xs hv) in hj.
      apply Forall_forall with (x := x) in hbound.
      * exact hbound.
      * apply nth_error_In in hj. exact hj.
Qed.

Lemma LeastPosition_iff : forall m v,
  LeastPosition m v <-> LeastCode m v.
Proof.
  intros m v. split.
  - intros [i [[xs [hv hmi]] hbound]].
    exists xs. split; [exact hv |]. split.
    + apply nth_error_In in hmi. exact hmi.
    + apply Forall_forall. intros x hx.
      apply In_nth_error in hx. destruct hx as [j hx].
      apply hbound with (j := j).
      apply (NthElement_decode v j x xs hv). exact hx.
  - intros [xs [hv [hmin hbound]]].
    apply In_nth_error in hmin. destruct hmin as [i hmi].
    exists i. split.
    + apply (NthElement_decode v i m xs hv). exact hmi.
    + intros j x hj.
      apply (NthElement_decode v j x xs hv) in hj.
      apply Forall_forall with (x := x) in hbound.
      * exact hbound.
      * apply nth_error_In in hj. exact hj.
Qed.

Lemma greatestTermAt_nat : forall e m v,
  Formula.Sat natModel e (greatestTermAt m v) <->
  GreatestCode (Term.eval natModel e m) (Term.eval natModel e v).
Proof. intros. rewrite greatestTermAt_position. apply GreatestPosition_iff. Qed.

Lemma leastTermAt_nat : forall e m v,
  Formula.Sat natModel e (leastTermAt m v) <->
  LeastCode (Term.eval natModel e m) (Term.eval natModel e v).
Proof. intros. rewrite leastTermAt_position. apply LeastPosition_iff. Qed.

(** A median certificate is a coded nondecreasing permutation plus one of
    the two division-free length/index cases.  Actual [NthElement] witnesses
    ensure that no out-of-range totalized projection can satisfy a case. *)
Definition TwiceMedianPosition (m v : nat) : Prop :=
  exists sorted,
    PermutationCode sorted v /\
    SortedCode sorted /\
    ((exists k a,
        HasLength v (k + k + 1) /\
        NthElement sorted k a /\
        m = a + a) \/
     exists k a b,
        HasLength v (S k + S k) /\
        NthElement sorted k a /\
        NthElement sorted (S k) b /\
        m = a + b).

Definition twiceMedianTermAt (m v : term) : formula :=
  pEx
    (pAnd3
      (permutationTermAt (tVar 0) (liftTerm 1 v))
      (sortedTermAt (tVar 0))
      (pOr
        (pEx (pEx
          (pAnd3
            (hasLengthTermAt (liftTerm 3 v)
              (tSucc (tAdd (tVar 1) (tVar 1))))
            (nthElementTermAt (tVar 2) (tVar 1) (tVar 0))
            (pEq (liftTerm 3 m) (tAdd (tVar 0) (tVar 0))))))
        (pEx (pEx (pEx
          (pAnd4
            (hasLengthTermAt (liftTerm 4 v)
              (tAdd (tSucc (tVar 2)) (tSucc (tVar 2))))
            (nthElementTermAt (tVar 3) (tVar 2) (tVar 1))
            (nthElementTermAt (tVar 3) (tSucc (tVar 2)) (tVar 0))
            (pEq (liftTerm 4 m) (tAdd (tVar 1) (tVar 0))))))))).

Lemma twiceMedianTermAt_position : forall e m v,
  Formula.Sat natModel e (twiceMedianTermAt m v) <->
  TwiceMedianPosition (Term.eval natModel e m) (Term.eval natModel e v).
Proof.
  intros e m v. unfold twiceMedianTermAt, TwiceMedianPosition, pAnd3, pAnd4.
  cbn [Formula.Sat].
  setoid_rewrite permutationTermAt_nat.
  setoid_rewrite sortedTermAt_nat.
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons.
  setoid_rewrite eval_liftTerm_scons3.
  setoid_rewrite eval_liftTerm_scons4.
  split.
  - intros [sorted [hperm [hsorted hcase]]].
    exists sorted. split; [exact hperm |]. split; [exact hsorted |].
    destruct hcase as [[k [a [hlen [hnth heq]]]] |
      [k [a [b [hlen [ha [hb heq]]]]]]].
    + left. exists k, a. split.
      * replace (k + k + 1) with (S (k + k)) by lia. exact hlen.
      * split; [exact hnth | lia].
    + right. exists k, a, b. split.
      * exact hlen.
      * split; [exact ha |]. split; [exact hb | lia].
  - intros [sorted [hperm [hsorted hcase]]].
    exists sorted. split; [exact hperm |]. split; [exact hsorted |].
    destruct hcase as [[k [a [hlen [hnth heq]]]] |
      [k [a [b [hlen [ha [hb heq]]]]]]].
    + left. exists k, a. split.
      * replace (S (k + k)) with (k + k + 1) by lia. exact hlen.
      * split; [exact hnth | lia].
    + right. exists k, a, b. split.
      * exact hlen.
      * split; [exact ha |]. split; [exact hb | lia].
Qed.

Lemma TwiceMedianPosition_iff : forall m v,
  TwiceMedianPosition m v <-> TwiceMedianCode m v.
Proof.
  intros m v. split.
  - intros [sorted [hperm [hsorted hcase]]].
    destruct hperm as [ss [xs [hs [hv hp]]]].
    destruct hsorted as [ss' [hs' hsort]].
    pose proof (decode_functional sorted ss ss' hs hs') as hss. subst ss'.
    exists xs. split; [exact hv |].
    exists ss. split; [exact hp |]. split; [exact hsort |].
    destruct hcase as [[k [a [[xs' [hv' hlen]] [hnth heq]]]] |
      [k [a [b [[xs' [hv' hlen]] [ha [hb heq]]]]]]].
    + pose proof (decode_functional v xs xs' hv hv') as hx. subst xs'.
      left. exists k, a. repeat split; try assumption.
      apply (NthElement_decode sorted k a ss hs) in hnth. exact hnth.
    + pose proof (decode_functional v xs xs' hv hv') as hx. subst xs'.
      right. exists k, a, b. repeat split; try assumption.
      * apply (NthElement_decode sorted k a ss hs) in ha. exact ha.
      * apply (NthElement_decode sorted (S k) b ss hs) in hb. exact hb.
  - intros [xs [hv [ss [hp [hsort hcase]]]]].
    set (sorted := listCode ss).
    exists sorted. split.
    + exists ss, xs. repeat split; try assumption.
      unfold sorted. apply decode_listCode.
    + split.
      * exists ss. split; [unfold sorted; apply decode_listCode | exact hsort].
      * destruct hcase as [[k [a [hlen [ha heq]]]] |
          [k [a [b [hlen [ha [hb heq]]]]]]].
        -- left. exists k, a. repeat split; try assumption.
           ++ exists xs. now split.
           ++ apply (NthElement_decode sorted k a ss
                ltac:(unfold sorted; apply decode_listCode)). exact ha.
        -- right. exists k, a, b. repeat split; try assumption.
           ++ exists xs. now split.
           ++ apply (NthElement_decode sorted k a ss
                ltac:(unfold sorted; apply decode_listCode)). exact ha.
           ++ apply (NthElement_decode sorted (S k) b ss
                ltac:(unfold sorted; apply decode_listCode)). exact hb.
Qed.

Lemma twiceMedianTermAt_nat : forall e m v,
  Formula.Sat natModel e (twiceMedianTermAt m v) <->
  TwiceMedianCode (Term.eval natModel e m) (Term.eval natModel e v).
Proof.
  intros. rewrite twiceMedianTermAt_position. apply TwiceMedianPosition_iff.
Qed.

(** The mode certificate fixes the positive count of the candidate once,
    then checks only values occurring at bounded positions.  Every possible
    rival occurs at such a position, while absent naturals have count zero. *)
Definition UniqueModePosition (m v : nat) : Prop :=
  exists len cm,
    HasLength v len /\
    OccurrencesCode v cm m /\
    0 < cm /\
    (exists i, i < len /\ NthElement v i m) /\
    forall j x,
      j < len -> NthElement v j x -> x <> m ->
      exists cx, OccurrencesCode v cx x /\ cx < cm.

Definition uniqueModeTermAt (m v : term) : formula :=
  pEx (pEx
    (pAnd5
      (hasLengthTermAt (liftTerm 2 v) (tVar 1))
      (occurrencesTermAt (liftTerm 2 v) (tVar 0) (liftTerm 2 m))
      (Formula.ltTermAt tZero (tVar 0))
      (pEx
        (pAnd
          (Formula.ltTermAt (tVar 0) (tVar 2))
          (nthElementTermAt (liftTerm 3 v) (tVar 0) (liftTerm 3 m))))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 2))
          (pAll
            (pImp
              (nthElementTermAt (liftTerm 4 v) (tVar 1) (tVar 0))
              (pImp
                (pNot (pEq (tVar 0) (liftTerm 4 m)))
                (pEx
                  (pAnd
                    (occurrencesTermAt
                      (liftTerm 5 v) (tVar 0) (tVar 1))
                    (Formula.ltTermAt (tVar 0) (tVar 3))))))))))).

Lemma uniqueModeTermAt_position : forall e m v,
  Formula.Sat natModel e (uniqueModeTermAt m v) <->
  UniqueModePosition (Term.eval natModel e m) (Term.eval natModel e v).
Proof.
  intros e m v.
  unfold uniqueModeTermAt, UniqueModePosition, pAnd5, pNot.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite occurrencesTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons2.
  setoid_rewrite eval_liftTerm_scons3.
  setoid_rewrite eval_liftTerm_scons4.
  setoid_rewrite eval_liftTerm_scons5.
  split.
  - intros [len [cm [hlen [hcm [hpos [hcandidate hdom]]]]]].
    exists len, cm. repeat split; try assumption.
    intros j x hj hjx hneq. exact (hdom j hj x hjx hneq).
  - intros [len [cm [hlen [hcm [hpos [hcandidate hdom]]]]]].
    exists len, cm. repeat split; try assumption.
    intros j hj x hjx hneq. exact (hdom j x hj hjx hneq).
Qed.

Lemma UniqueModePosition_iff : forall m v,
  UniqueModePosition m v <-> UniqueModeCode m v.
Proof.
  intros m v. split.
  - intros [len [cm
      [[xs [hv hlen]] [hcm [hpos [[i [hi hmi]] hdom]]]]]].
    destruct hcm as [xs' [hv' hcountm]].
    pose proof (decode_functional v xs xs' hv hv') as hxs. subst xs'.
    exists xs. split; [exact hv |]. split.
    + apply nth_error_In with (n := i).
      apply (NthElement_decode v i m xs hv) in hmi. exact hmi.
    + intros x hx hneq.
      apply In_nth_error in hx. destruct hx as [j hx].
      assert (hj : j < len).
      { rewrite <- hlen. apply nth_error_Some. rewrite hx. discriminate. }
      assert (hjx : NthElement v j x).
      { apply (NthElement_decode v j x xs hv). exact hx. }
      destruct (hdom j x hj hjx hneq) as [cx [hcx hlt]].
      destruct hcx as [ys [hvy hcountx]].
      pose proof (decode_functional v xs ys hv hvy) as hxy. subst ys.
      rewrite hcountx, hcountm. exact hlt.
  - intros [xs [hv [hmin hdom]]].
    set (cm := count_occ Nat.eq_dec xs m).
    exists (length xs), cm. repeat split.
    + exists xs. now split.
    + exists xs. split; [exact hv | reflexivity].
    + unfold cm. apply (proj1 (count_occ_In Nat.eq_dec xs m)). exact hmin.
    + apply In_nth_error in hmin. destruct hmin as [i hi].
      exists i. split.
      * apply nth_error_Some. rewrite hi. discriminate.
      * apply (NthElement_decode v i m xs hv). exact hi.
    + intros j x hj hjx hneq.
      apply (NthElement_decode v j x xs hv) in hjx.
      exists (count_occ Nat.eq_dec xs x). split.
      * exists xs. split; [exact hv | reflexivity].
      * unfold cm. apply hdom.
        -- apply nth_error_In in hjx. exact hjx.
        -- exact hneq.
Qed.

Lemma uniqueModeTermAt_nat : forall e m v,
  Formula.Sat natModel e (uniqueModeTermAt m v) <->
  UniqueModeCode (Term.eval natModel e m) (Term.eval natModel e v).
Proof.
  intros. rewrite uniqueModeTermAt_position. apply UniqueModePosition_iff.
Qed.

Definition validCodeFormula : formula := validCodeTermAt (tVar 0).
Definition hasLengthFormula : formula :=
  hasLengthTermAt (tVar 0) (tVar 1).
Definition nthElementFormula : formula :=
  nthElementTermAt (tVar 0) (tVar 1) (tVar 2).

Definition singletonFormula : formula :=
  singletonTermAt (tVar 0) (tVar 1).
Definition concatenationFormula : formula :=
  concatTermAt (tVar 0) (tVar 1) (tVar 2).
Definition flattenFormula : formula :=
  flattenTermAt (tVar 0) (tVar 1).
Definition occurrencesFormula : formula :=
  occurrencesTermAt (tVar 0) (tVar 1) (tVar 2).
Definition permutationFormula : formula :=
  permutationTermAt (tVar 0) (tVar 1).
Definition contiguousSubstringFormula : formula :=
  contiguousSubstringTermAt (tVar 0) (tVar 1).
Definition subsequenceFormula : formula :=
  subsequenceTermAt (tVar 0) (tVar 1).
Definition noDuplicatesFormula : formula :=
  noDuplicatesTermAt (tVar 0).
Definition sortedFormula : formula :=
  sortedTermAt (tVar 0).
Definition lexSortedFormula : formula :=
  lexSortedTermAt (tVar 0).
Definition allPermutationsFormula : formula :=
  allPermutationsTermAt (tVar 0) (tVar 1).
Definition sumElementsFormula : formula :=
  sumElementsTermAt (tVar 0) (tVar 1).
Definition productElementsFormula : formula :=
  productElementsTermAt (tVar 0) (tVar 1).
Definition greatestFormula : formula :=
  greatestTermAt (tVar 0) (tVar 1).
Definition leastFormula : formula :=
  leastTermAt (tVar 0) (tVar 1).
Definition twiceMedianFormula : formula :=
  twiceMedianTermAt (tVar 0) (tVar 1).
Definition uniqueModeFormula : formula :=
  uniqueModeTermAt (tVar 0) (tVar 1).

Theorem validCodeFormula_correct : forall e,
  Formula.Sat natModel e validCodeFormula <-> ValidCode (e 0).
Proof. intro e. unfold validCodeFormula. apply validCodeTermAt_nat. Qed.

Theorem hasLengthFormula_correct : forall e,
  Formula.Sat natModel e hasLengthFormula <-> HasLength (e 0) (e 1).
Proof. intro e. unfold hasLengthFormula. apply hasLengthTermAt_nat. Qed.

Theorem nthElementFormula_correct : forall e,
  Formula.Sat natModel e nthElementFormula <->
  NthElement (e 0) (e 1) (e 2).
Proof. intro e. unfold nthElementFormula. apply nthElementTermAt_nat. Qed.

Theorem singletonFormula_correct : forall e,
  Formula.Sat natModel e singletonFormula <-> SingletonCode (e 0) (e 1).
Proof. intro e. unfold singletonFormula. apply singletonTermAt_nat. Qed.

Theorem concatenationFormula_correct : forall e,
  Formula.Sat natModel e concatenationFormula <->
  ConcatenationCode (e 0) (e 1) (e 2).
Proof. intro e. unfold concatenationFormula. apply concatTermAt_nat. Qed.

Theorem flattenFormula_correct : forall e,
  Formula.Sat natModel e flattenFormula <-> FlattenCode (e 0) (e 1).
Proof. intro e. unfold flattenFormula. apply flattenTermAt_nat. Qed.

Theorem occurrencesFormula_correct : forall e,
  Formula.Sat natModel e occurrencesFormula <->
  OccurrencesCode (e 0) (e 1) (e 2).
Proof. intro e. unfold occurrencesFormula. apply occurrencesTermAt_nat. Qed.

Theorem permutationFormula_correct : forall e,
  Formula.Sat natModel e permutationFormula <-> PermutationCode (e 0) (e 1).
Proof. intro e. unfold permutationFormula. apply permutationTermAt_nat. Qed.

Theorem contiguousSubstringFormula_correct : forall e,
  Formula.Sat natModel e contiguousSubstringFormula <->
  ContiguousSubstringCode (e 0) (e 1).
Proof.
  intro e. unfold contiguousSubstringFormula.
  apply contiguousSubstringTermAt_nat.
Qed.

Theorem subsequenceFormula_correct : forall e,
  Formula.Sat natModel e subsequenceFormula <-> SubsequenceCode (e 0) (e 1).
Proof. intro e. unfold subsequenceFormula. apply subsequenceTermAt_nat. Qed.

Theorem noDuplicatesFormula_correct : forall e,
  Formula.Sat natModel e noDuplicatesFormula <-> NoDuplicatesCode (e 0).
Proof. intro e. unfold noDuplicatesFormula. apply noDuplicatesTermAt_nat. Qed.

Theorem sortedFormula_correct : forall e,
  Formula.Sat natModel e sortedFormula <-> SortedCode (e 0).
Proof. intro e. unfold sortedFormula. apply sortedTermAt_nat. Qed.

Theorem lexSortedFormula_correct : forall e,
  Formula.Sat natModel e lexSortedFormula <-> LexSortedCode (e 0).
Proof. intro e. unfold lexSortedFormula. apply lexSortedTermAt_nat. Qed.

Theorem allPermutationsFormula_correct : forall e,
  Formula.Sat natModel e allPermutationsFormula <->
  AllPermutationsCode (e 0) (e 1).
Proof.
  intro e. unfold allPermutationsFormula. apply allPermutationsTermAt_nat.
Qed.

Theorem sumElementsFormula_correct : forall e,
  Formula.Sat natModel e sumElementsFormula <->
  SumElementsCode (e 0) (e 1).
Proof. intro e. unfold sumElementsFormula. apply sumElementsTermAt_nat. Qed.

Theorem productElementsFormula_correct : forall e,
  Formula.Sat natModel e productElementsFormula <->
  ProductElementsCode (e 0) (e 1).
Proof.
  intro e. unfold productElementsFormula. apply productElementsTermAt_nat.
Qed.

Theorem greatestFormula_correct : forall e,
  Formula.Sat natModel e greatestFormula <-> GreatestCode (e 0) (e 1).
Proof. intro e. unfold greatestFormula. apply greatestTermAt_nat. Qed.

Theorem leastFormula_correct : forall e,
  Formula.Sat natModel e leastFormula <-> LeastCode (e 0) (e 1).
Proof. intro e. unfold leastFormula. apply leastTermAt_nat. Qed.

Theorem twiceMedianFormula_correct : forall e,
  Formula.Sat natModel e twiceMedianFormula <->
  TwiceMedianCode (e 0) (e 1).
Proof. intro e. unfold twiceMedianFormula. apply twiceMedianTermAt_nat. Qed.

Theorem uniqueModeFormula_correct : forall e,
  Formula.Sat natModel e uniqueModeFormula <-> UniqueModeCode (e 0) (e 1).
Proof. intro e. unfold uniqueModeFormula. apply uniqueModeTermAt_nat. Qed.

End PAListFormulas.
