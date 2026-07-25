(**
  Canonical structural-rank fragments of Peano arithmetic.

  This file packages an arbitrary finite list of genuine PA axioms inside a
  canonical fragment: all six non-induction axioms, together with induction
  instances whose source formulas have structural rank at most [n].  Thus it
  is enough to prove strictness for this one-parameter hierarchy.

  [PARankFragmentStrictness] is deliberately a proposition, not an axiom.  It
  states the remaining mathematical input in the strong Ryll--Nardzewski
  form: every rank fragment misses an induction instance.  The results below
  reduce it to the fragment-strictness premise and the non-finite-
  axiomatizability conclusion already established in [FiniteBasisReduction].
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import FiniteBasisReduction.

Import ListNotations.
Import PAFiniteBasisReduction.

Module PAHierarchyReduction.

(** Positive structural rank of arithmetic terms.  Bounding variable indices
    as well as tree depth makes every rank-bounded syntax class finite. *)
Fixpoint term_rank (t : PA.term) : nat :=
  match t with
  | PA.tVar n => S n
  | PA.tZero => 1
  | PA.tSucc a => S (term_rank a)
  | PA.tAdd a b => S (Nat.max (term_rank a) (term_rank b))
  | PA.tMul a b => S (Nat.max (term_rank a) (term_rank b))
  end.

(** Structural depth of formulas, including the terms in atomic equations. *)
Fixpoint formula_rank (phi : PA.formula) : nat :=
  match phi with
  | PA.pEq a b => S (Nat.max (term_rank a) (term_rank b))
  | PA.pBot => 1
  | PA.pImp a b => S (Nat.max (formula_rank a) (formula_rank b))
  | PA.pAnd a b => S (Nat.max (formula_rank a) (formula_rank b))
  | PA.pOr a b => S (Nat.max (formula_rank a) (formula_rank b))
  | PA.pAll a => S (formula_rank a)
  | PA.pEx a => S (formula_rank a)
  end.

(** Apply a binary constructor to every pair drawn from two finite lists. *)
Definition list_map2 {A B C : Type} (f : A -> B -> C)
    (xs : list A) (ys : list B) : list C :=
  flat_map (fun x => map (f x) ys) xs.

Lemma in_list_map2_iff : forall (A B C : Type) (f : A -> B -> C)
    (xs : list A) (ys : list B) z,
  In z (list_map2 f xs ys) <->
  exists x y, In x xs /\ In y ys /\ f x y = z.
Proof.
  intros A B C f xs ys z.
  unfold list_map2.
  rewrite in_flat_map.
  split.
  - intros [x [hx hz]].
    apply in_map_iff in hz.
    destruct hz as [y [hy hz]].
    exists x, y.
    repeat split; assumption.
  - intros [x [y [hx [hy hxy]]]].
    exists x.
    split; [exact hx |].
    apply in_map_iff.
    exists y.
    split; assumption.
Qed.

(** Forward membership in a [list_map2] enumeration: supply the two
    components and close each membership obligation with [tac]. *)
Ltac map2_member a b tac :=
  apply in_list_map2_iff; exists a, b; repeat split; try reflexivity; tac.

(** Inverse direction: unpack a [list_map2] membership hypothesis [H] and
    bound the resulting binary rank through [IH] on both components. *)
Ltac map2_rank_bound H IH :=
  apply in_list_map2_iff in H;
  let a := fresh "a" in let b := fresh "b" in
  let ha := fresh "ha" in let hb := fresh "hb" in let hab := fresh "hab" in
  destruct H as [a [b [ha [hb hab]]]];
  subst; simpl;
  apply (proj1 (Nat.succ_le_mono _ _));
  apply Nat.max_lub; [exact (IH a ha) | exact (IH b hb)].

(** Select the [n]-th summand (0-based) of a nested [app] enumeration:
    step right [n] times, then descend left. *)
Ltac in_app_pick n :=
  lazymatch n with
  | O => apply in_app_iff; left
  | S ?m => apply in_app_iff; right; in_app_pick m
  end.

(** Select the final summand after [n] right steps. *)
Ltac in_app_last n :=
  lazymatch n with
  | O => idtac
  | S ?m => apply in_app_iff; right; in_app_last m
  end.

(** Concrete enumerations of all terms and formulas up to a rank bound.
    At successor rank, every immediate subterm/subformula comes from the
    preceding list.  Variable indices are bounded explicitly by [seq]. *)
Fixpoint term_rank_enum (n : nat) : list PA.term :=
  match n with
  | 0 => []
  | S k =>
      map PA.tVar (seq 0 (S k)) ++
      [PA.tZero] ++
      map PA.tSucc (term_rank_enum k) ++
      list_map2 PA.tAdd (term_rank_enum k) (term_rank_enum k) ++
      list_map2 PA.tMul (term_rank_enum k) (term_rank_enum k)
  end.

Fixpoint formula_rank_enum (n : nat) : list PA.formula :=
  match n with
  | 0 => []
  | S k =>
      list_map2 PA.pEq (term_rank_enum k) (term_rank_enum k) ++
      [PA.pBot] ++
      list_map2 PA.pImp (formula_rank_enum k) (formula_rank_enum k) ++
      list_map2 PA.pAnd (formula_rank_enum k) (formula_rank_enum k) ++
      list_map2 PA.pOr (formula_rank_enum k) (formula_rank_enum k) ++
      map PA.pAll (formula_rank_enum k) ++
      map PA.pEx (formula_rank_enum k)
  end.

Lemma term_rank_enum_sound : forall n t,
  In t (term_rank_enum n) -> term_rank t <= n.
Proof.
  induction n as [|n IH]; intros t ht.
  - simpl in ht. contradiction.
  - cbn [term_rank_enum] in ht.
    repeat rewrite in_app_iff in ht.
    destruct ht as [ht | [ht | [ht | [ht | ht]]]].
    + apply in_map_iff in ht.
      destruct ht as [i [hi hseq]].
      subst t.
      apply in_seq in hseq.
      simpl. lia.
    + simpl in ht.
      destruct ht as [ht | []].
      subst t. simpl. lia.
    + apply in_map_iff in ht.
      destruct ht as [a [ha hin]].
      subst t.
      simpl.
      apply (proj1 (Nat.succ_le_mono _ _)).
      exact (IH a hin).
    + map2_rank_bound ht IH.
    + map2_rank_bound ht IH.
Qed.

Lemma term_rank_enum_complete : forall n t,
  term_rank t <= n -> In t (term_rank_enum n).
Proof.
  induction n as [|n IH]; intros t ht.
  - destruct t; simpl in ht; lia.
  - destruct t as [i | | a | a b | a b]; simpl in ht.
    + in_app_pick 0.
      apply in_map_iff.
      exists i.
      split; [reflexivity |].
      apply in_seq. simpl. lia.
    + in_app_pick 1.
      simpl. auto.
    + in_app_pick 2.
      apply in_map_iff.
      exists a.
      split; [reflexivity |].
      apply IH.
      lia.
    + in_app_pick 3.
      map2_member a b ltac:(apply IH; lia).
    + in_app_last 4.
      map2_member a b ltac:(apply IH; lia).
Qed.

Theorem term_rank_enum_spec : forall n t,
  In t (term_rank_enum n) <-> term_rank t <= n.
Proof.
  intros n t.
  split.
  - apply term_rank_enum_sound.
  - apply term_rank_enum_complete.
Qed.

Lemma formula_rank_enum_sound : forall n phi,
  In phi (formula_rank_enum n) -> formula_rank phi <= n.
Proof.
  induction n as [|n IH]; intros phi hphi.
  - simpl in hphi. contradiction.
  - cbn [formula_rank_enum] in hphi.
    repeat rewrite in_app_iff in hphi.
    destruct hphi as
      [hphi | [hphi | [hphi | [hphi | [hphi | [hphi | hphi]]]]]].
    + apply in_list_map2_iff in hphi.
      destruct hphi as [a [b [ha [hb hab]]]].
      subst phi.
      simpl.
      apply (proj1 (Nat.succ_le_mono _ _)).
      apply Nat.max_lub.
      * exact (term_rank_enum_sound n a ha).
      * exact (term_rank_enum_sound n b hb).
    + simpl in hphi.
      destruct hphi as [hphi | []].
      subst phi. simpl. lia.
    + map2_rank_bound hphi IH.
    + map2_rank_bound hphi IH.
    + map2_rank_bound hphi IH.
    + apply in_map_iff in hphi.
      destruct hphi as [a [ha hin]].
      subst phi.
      simpl.
      apply (proj1 (Nat.succ_le_mono _ _)).
      exact (IH a hin).
    + apply in_map_iff in hphi.
      destruct hphi as [a [ha hin]].
      subst phi.
      simpl.
      apply (proj1 (Nat.succ_le_mono _ _)).
      exact (IH a hin).
Qed.

Lemma formula_rank_enum_complete : forall n phi,
  formula_rank phi <= n -> In phi (formula_rank_enum n).
Proof.
  induction n as [|n IH]; intros phi hphi.
  - destruct phi; simpl in hphi; lia.
  - destruct phi as [a b | | a b | a b | a b | a | a]; simpl in hphi.
    + in_app_pick 0.
      map2_member a b ltac:(apply term_rank_enum_complete; lia).
    + in_app_pick 1.
      simpl. auto.
    + in_app_pick 2.
      map2_member a b ltac:(apply IH; lia).
    + in_app_pick 3.
      map2_member a b ltac:(apply IH; lia).
    + in_app_pick 4.
      map2_member a b ltac:(apply IH; lia).
    + in_app_pick 5.
      apply in_map_iff.
      exists a.
      split; [reflexivity |].
      apply IH. lia.
    + in_app_last 6.
      apply in_map_iff.
      exists a.
      split; [reflexivity |].
      apply IH. lia.
Qed.

Theorem formula_rank_enum_spec : forall n phi,
  In phi (formula_rank_enum n) <-> formula_rank phi <= n.
Proof.
  intros n phi.
  split.
  - apply formula_rank_enum_sound.
  - apply formula_rank_enum_complete.
Qed.

(** List-witness formulations make the finiteness statement independent of
    any particular finite-set library. *)
Corollary term_rank_bounded_finite : forall n,
  exists ts : list PA.term,
    forall t, term_rank t <= n <-> In t ts.
Proof.
  intro n.
  exists (term_rank_enum n).
  intro t.
  symmetry.
  apply term_rank_enum_spec.
Qed.

Corollary formula_rank_bounded_finite : forall n,
  exists fs : list PA.formula,
    forall phi, formula_rank phi <= n <-> In phi fs.
Proof.
  intro n.
  exists (formula_rank_enum n).
  intro phi.
  symmetry.
  apply formula_rank_enum_spec.
Qed.

(** A completely raw structure for the first-order language of arithmetic.
    It deliberately imposes no Peano axioms and no meta-level induction
    principle.  This is the right semantic object for countermodels to a
    bounded induction fragment; [PA.Model] is not, because [PA.Model] already
    stores full induction for every meta-level predicate. *)
Record RawPAModel : Type := {
  raw_carrier : Type;
  raw_zero : raw_carrier;
  raw_succ : raw_carrier -> raw_carrier;
  raw_add : raw_carrier -> raw_carrier -> raw_carrier;
  raw_mul : raw_carrier -> raw_carrier -> raw_carrier
}.

Coercion raw_carrier : RawPAModel >-> Sortclass.

Fixpoint raw_term_eval (M : RawPAModel) (e : nat -> M)
    (t : PA.term) : M :=
  match t with
  | PA.tVar n => e n
  | PA.tZero => raw_zero M
  | PA.tSucc a => raw_succ M (raw_term_eval M e a)
  | PA.tAdd a b => raw_add M (raw_term_eval M e a) (raw_term_eval M e b)
  | PA.tMul a b => raw_mul M (raw_term_eval M e a) (raw_term_eval M e b)
  end.

Fixpoint raw_formula_sat (M : RawPAModel) (e : nat -> M)
    (phi : PA.formula) : Prop :=
  match phi with
  | PA.pEq a b => raw_term_eval M e a = raw_term_eval M e b
  | PA.pBot => False
  | PA.pImp a b => raw_formula_sat M e a -> raw_formula_sat M e b
  | PA.pAnd a b => raw_formula_sat M e a /\ raw_formula_sat M e b
  | PA.pOr a b => raw_formula_sat M e a \/ raw_formula_sat M e b
  | PA.pAll a => forall d, raw_formula_sat M (scons M d e) a
  | PA.pEx a => exists d, raw_formula_sat M (scons M d e) a
  end.

Lemma raw_term_eval_ext : forall (M : RawPAModel) t (e e' : nat -> M),
  (forall n, e n = e' n) ->
  raw_term_eval M e t = raw_term_eval M e' t.
Proof.
  intros M t.
  induction t as [n | | a IHa | a IHa b IHb | a IHa b IHb];
    simpl; intros e e' he; try reflexivity.
  - apply he.
  - now rewrite (IHa e e' he).
  - now rewrite (IHa e e' he), (IHb e e' he).
  - now rewrite (IHa e e' he), (IHb e e' he).
Qed.

Lemma raw_term_eval_rename : forall (M : RawPAModel) t r (e : nat -> M),
  raw_term_eval M e (PA.Term.rename r t) =
  raw_term_eval M (fun n => e (r n)) t.
Proof.
  intros M t.
  induction t as [n | | a IHa | a IHa b IHb | a IHa b IHb];
    simpl; intros r e; try reflexivity.
  - now rewrite IHa.
  - now rewrite IHa, IHb.
  - now rewrite IHa, IHb.
Qed.

Lemma raw_term_eval_subst : forall (M : RawPAModel) t sigma (e : nat -> M),
  raw_term_eval M e (PA.Term.subst sigma t) =
  raw_term_eval M (fun n => raw_term_eval M e (sigma n)) t.
Proof.
  intros M t.
  induction t as [n | | a IHa | a IHa b IHb | a IHa b IHb];
    simpl; intros sigma e; try reflexivity.
  - now rewrite IHa.
  - now rewrite IHa, IHb.
  - now rewrite IHa, IHb.
Qed.

Lemma raw_term_eval_upSubst : forall (M : RawPAModel)
    sigma (e : nat -> M) d n,
  raw_term_eval M (scons M d e) (PA.Term.upSubst sigma n) =
  scons M d (fun k => raw_term_eval M e (sigma k)) n.
Proof.
  intros M sigma e d [|n]; simpl.
  - reflexivity.
  - rewrite raw_term_eval_rename.
    apply raw_term_eval_ext.
    intro k. reflexivity.
Qed.

Lemma raw_formula_sat_ext : forall (M : RawPAModel)
    phi (e e' : nat -> M),
  (forall n, e n = e' n) ->
  (raw_formula_sat M e phi <-> raw_formula_sat M e' phi).
Proof.
  intros M phi.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa];
    simpl; intros e e' he.
  - rewrite (raw_term_eval_ext M a e e' he).
    rewrite (raw_term_eval_ext M b e e' he).
    reflexivity.
  - reflexivity.
  - split; intros h ha.
    + apply (proj1 (IHb e e' he)).
      apply h.
      apply (proj2 (IHa e e' he)). exact ha.
    + apply (proj2 (IHb e e' he)).
      apply h.
      apply (proj1 (IHa e e' he)). exact ha.
  - split; intros [ha hb]; split.
    + apply (proj1 (IHa e e' he)). exact ha.
    + apply (proj1 (IHb e e' he)). exact hb.
    + apply (proj2 (IHa e e' he)). exact ha.
    + apply (proj2 (IHb e e' he)). exact hb.
  - split; intros h.
    + destruct h as [ha | hb].
      * left. apply (proj1 (IHa e e' he)). exact ha.
      * right. apply (proj1 (IHb e e' he)). exact hb.
    + destruct h as [ha | hb].
      * left. apply (proj2 (IHa e e' he)). exact ha.
      * right. apply (proj2 (IHb e e' he)). exact hb.
  - split; intros hall d.
    + apply (proj1 (IHa (scons M d e) (scons M d e')
        (fun n => match n with 0 => eq_refl | S k => he k end))).
      exact (hall d).
    + apply (proj2 (IHa (scons M d e) (scons M d e')
        (fun n => match n with 0 => eq_refl | S k => he k end))).
      exact (hall d).
  - split; intros hex.
    + destruct hex as [d hd].
      exists d.
      apply (proj1 (IHa (scons M d e) (scons M d e')
        (fun n => match n with 0 => eq_refl | S k => he k end))).
      exact hd.
    + destruct hex as [d hd].
      exists d.
      apply (proj2 (IHa (scons M d e) (scons M d e')
        (fun n => match n with 0 => eq_refl | S k => he k end))).
      exact hd.
Qed.

Lemma raw_formula_sat_rename : forall (M : RawPAModel)
    phi r (e : nat -> M),
  raw_formula_sat M e (PA.Formula.rename r phi) <->
  raw_formula_sat M (fun n => e (r n)) phi.
Proof.
  intros M phi.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa];
    simpl; intros r e.
  - rewrite !raw_term_eval_rename. reflexivity.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - split; intros hall d.
    + pose proof (proj1 (IHa (up r) (scons M d e)) (hall d)) as h.
      apply (proj1 (raw_formula_sat_ext M a
        (fun n => scons M d e (up r n))
        (scons M d (fun n => e (r n)))
        (fun n => match n with 0 => eq_refl | S _ => eq_refl end))).
      exact h.
    + apply (proj2 (IHa (up r) (scons M d e))).
      apply (proj2 (raw_formula_sat_ext M a
        (fun n => scons M d e (up r n))
        (scons M d (fun n => e (r n)))
        (fun n => match n with 0 => eq_refl | S _ => eq_refl end))).
      exact (hall d).
  - split; intros hex.
    + destruct hex as [d hd].
      exists d.
      pose proof (proj1 (IHa (up r) (scons M d e)) hd) as h.
      apply (proj1 (raw_formula_sat_ext M a
        (fun n => scons M d e (up r n))
        (scons M d (fun n => e (r n)))
        (fun n => match n with 0 => eq_refl | S _ => eq_refl end))).
      exact h.
    + destruct hex as [d hd].
      exists d.
      apply (proj2 (IHa (up r) (scons M d e))).
      apply (proj2 (raw_formula_sat_ext M a
        (fun n => scons M d e (up r n))
        (scons M d (fun n => e (r n)))
        (fun n => match n with 0 => eq_refl | S _ => eq_refl end))).
      exact hd.
Qed.

Lemma raw_formula_sat_subst : forall (M : RawPAModel)
    phi sigma (e : nat -> M),
  raw_formula_sat M e (PA.Formula.subst sigma phi) <->
  raw_formula_sat M (fun n => raw_term_eval M e (sigma n)) phi.
Proof.
  intros M phi.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa];
    simpl; intros sigma e.
  - rewrite !raw_term_eval_subst. reflexivity.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - split; intros hall d.
    + pose proof (proj1 (IHa (PA.Term.upSubst sigma)
        (scons M d e)) (hall d)) as h.
      apply (proj1 (raw_formula_sat_ext M a
        (fun n => raw_term_eval M (scons M d e)
          (PA.Term.upSubst sigma n))
        (scons M d (fun k => raw_term_eval M e (sigma k)))
        (raw_term_eval_upSubst M sigma e d))).
      exact h.
    + apply (proj2 (IHa (PA.Term.upSubst sigma) (scons M d e))).
      apply (proj2 (raw_formula_sat_ext M a
        (fun n => raw_term_eval M (scons M d e)
          (PA.Term.upSubst sigma n))
        (scons M d (fun k => raw_term_eval M e (sigma k)))
        (raw_term_eval_upSubst M sigma e d))).
      exact (hall d).
  - split; intros hex.
    + destruct hex as [d hd].
      exists d.
      pose proof (proj1 (IHa (PA.Term.upSubst sigma)
        (scons M d e)) hd) as h.
      apply (proj1 (raw_formula_sat_ext M a
        (fun n => raw_term_eval M (scons M d e)
          (PA.Term.upSubst sigma n))
        (scons M d (fun k => raw_term_eval M e (sigma k)))
        (raw_term_eval_upSubst M sigma e d))).
      exact h.
    + destruct hex as [d hd].
      exists d.
      apply (proj2 (IHa (PA.Term.upSubst sigma) (scons M d e))).
      apply (proj2 (raw_formula_sat_ext M a
        (fun n => raw_term_eval M (scons M d e)
          (PA.Term.upSubst sigma n))
        (scons M d (fun k => raw_term_eval M e (sigma k)))
        (raw_term_eval_upSubst M sigma e d))).
      exact hd.
Qed.

Lemma raw_formula_sat_instTerm : forall (M : RawPAModel)
    phi t (e : nat -> M),
  raw_formula_sat M e
      (PA.Formula.subst (PA.Formula.instTerm t) phi) <->
  raw_formula_sat M (scons M (raw_term_eval M e t) e) phi.
Proof.
  intros M phi t e.
  eapply iff_trans.
  - apply raw_formula_sat_subst.
  - apply raw_formula_sat_ext.
    intros [|n]; reflexivity.
Qed.

Lemma raw_formula_sat_rename_succ : forall (M : RawPAModel)
    phi (e : nat -> M) d,
  raw_formula_sat M (scons M d e) (PA.Formula.rename S phi) <->
  raw_formula_sat M e phi.
Proof.
  intros M phi e d.
  eapply iff_trans.
  - apply raw_formula_sat_rename.
  - apply raw_formula_sat_ext.
    intro n. reflexivity.
Qed.

(** Natural deduction is sound for every raw PA structure.  The only global
    principle used here is excluded middle, matching [Prov]'s classical
    [P_lem] constructor; no arithmetic law or induction hypothesis occurs. *)
Theorem raw_PA_Prov_soundness : forall (M : RawPAModel) G phi,
  PA.Formula.Prov G phi ->
  forall e : nat -> M,
    (forall psi, In psi G -> raw_formula_sat M e psi) ->
    raw_formula_sat M e phi.
Proof.
  intros M G phi h.
  induction h; intros e hG; simpl.
  - exact (hG a H).
  - intros ha.
    apply IHh.
    intros x hx.
    simpl in hx.
    destruct hx as [hx | hx].
    + subst x. exact ha.
    + exact (hG x hx).
  - exact (IHh1 e hG (IHh2 e hG)).
  - exfalso. exact (IHh e hG).
  - destruct (classic (raw_formula_sat M e a)) as [ha | hna].
    + left. exact ha.
    + right. exact hna.
  - split; [exact (IHh1 e hG) | exact (IHh2 e hG)].
  - exact (proj1 (IHh e hG)).
  - exact (proj2 (IHh e hG)).
  - left. exact (IHh e hG).
  - right. exact (IHh e hG).
  - destruct (IHh1 e hG) as [ha | hb].
    + apply IHh2.
      intros x hx.
      simpl in hx.
      destruct hx as [hx | hx].
      * subst x. exact ha.
      * exact (hG x hx).
    + apply IHh3.
      intros x hx.
      simpl in hx.
      destruct hx as [hx | hx].
      * subst x. exact hb.
      * exact (hG x hx).
  - intros d.
    apply IHh.
    intros x hx.
    apply in_map_iff in hx.
    destruct hx as [g [hg_eq hg]].
    subst x.
    apply (proj2 (raw_formula_sat_rename_succ M g e d)).
    exact (hG g hg).
  - apply (proj2 (raw_formula_sat_instTerm M a t e)).
    exact (IHh e hG (raw_term_eval M e t)).
  - exists (raw_term_eval M e t).
    apply (proj1 (raw_formula_sat_instTerm M a t e)).
    exact (IHh e hG).
  - destruct (IHh1 e hG) as [d hd].
    pose proof (IHh2 (scons M d e)) as hc_shift.
    assert (hctx : forall x,
        In x (a :: map (PA.Formula.rename S) G) ->
        raw_formula_sat M (scons M d e) x).
    {
      intros x hx.
      simpl in hx.
      destruct hx as [hx | hx].
      - subst x. exact hd.
      - apply in_map_iff in hx.
        destruct hx as [g [hg_eq hg]].
        subst x.
        apply (proj2 (raw_formula_sat_rename_succ M g e d)).
        exact (hG g hg).
    }
    apply (proj1 (raw_formula_sat_rename_succ M c e d)).
    exact (hc_shift hctx).
  - reflexivity.
  - pose proof (IHh1 e hG) as heq.
    pose proof (proj1 (raw_formula_sat_instTerm M a s e)
      (IHh2 e hG)) as hs.
    assert (henv : forall n,
        scons M (raw_term_eval M e s) e n =
        scons M (raw_term_eval M e t) e n).
    {
      intros [|n]; simpl.
      - exact heq.
      - reflexivity.
    }
    pose proof (proj1 (raw_formula_sat_ext M a
      (scons M (raw_term_eval M e s) e)
      (scons M (raw_term_eval M e t) e) henv) hs) as ht.
    apply (proj2 (raw_formula_sat_instTerm M a t e)).
    exact ht.
Qed.

(** The finite, non-schematic part of PA's displayed axiom predicate. *)
Definition PABaseAxiom (f : PA.formula) : Prop :=
  f = PA.Formula.sealPA PA.Formula.succInj \/
  f = PA.Formula.sealPA PA.Formula.zeroNotSucc \/
  f = PA.Formula.sealPA PA.Formula.addZero \/
  f = PA.Formula.sealPA PA.Formula.addSucc \/
  f = PA.Formula.sealPA PA.Formula.mulZero \/
  f = PA.Formula.sealPA PA.Formula.mulSucc.

(** The canonical rank-[n] fragment consists of all base axioms and exactly
    the induction instances generated by formulas of rank at most [n]. *)
Definition PARankFragment (n : nat) (f : PA.formula) : Prop :=
  PABaseAxiom f \/
  exists phi : PA.formula,
    formula_rank phi <= n /\
    f = PA.Formula.sealPA (PA.Formula.inductionForm phi).

(** An explicit finite enumeration of the canonical fragment.  Duplicates
    are harmless: membership, rather than list identity, is the finite-set
    interface used throughout this development. *)
Definition PA_base_axiom_enum : list PA.formula :=
  [PA.Formula.sealPA PA.Formula.succInj;
   PA.Formula.sealPA PA.Formula.zeroNotSucc;
   PA.Formula.sealPA PA.Formula.addZero;
   PA.Formula.sealPA PA.Formula.addSucc;
   PA.Formula.sealPA PA.Formula.mulZero;
   PA.Formula.sealPA PA.Formula.mulSucc].

Definition PA_rank_fragment_enum (n : nat) : list PA.formula :=
  PA_base_axiom_enum ++
  map (fun phi =>
    PA.Formula.sealPA (PA.Formula.inductionForm phi))
    (formula_rank_enum n).

Lemma PA_base_axiom_enum_spec : forall f,
  In f PA_base_axiom_enum <-> PABaseAxiom f.
Proof.
  intro f.
  unfold PA_base_axiom_enum, PABaseAxiom.
  simpl.
  intuition congruence.
Qed.

Theorem PA_rank_fragment_enum_spec : forall n f,
  In f (PA_rank_fragment_enum n) <-> PARankFragment n f.
Proof.
  intros n f.
  unfold PA_rank_fragment_enum, PARankFragment.
  rewrite in_app_iff, PA_base_axiom_enum_spec.
  split.
  - intros [hbase | hind].
    + left. exact hbase.
    + right.
      apply in_map_iff in hind.
      destruct hind as [phi [hphi hin]].
      exists phi.
      split.
      * exact (formula_rank_enum_sound n phi hin).
      * symmetry. exact hphi.
  - intros [hbase | [phi [hrank hphi]]].
    + left. exact hbase.
    + right.
      apply in_map_iff.
      exists phi.
      split.
      * symmetry. exact hphi.
      * exact (formula_rank_enum_complete n phi hrank).
Qed.

Corollary PA_rank_fragment_finite : forall n,
  exists fs : list PA.formula,
    forall f, PARankFragment n f <-> In f fs.
Proof.
  intro n.
  exists (PA_rank_fragment_enum n).
  intro f.
  symmetry.
  apply PA_rank_fragment_enum_spec.
Qed.

Lemma PA_base_axiom_is_ax_s : forall f,
  PABaseAxiom f -> PA.Formula.Ax_s f.
Proof.
  intros f hf.
  unfold PABaseAxiom in hf.
  unfold PA.Formula.Ax_s.
  destruct hf as [hf | [hf | [hf | [hf | [hf | hf]]]]].
  - left. exact hf.
  - right. left. exact hf.
  - right. right. left. exact hf.
  - right. right. right. left. exact hf.
  - right. right. right. right. left. exact hf.
  - right. right. right. right. right. left. exact hf.
Qed.

(** Every canonical fragment is literally a subtheory of PA. *)
Lemma PA_rank_fragment_subset_ax_s : forall n f,
  PARankFragment n f -> PA.Formula.Ax_s f.
Proof.
  intros n f [hbase | [phi [_ hf]]].
  - exact (PA_base_axiom_is_ax_s f hbase).
  - unfold PA.Formula.Ax_s.
    right. right. right. right. right. right.
    exists phi. exact hf.
Qed.

Lemma PA_rank_fragment_base : forall n f,
  PABaseAxiom f -> PARankFragment n f.
Proof.
  intros n f hf.
  left. exact hf.
Qed.

Lemma PA_rank_fragment_induction : forall n phi,
  formula_rank phi <= n ->
  PARankFragment n
    (PA.Formula.sealPA (PA.Formula.inductionForm phi)).
Proof.
  intros n phi hrank.
  right. exists phi.
  split; [exact hrank | reflexivity].
Qed.

(** The hierarchy is monotone in its rank bound. *)
Lemma PA_rank_fragment_mono : forall n m f,
  n <= m ->
  PARankFragment n f ->
  PARankFragment m f.
Proof.
  intros n m f hnm [hbase | [phi [hrank hf]]].
  - left. exact hbase.
  - right. exists phi.
    split; [lia | exact hf].
Qed.

(** Each displayed PA axiom occurs at some finite rank. *)
Lemma PA_axiom_bounded_by_rank : forall f,
  PA.Formula.Ax_s f ->
  exists n, PARankFragment n f.
Proof.
  intros f hf.
  unfold PA.Formula.Ax_s in hf.
  destruct hf as
      [hf | [hf | [hf | [hf | [hf | [hf | [phi hf]]]]]]].
  - exists 0. left. unfold PABaseAxiom. left. exact hf.
  - exists 0. left. unfold PABaseAxiom. right. left. exact hf.
  - exists 0. left. unfold PABaseAxiom. right. right. left. exact hf.
  - exists 0. left. unfold PABaseAxiom.
    right. right. right. left. exact hf.
  - exists 0. left. unfold PABaseAxiom.
    right. right. right. right. left. exact hf.
  - exists 0. left. unfold PABaseAxiom.
    right. right. right. right. right. exact hf.
  - exists (formula_rank phi).
    right. exists phi.
    split; [lia | exact hf].
Qed.

(** A single rank bound dominates every member of any finite list of genuine
    PA axioms.  The bound is obtained structurally by taking maxima; no
    decidability or enumeration of formulas is needed. *)
Theorem finite_PA_fragment_bounded_by_rank :
  forall Delta : list PA.formula,
    (forall delta, In delta Delta -> PA.Formula.Ax_s delta) ->
    exists n, forall delta, In delta Delta -> PARankFragment n delta.
Proof.
  intros Delta.
  induction Delta as [|a Delta IH]; intro hDelta.
  - exists 0.
    intros delta hdelta. contradiction.
  - assert (ha : PA.Formula.Ax_s a).
    {
      apply hDelta.
      simpl. left. reflexivity.
    }
    assert (hTail : forall delta,
        In delta Delta -> PA.Formula.Ax_s delta).
    {
      intros delta hdelta.
      apply hDelta.
      simpl. right. exact hdelta.
    }
    destruct (PA_axiom_bounded_by_rank a ha) as [na hna].
    destruct (IH hTail) as [n hn].
    exists (Nat.max na n).
    intros delta hdelta.
    simpl in hdelta.
    destruct hdelta as [hdelta | hdelta].
    + subst delta.
      apply (PA_rank_fragment_mono na (Nat.max na n) a).
      * apply Nat.le_max_l.
      * exact hna.
    + apply (PA_rank_fragment_mono n (Nat.max na n) delta).
      * apply Nat.le_max_r.
      * exact (hn delta hdelta).
Qed.

(** Satisfaction and falsification for arbitrary raw arithmetic structures.
    Validity quantifies over all valuations because the generic soundness
    theorem applies to open formulas as well as sentences. *)
Definition RawModelSatisfies (M : RawPAModel)
    (B : PA.formula -> Prop) : Prop :=
  forall f, B f -> forall e : nat -> M, raw_formula_sat M e f.

Definition RawModelFalsifies (M : RawPAModel) (f : PA.formula) : Prop :=
  exists e : nat -> M, ~ raw_formula_sat M e f.

(** Generic semantic non-derivability: a countermodel to [f] which validates
    every axiom of [B] rules out bounded provability from [B]. *)
Theorem BProv_not_of_raw_countermodel :
  forall (M : RawPAModel) (B : PA.formula -> Prop) f,
    RawModelSatisfies M B ->
    RawModelFalsifies M f ->
    ~ PA.Formula.BProv B [] f.
Proof.
  intros M B f hModel [e hFalse] [L [hL hProv]].
  apply hFalse.
  apply (raw_PA_Prov_soundness M L f).
  - rewrite app_nil_r in hProv.
    exact hProv.
  - intros theta htheta.
    exact (hModel theta (hL theta htheta) e).
Qed.

(** The requested raw-model bridge.  A law-free PA structure validating the
    canonical rank fragment while falsifying a genuine PA axiom provides the
    exact PA-provable sentence separation used by the finite-basis theorem. *)
Theorem PA_rank_fragment_separation_of_raw_countermodel :
  forall (M : RawPAModel) n psi,
    PA.Formula.Ax_s psi ->
    RawModelSatisfies M (PARankFragment n) ->
    RawModelFalsifies M psi ->
    PA.Formula.Sentence psi /\
    PA.Formula.BProv PA.Formula.Ax_s [] psi /\
    ~ PA.Formula.BProv (PARankFragment n) [] psi.
Proof.
  intros M n psi hAx hModel hFalse.
  split.
  - exact (PA.Formula.sentence_ax_s psi hAx).
  - split.
    + exact (PA.Formula.BProv_ax PA.Formula.Ax_s [] psi hAx).
    + exact (BProv_not_of_raw_countermodel M
        (PARankFragment n) psi hModel hFalse).
Qed.

Theorem PA_rank_fragment_misses_induction_of_raw_countermodel :
  forall (M : RawPAModel) n phi,
    RawModelSatisfies M (PARankFragment n) ->
    RawModelFalsifies M
      (PA.Formula.sealPA (PA.Formula.inductionForm phi)) ->
    ~ PA.Formula.BProv (PARankFragment n) []
        (PA.Formula.sealPA (PA.Formula.inductionForm phi)).
Proof.
  intros M n phi hModel hFalse.
  exact (BProv_not_of_raw_countermodel M (PARankFragment n)
    (PA.Formula.sealPA (PA.Formula.inductionForm phi)) hModel hFalse).
Qed.

(** --------------------------------------------------------------------
    The first unconditional hierarchy step: a two-successor-chain model.

    [main_chain 0] is the interpretation of zero.  Successor advances within
    either chain, so [extra_chain 0] has no predecessor.  Addition and
    multiplication are defined by the displayed PA recursions in their second
    argument.  Consequently all six non-induction axioms hold, but induction
    for "zero or a successor" fails at [extra_chain 0]. *)

Inductive TwoChain : Type :=
| main_chain : nat -> TwoChain
| extra_chain : nat -> TwoChain.

Definition two_chain_zero : TwoChain := main_chain 0.

Definition two_chain_succ (x : TwoChain) : TwoChain :=
  match x with
  | main_chain n => main_chain (S n)
  | extra_chain n => extra_chain (S n)
  end.

Fixpoint two_chain_succ_iter (n : nat) (x : TwoChain) : TwoChain :=
  match n with
  | 0 => x
  | S k => two_chain_succ (two_chain_succ_iter k x)
  end.

Definition two_chain_add (x y : TwoChain) : TwoChain :=
  match y with
  | main_chain n => two_chain_succ_iter n x
  | extra_chain n => extra_chain n
  end.

Fixpoint two_chain_mul_iter (x : TwoChain) (n : nat) : TwoChain :=
  match n with
  | 0 => two_chain_zero
  | S k => two_chain_add (two_chain_mul_iter x k) x
  end.

Definition two_chain_mul (x y : TwoChain) : TwoChain :=
  match y with
  | main_chain n => two_chain_mul_iter x n
  | extra_chain n => two_chain_mul_iter x n
  end.

Definition two_chain_raw_model : RawPAModel :=
  {| raw_carrier := TwoChain;
     raw_zero := two_chain_zero;
     raw_succ := two_chain_succ;
     raw_add := two_chain_add;
     raw_mul := two_chain_mul |}.

Lemma raw_formula_sat_closeN_of_valid :
  forall (M : RawPAModel) k phi,
    (forall e : nat -> M, raw_formula_sat M e phi) ->
    forall e : nat -> M,
      raw_formula_sat M e (PA.Formula.closeN k phi).
Proof.
  intros M k.
  induction k as [|k IH]; intros phi hValid e; simpl.
  - exact (hValid e).
  - apply IH.
    intros e' d.
    exact (hValid (scons M d e')).
Qed.

Lemma raw_formula_sat_sealPA_of_valid :
  forall (M : RawPAModel) phi,
    (forall e : nat -> M, raw_formula_sat M e phi) ->
    forall e : nat -> M,
      raw_formula_sat M e (PA.Formula.sealPA phi).
Proof.
  intros M phi hValid e.
  unfold PA.Formula.sealPA.
  exact (raw_formula_sat_closeN_of_valid M
    (PA.Formula.bound phi) phi hValid e).
Qed.

Lemma two_chain_succInj_valid : forall e : nat -> two_chain_raw_model,
  raw_formula_sat two_chain_raw_model e PA.Formula.succInj.
Proof.
  intros e.
  cbn [PA.Formula.succInj raw_formula_sat raw_term_eval
    two_chain_raw_model two_chain_succ].
  intros x y h.
  destruct x as [m | m], y as [n | n];
    inversion h; reflexivity.
Qed.

Lemma two_chain_zeroNotSucc_valid : forall e : nat -> two_chain_raw_model,
  raw_formula_sat two_chain_raw_model e PA.Formula.zeroNotSucc.
Proof.
  intros e.
  cbn [PA.Formula.zeroNotSucc raw_formula_sat raw_term_eval
    two_chain_raw_model two_chain_succ two_chain_zero].
  intros x h.
  destruct x; discriminate.
Qed.

Lemma two_chain_addZero_valid : forall e : nat -> two_chain_raw_model,
  raw_formula_sat two_chain_raw_model e PA.Formula.addZero.
Proof.
  intros e.
  cbn [PA.Formula.addZero raw_formula_sat raw_term_eval
    two_chain_raw_model two_chain_add two_chain_zero
    two_chain_succ_iter].
  intro x. reflexivity.
Qed.

Lemma two_chain_addSucc_valid : forall e : nat -> two_chain_raw_model,
  raw_formula_sat two_chain_raw_model e PA.Formula.addSucc.
Proof.
  intros e.
  cbn [PA.Formula.addSucc raw_formula_sat raw_term_eval
    two_chain_raw_model].
  intros x y.
  destruct y; reflexivity.
Qed.

Lemma two_chain_mulZero_valid : forall e : nat -> two_chain_raw_model,
  raw_formula_sat two_chain_raw_model e PA.Formula.mulZero.
Proof.
  intros e.
  cbn [PA.Formula.mulZero raw_formula_sat raw_term_eval
    two_chain_raw_model two_chain_mul two_chain_mul_iter
    two_chain_zero].
  intro x. reflexivity.
Qed.

Lemma two_chain_mulSucc_valid : forall e : nat -> two_chain_raw_model,
  raw_formula_sat two_chain_raw_model e PA.Formula.mulSucc.
Proof.
  intros e.
  cbn [PA.Formula.mulSucc raw_formula_sat raw_term_eval
    two_chain_raw_model].
  intros x y.
  destruct y; reflexivity.
Qed.

Lemma two_chain_base_axiom_valid : forall f,
  PABaseAxiom f ->
  forall e : nat -> two_chain_raw_model,
    raw_formula_sat two_chain_raw_model e f.
Proof.
  intros f hf.
  unfold PABaseAxiom in hf.
  destruct hf as [hf | [hf | [hf | [hf | [hf | hf]]]]];
    subst f; apply raw_formula_sat_sealPA_of_valid.
  - exact two_chain_succInj_valid.
  - exact two_chain_zeroNotSucc_valid.
  - exact two_chain_addZero_valid.
  - exact two_chain_addSucc_valid.
  - exact two_chain_mulZero_valid.
  - exact two_chain_mulSucc_valid.
Qed.

Lemma formula_rank_positive : forall phi, 0 < formula_rank phi.
Proof.
  intros phi.
  destruct phi; simpl; lia.
Qed.

Lemma PA_rank_zero_fragment_is_base : forall f,
  PARankFragment 0 f -> PABaseAxiom f.
Proof.
  intros f [hbase | [phi [hrank _]]].
  - exact hbase.
  - pose proof (formula_rank_positive phi).
    lia.
Qed.

Lemma two_chain_rank_zero_model :
  RawModelSatisfies two_chain_raw_model (PARankFragment 0).
Proof.
  intros f hf e.
  exact (two_chain_base_axiom_valid f
    (PA_rank_zero_fragment_is_base f hf) e).
Qed.

(** The induction predicate [x = 0 \/ exists y, x = S y].  Under the
    existential binder the original free variable [x] becomes index 1. *)
Definition zero_or_successor_formula : PA.formula :=
  PA.pOr
    (PA.pEq (PA.tVar 0) PA.tZero)
    (PA.pEx (PA.pEq (PA.tVar 1) (PA.tSucc (PA.tVar 0)))).

Lemma two_chain_zero_or_successor_induction_false :
  forall e : nat -> two_chain_raw_model,
    ~ raw_formula_sat two_chain_raw_model e
        (PA.Formula.inductionForm zero_or_successor_formula).
Proof.
  intros e hInd.
  assert (hZero : raw_formula_sat two_chain_raw_model e
      (PA.Formula.subst PA.Formula.substZero
        zero_or_successor_formula)).
  {
    cbn [zero_or_successor_formula PA.Formula.subst
      PA.Term.subst PA.Formula.substZero raw_formula_sat raw_term_eval
      two_chain_raw_model two_chain_zero].
    left. reflexivity.
  }
  assert (hStep : raw_formula_sat two_chain_raw_model e
      (PA.pAll
        (PA.pImp zero_or_successor_formula
          (PA.Formula.subst PA.Formula.substSuccVar
            zero_or_successor_formula)))).
  {
    cbn [zero_or_successor_formula PA.Formula.subst
      PA.Term.subst PA.Formula.substSuccVar raw_formula_sat raw_term_eval
      two_chain_raw_model two_chain_succ].
    intros x _.
    right. exists x. reflexivity.
  }
  unfold PA.Formula.inductionForm in hInd.
  simpl in hInd.
  specialize (hInd (conj hZero hStep) (extra_chain 0)).
  cbn [zero_or_successor_formula raw_formula_sat raw_term_eval
    two_chain_raw_model two_chain_zero two_chain_succ] in hInd.
  destruct hInd as [hZero' | [pred hPred]].
  - discriminate.
  - destruct pred; discriminate.
Qed.

Lemma raw_formula_sat_closeN_false_of_everywhere_false :
  forall (M : RawPAModel) (d0 : M) k phi,
    (forall e : nat -> M, ~ raw_formula_sat M e phi) ->
    forall e : nat -> M,
      ~ raw_formula_sat M e (PA.Formula.closeN k phi).
Proof.
  intros M d0 k.
  induction k as [|k IH]; intros phi hFalse e; simpl.
  - exact (hFalse e).
  - apply (IH (PA.pAll phi)).
    intros e' hAll.
    exact (hFalse (scons M d0 e') (hAll d0)).
Qed.

Lemma raw_formula_sat_sealPA_false_of_everywhere_false :
  forall (M : RawPAModel) (d0 : M) phi,
    (forall e : nat -> M, ~ raw_formula_sat M e phi) ->
    forall e : nat -> M,
      ~ raw_formula_sat M e (PA.Formula.sealPA phi).
Proof.
  intros M d0 phi hFalse e.
  unfold PA.Formula.sealPA.
  exact (raw_formula_sat_closeN_false_of_everywhere_false M d0
    (PA.Formula.bound phi) phi hFalse e).
Qed.

Lemma two_chain_falsifies_zero_or_successor_induction :
  RawModelFalsifies two_chain_raw_model
    (PA.Formula.sealPA
      (PA.Formula.inductionForm zero_or_successor_formula)).
Proof.
  exists (fun _ => main_chain 0).
  exact (raw_formula_sat_sealPA_false_of_everywhere_false
    two_chain_raw_model (main_chain 0)
    (PA.Formula.inductionForm zero_or_successor_formula)
    two_chain_zero_or_successor_induction_false
    (fun _ => main_chain 0)).
Qed.

(** An unconditional first step of the canonical hierarchy. *)
Theorem PA_rank_zero_fragment_misses_zero_or_successor_induction :
  ~ PA.Formula.BProv (PARankFragment 0) []
      (PA.Formula.sealPA
        (PA.Formula.inductionForm zero_or_successor_formula)).
Proof.
  exact (PA_rank_fragment_misses_induction_of_raw_countermodel
    two_chain_raw_model 0 zero_or_successor_formula
    two_chain_rank_zero_model
    two_chain_falsifies_zero_or_successor_induction).
Qed.

Theorem PA_rank_zero_fragment_strict :
  exists phi : PA.formula,
    ~ PA.Formula.BProv (PARankFragment 0) []
        (PA.Formula.sealPA (PA.Formula.inductionForm phi)).
Proof.
  exists zero_or_successor_formula.
  exact PA_rank_zero_fragment_misses_zero_or_successor_induction.
Qed.

Theorem PA_rank_zero_fragment_separation :
  PA.Formula.Sentence
      (PA.Formula.sealPA
        (PA.Formula.inductionForm zero_or_successor_formula)) /\
  PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.sealPA
        (PA.Formula.inductionForm zero_or_successor_formula)) /\
  ~ PA.Formula.BProv (PARankFragment 0) []
      (PA.Formula.sealPA
        (PA.Formula.inductionForm zero_or_successor_formula)).
Proof.
  exact (PA_rank_fragment_separation_of_raw_countermodel
    two_chain_raw_model 0
    (PA.Formula.sealPA
      (PA.Formula.inductionForm zero_or_successor_formula))
    (PA.Formula.Ax_s_induction zero_or_successor_formula)
    two_chain_rank_zero_model
    two_chain_falsifies_zero_or_successor_induction).
Qed.

(** Canonical-hierarchy strictness in its strongest natural form: each rank
    fragment fails to prove some further induction instance. *)
Definition PARankFragmentStrictness : Prop :=
  forall n : nat,
    exists phi : PA.formula,
      ~ PA.Formula.BProv (PARankFragment n) []
          (PA.Formula.sealPA (PA.Formula.inductionForm phi)).

(** A semantic form of the remaining hierarchy theorem.  It isolates the
    future model construction from all proof-theoretic bookkeeping. *)
Definition PARankFragmentRawCountermodelStrictness : Prop :=
  forall n : nat,
    exists (M : RawPAModel) (phi : PA.formula),
      RawModelSatisfies M (PARankFragment n) /\
      RawModelFalsifies M
        (PA.Formula.sealPA (PA.Formula.inductionForm phi)).

Theorem rank_fragment_strictness_of_raw_countermodels :
  PARankFragmentRawCountermodelStrictness ->
  PARankFragmentStrictness.
Proof.
  intros hModels n.
  destruct (hModels n) as [M [phi [hModel hFalse]]].
  exists phi.
  exact (PA_rank_fragment_misses_induction_of_raw_countermodel
    M n phi hModel hFalse).
Qed.

(** Canonical rank-fragment strictness already implies strictness for every
    arbitrary finite list of genuine PA axioms. *)
Theorem induction_fragment_strictness_of_rank_fragment_strictness :
  PARankFragmentStrictness -> PAInductionFragmentStrictness.
Proof.
  intros hStrict Delta hDelta.
  destruct (finite_PA_fragment_bounded_by_rank Delta hDelta) as
      [n hBound].
  destruct (hStrict n) as [phi hNot].
  exists phi.
  intro hProv.
  apply hNot.
  unfold PA.Formula.BProv.
  exists Delta.
  split.
  - exact hBound.
  - rewrite app_nil_r.
    exact hProv.
Qed.

Theorem finite_fragment_strictness_of_rank_fragment_strictness :
  PARankFragmentStrictness -> PAFiniteFragmentStrictness.
Proof.
  intro hStrict.
  apply finite_fragment_strictness_of_induction_fragment_strictness.
  exact (induction_fragment_strictness_of_rank_fragment_strictness hStrict).
Qed.

(** Once strictness is established just for the canonical hierarchy, the
    repository's finite-basis reduction gives the headline theorem. *)
Theorem peano_arithmetic_not_finitely_axiomatizable_of_rank_fragment_strictness :
  PARankFragmentStrictness ->
  ~ DeductivelyFinitelyAxiomatizable PA.Formula.Ax_s.
Proof.
  intro hStrict.
  apply peano_arithmetic_not_finitely_axiomatizable_of_fragment_strictness.
  exact (finite_fragment_strictness_of_rank_fragment_strictness hStrict).
Qed.

End PAHierarchyReduction.
