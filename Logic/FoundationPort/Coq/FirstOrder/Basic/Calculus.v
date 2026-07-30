(**
  A one-sided classical sequent calculus for first-order NNF formulas.

  This begins the port of [Foundation/FirstOrder/Basic/Calculus.lean].  The
  primitive derivation stays in [Type], preserving proof data, and uses the
  duplicate-insensitive generic list inclusion shared by the audited
  one-sided calculus infrastructure.
*)

From Stdlib Require Import Arith.PeanoNat Lists.List Vectors.Fin.
From FoundationModal Require Import GenericAdjunctiveSet GenericCalculus.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition first_order_sequent (L : language) : Type := list (proposition L).

Definition first_order_sequent_shift {L}
    (Gamma : first_order_sequent L) : first_order_sequent L :=
  map semiformula_shift Gamma.

Definition first_order_sequent_language_map {L M}
    (h : language_hom L M) (Gamma : first_order_sequent L) :
    first_order_sequent M :=
  map (semiformula_language_map h) Gamma.

Lemma first_order_sequent_language_map_shift :
  forall L M (h : language_hom L M) (Gamma : first_order_sequent L),
    first_order_sequent_language_map h (first_order_sequent_shift Gamma) =
    first_order_sequent_shift (first_order_sequent_language_map h Gamma).
Proof.
  intros L M h Gamma. induction Gamma as [|p Gamma IH]; simpl.
  - reflexivity.
  - now rewrite semiformula_language_map_shift, IH.
Qed.

Definition first_order_sequent_rewrite {L}
    (f : nat -> syntactic_term L) (Gamma : first_order_sequent L) :
    first_order_sequent L :=
  map (semiformula_rewrite (rew_rewrite f)) Gamma.

Lemma first_order_sequent_rewrite_under_free_shift :
  forall L (f : nat -> syntactic_term L) (Gamma : first_order_sequent L),
    first_order_sequent_rewrite (rew_rewrite_under_free f)
      (first_order_sequent_shift Gamma) =
    first_order_sequent_shift (first_order_sequent_rewrite f Gamma).
Proof.
  intros L f Gamma. induction Gamma as [|p Gamma IH]; simpl.
  - reflexivity.
  - now rewrite semiformula_rewrite_under_free_shift, IH.
Qed.

(** Primitive LK rules.  Contraction includes exchange and weakening because
    [generic_list_subset] is pointwise list inclusion. *)
Inductive first_order_derivation (L : language) :
    first_order_sequent L -> Type :=
| FODIdentity : forall k (r : language_rel L k)
    (v : Fin.t k -> syntactic_term L),
    @first_order_derivation L
      [Semiformula_rel r v; Semiformula_nrel r v]
| FODCut : forall (p : proposition L) Gamma Delta,
    @first_order_derivation L (p :: Gamma) ->
    @first_order_derivation L (semiformula_neg p :: Delta) ->
    @first_order_derivation L (Gamma ++ Delta)
| FODContraction : forall Gamma Delta,
    @first_order_derivation L Gamma ->
    generic_list_subset Gamma Delta ->
    @first_order_derivation L Delta
| FODVerum : @first_order_derivation L [Semiformula_verum 0]
| FODOr : forall (p q : proposition L) Gamma,
    @first_order_derivation L (p :: q :: Gamma) ->
    @first_order_derivation L (Semiformula_or p q :: Gamma)
  | FODAnd : forall (p q : proposition L) Gamma,
    @first_order_derivation L (p :: Gamma) ->
    @first_order_derivation L (q :: Gamma) ->
    @first_order_derivation L (Semiformula_and p q :: Gamma)
| FODAll : forall (p : semiproposition L 1) Gamma,
    @first_order_derivation L
      (@semiformula_free L 0 p :: first_order_sequent_shift Gamma) ->
    @first_order_derivation L (Semiformula_all p :: Gamma)
| FODExists : forall (p : semiproposition L 1)
    (t : syntactic_term L) Gamma,
    @first_order_derivation L
      (semiformula_substitute (fun _ : Fin.t 1 => t) p :: Gamma) ->
    @first_order_derivation L (Semiformula_exists p :: Gamma).

Arguments first_order_derivation L Gamma : clear implicits.
Arguments FODIdentity {L k} _ _.
Arguments FODCut {L p Gamma Delta} _ _.
Arguments FODContraction {L Gamma Delta} _ _.
Arguments FODVerum {L}.
Arguments FODOr {L p q Gamma} _.
Arguments FODAnd {L p q Gamma} _ _.
Arguments FODAll {L p Gamma} _.
Arguments FODExists {L p t Gamma} _.

Fixpoint first_order_derivation_height {L Gamma}
    (d : first_order_derivation L Gamma) : nat :=
  match d with
  | FODIdentity _ _ => 0
  | FODCut dp dn =>
      S (Nat.max (first_order_derivation_height dp)
                 (first_order_derivation_height dn))
  | FODContraction d _ => S (first_order_derivation_height d)
  | FODVerum => 0
  | FODOr d => S (first_order_derivation_height d)
  | FODAnd dp dq =>
      S (Nat.max (first_order_derivation_height dp)
                 (first_order_derivation_height dq))
  | FODAll d => S (first_order_derivation_height d)
  | FODExists d => S (first_order_derivation_height d)
  end.

Definition first_order_derivation_cast {L Gamma Delta}
    (d : first_order_derivation L Gamma) (e : Gamma = Delta) :
    first_order_derivation L Delta :=
  generic_lk_cast (first_order_derivation L) d e.

Lemma first_order_derivation_height_cast :
  forall L Gamma Delta (d : first_order_derivation L Gamma)
         (e : Gamma = Delta),
    first_order_derivation_height (first_order_derivation_cast d e) =
    first_order_derivation_height d.
Proof. intros L Gamma Delta d e; destruct e; reflexivity. Qed.

Definition first_order_derivation_contra {L Gamma Delta}
    (d : first_order_derivation L Gamma)
    (H : generic_list_subset Gamma Delta) :
    first_order_derivation L Delta :=
  FODContraction d H.

Definition first_order_derivation_top {L Gamma}
    (Htop : generic_list_member (Semiformula_verum 0) Gamma) :
    first_order_derivation L Gamma.
Proof.
  apply (FODContraction FODVerum).
  intros p [Hp | Hp].
  - now subst p.
  - contradiction.
Defined.

Definition first_order_derivation_atomic_identity {L k}
    (r : language_rel L k) (v : Fin.t k -> syntactic_term L)
    (Gamma : first_order_sequent L)
    (Hpos : generic_list_member (Semiformula_rel r v) Gamma)
    (Hneg : generic_list_member (Semiformula_nrel r v) Gamma) :
    first_order_derivation L Gamma.
Proof.
  apply (FODContraction (FODIdentity r v)).
  intros p [Hp | [Hp | Hp]].
  - now subst p.
  - now subst p.
  - contradiction.
Defined.

Definition first_order_derivation_rotate {L p Gamma}
    (d : first_order_derivation L (p :: Gamma)) :
    first_order_derivation L (Gamma ++ [p]) :=
  FODContraction d (@generic_list_subset_rotate _ p Gamma).

Definition first_order_derivation_tensor {L p q Gamma Delta}
    (dp : first_order_derivation L (p :: Gamma))
    (dq : first_order_derivation L (q :: Delta)) :
    first_order_derivation L
      (Semiformula_and p q :: Gamma ++ Delta) :=
  FODAnd
    (FODContraction dp
      (@generic_list_subset_cons_append_right _ p Gamma Delta))
    (FODContraction dq
      (@generic_list_subset_cons_append_left _ q Gamma Delta)).

(** Every derivation is functorial in the underlying first-order language. *)
Fixpoint first_order_derivation_language_map {L M Gamma}
    (h : language_hom L M) (d : first_order_derivation L Gamma) {struct d} :
    first_order_derivation M (first_order_sequent_language_map h Gamma).
Proof.
  destruct d as [k r v | p Gamma Delta dp dn | Gamma Delta d Hsub |
    | p q Gamma d | p q Gamma dp dq | p Gamma d | p t Gamma d].
  - exact (FODIdentity (hom_rel h r)
      (fun i => semiterm_language_map h (v i))).
  - pose (dp' := @first_order_derivation_language_map L M _ h dp).
    pose (dn' := @first_order_derivation_language_map L M _ h dn).
    refine (first_order_derivation_cast
      (FODCut dp'
        (first_order_derivation_cast dn' _)) _).
    + simpl. now rewrite semiformula_language_map_neg.
    + unfold first_order_sequent_language_map. simpl.
      now rewrite List.map_app.
  - apply (FODContraction (@first_order_derivation_language_map L M _ h d)).
    now apply generic_list_map_subset.
  - exact FODVerum.
  - exact (FODOr (@first_order_derivation_language_map L M _ h d)).
  - exact (FODAnd (@first_order_derivation_language_map L M _ h dp)
                  (@first_order_derivation_language_map L M _ h dq)).
  - apply FODAll.
    refine (first_order_derivation_cast
      (@first_order_derivation_language_map L M _ h d) _).
    simpl. rewrite semiformula_language_map_free.
    now rewrite first_order_sequent_language_map_shift.
  - apply (FODExists (t := semiterm_language_map h t)).
    refine (first_order_derivation_cast
      (@first_order_derivation_language_map L M _ h d) _).
    simpl. now rewrite semiformula_language_map_substitute.
Defined.

(** Simultaneously rewrite every free variable occurring in a derivation. *)
Fixpoint first_order_derivation_rewrite {L Gamma}
    (f : nat -> syntactic_term L) (d : first_order_derivation L Gamma)
    {struct d} :
    first_order_derivation L (first_order_sequent_rewrite f Gamma).
Proof.
  destruct d as [k r v | p Gamma Delta dp dn | Gamma Delta d Hsub |
    | p q Gamma d | p q Gamma dp dq | p Gamma d | p t Gamma d].
  - exact (FODIdentity r
      (fun i => rew_apply (rew_rewrite f) (v i))).
  - pose (dp' := @first_order_derivation_rewrite L _ f dp).
    pose (dn' := @first_order_derivation_rewrite L _ f dn).
    refine (first_order_derivation_cast
      (FODCut dp'
        (first_order_derivation_cast dn' _)) _).
    + simpl. now rewrite semiformula_rewrite_neg.
    + unfold first_order_sequent_rewrite. simpl.
      now rewrite List.map_app.
  - apply (FODContraction (@first_order_derivation_rewrite L _ f d)).
    now apply generic_list_map_subset.
  - exact FODVerum.
  - exact (FODOr (@first_order_derivation_rewrite L _ f d)).
  - exact (FODAnd (@first_order_derivation_rewrite L _ f dp)
                  (@first_order_derivation_rewrite L _ f dq)).
  - apply FODAll.
    refine (first_order_derivation_cast
      (@first_order_derivation_rewrite L _
        (rew_rewrite_under_free f) d) _).
    simpl. rewrite semiformula_rewrite_under_free_free.
    now rewrite first_order_sequent_rewrite_under_free_shift.
  - apply (FODExists
      (t := rew_apply (rew_rewrite f) t)).
    refine (first_order_derivation_cast
      (@first_order_derivation_rewrite L _ f d) _).
    simpl. now rewrite semiformula_rewrite_substitute_one.
Defined.

Definition first_order_derivation_map {L Gamma}
    (d : first_order_derivation L Gamma) (f : nat -> nat) :
    first_order_derivation L
      (first_order_sequent_rewrite
        (fun x => Semiterm_fvar (f x)) Gamma) :=
  first_order_derivation_rewrite (fun x => Semiterm_fvar (f x)) d.

Definition first_order_derivation_shift {L Gamma}
    (d : first_order_derivation L Gamma) :
    first_order_derivation L (first_order_sequent_shift Gamma) :=
  first_order_derivation_rewrite (fun x => Semiterm_fvar (S x)) d.

Definition first_order_fresh_map (m x : nat) : nat :=
  if Nat.eq_dec x m then 0 else S x.

Lemma semiformula_rewrite_map_substitute_fresh :
  forall L (p : semiproposition L 1) m,
    ~ semiformula_free_occurs m p ->
    semiformula_rewrite
      (rew_rewrite
        (fun x => Semiterm_fvar (first_order_fresh_map m x)))
      (semiformula_substitute
        (fun _ : Fin.t 1 => Semiterm_fvar m) p) =
    @semiformula_free L 0 p.
Proof.
  intros L p m Hfresh.
  unfold semiformula_substitute, semiformula_free.
  rewrite <- semiformula_rewrite_comp.
  apply semiformula_rewrite_ext_on_free.
  - intro i. assert (Hi : i = Fin.F1) by apply fin_one_eq_f1.
    subst i. cbn. unfold first_order_fresh_map.
    destruct (Nat.eq_dec m m); [reflexivity | contradiction].
  - intros x Hx. cbn.
    assert (Hxm : x <> m).
    { intro Heq. subst x. exact (Hfresh Hx). }
    unfold first_order_fresh_map.
    destruct (Nat.eq_dec x m); [contradiction | reflexivity].
Qed.

Lemma semiformula_rewrite_map_fresh_eq_shift :
  forall L (p : proposition L) m,
    ~ semiformula_free_occurs m p ->
    semiformula_rewrite
      (rew_rewrite
        (fun x => Semiterm_fvar (first_order_fresh_map m x))) p =
    semiformula_shift p.
Proof.
  intros L p m Hfresh. unfold semiformula_shift.
  apply semiformula_rewrite_ext_on_free.
  - intro i. exact (Fin.case0 (fun _ => _ = _) i).
  - intros x Hx. cbn.
    assert (Hxm : x <> m).
    { intro Heq. subst x. exact (Hfresh Hx). }
    unfold first_order_fresh_map.
    destruct (Nat.eq_dec x m); [contradiction | reflexivity].
Qed.

Lemma first_order_sequent_rewrite_map_fresh_eq_shift :
  forall L (Gamma : first_order_sequent L) m,
    (forall p, In p Gamma -> ~ semiformula_free_occurs m p) ->
    first_order_sequent_rewrite
      (fun x => Semiterm_fvar (first_order_fresh_map m x)) Gamma =
    first_order_sequent_shift Gamma.
Proof.
  intros L Gamma. induction Gamma as [|p Gamma IH]; intros m Hfresh; simpl.
  - reflexivity.
  - f_equal.
    + apply semiformula_rewrite_map_fresh_eq_shift.
      apply Hfresh. now left.
    + apply IH. intros q Hq. apply Hfresh. now right.
Qed.

(** Universal introduction from an instance at a genuinely fresh free
    variable.  No decidable equality on formulas or language symbols is
    required. *)
Definition first_order_derivation_generalize_fresh {L p m Gamma}
    (Hp : ~ semiformula_free_occurs m p)
    (HGamma : forall q, In q Gamma -> ~ semiformula_free_occurs m q)
    (d : first_order_derivation L
      (semiformula_substitute
        (fun _ : Fin.t 1 => Semiterm_fvar m) p :: Gamma)) :
    first_order_derivation L (Semiformula_all p :: Gamma).
Proof.
  apply FODAll.
  refine (first_order_derivation_cast
    (first_order_derivation_map d (first_order_fresh_map m)) _).
  simpl. f_equal.
  - apply semiformula_rewrite_map_substitute_fresh. exact Hp.
  - apply first_order_sequent_rewrite_map_fresh_eq_shift. exact HGamma.
Defined.

Definition first_order_sequent_new_variable {L}
    (Gamma : first_order_sequent L) : nat :=
  list_nat_max (map semiformula_fv_sup Gamma).

Lemma first_order_sequent_fv_sup_le_new_variable :
  forall L (Gamma : first_order_sequent L) p,
    In p Gamma ->
    semiformula_fv_sup p <= first_order_sequent_new_variable Gamma.
Proof.
  intros L Gamma p Hp. unfold first_order_sequent_new_variable.
  apply in_list_nat_max. now apply in_map.
Qed.

Lemma first_order_sequent_new_variable_fresh :
  forall L (Gamma : first_order_sequent L) p,
    In p Gamma ->
    ~ semiformula_free_occurs
      (first_order_sequent_new_variable Gamma) p.
Proof.
  intros L Gamma p Hp.
  apply semiformula_no_free_occurs_above_fv_sup.
  now apply first_order_sequent_fv_sup_le_new_variable.
Qed.

Lemma generic_list_member_of_list_in :
  forall (A : Type) (x : A) xs,
    In x xs -> generic_list_member x xs.
Proof.
  intros A x xs. induction xs as [|y ys IH]; simpl; [tauto |].
  intros [Hxy | Hx].
  - now left.
  - right. now apply IH.
Qed.

Definition first_order_derivation_all_new_variable {L p Gamma}
    (Hall : In (Semiformula_all p) Gamma)
    (d : first_order_derivation L
      (semiformula_substitute
        (fun _ : Fin.t 1 =>
          Semiterm_fvar (first_order_sequent_new_variable Gamma)) p
       :: Gamma)) :
    first_order_derivation L Gamma.
Proof.
  pose (m := first_order_sequent_new_variable Gamma).
  assert (Hp : ~ semiformula_free_occurs m p).
  { intro Hocc.
    apply (first_order_sequent_new_variable_fresh Hall).
    exact Hocc. }
  assert (HGamma : forall q, In q Gamma ->
      ~ semiformula_free_occurs m q).
  { intros q Hq. apply first_order_sequent_new_variable_fresh. exact Hq. }
  pose (dgeneral := first_order_derivation_generalize_fresh
    (m := m) (p := p) (Gamma := Gamma) Hp HGamma d).
  apply (FODContraction dgeneral). intros q [Hq | Hq].
  - subst q. now apply generic_list_member_of_list_in.
  - exact Hq.
Defined.

Lemma generic_list_subset_contract_head :
  forall (A : Type) (x : A) (xs : list A),
    generic_list_subset (x :: x :: xs) (x :: xs).
Proof.
  intros A x xs y [Hy | [Hy | Hy]].
  - now left.
  - now left.
  - now right.
Qed.

Lemma generic_list_subset_weaken_head :
  forall (A : Type) (x : A) (xs : list A),
    generic_list_subset xs (x :: xs).
Proof. intros A x xs y Hy. now right. Qed.

Fixpoint first_order_derivation_exists_of_instances {L}
    (ts : list (syntactic_term L)) (p : semiproposition L 1)
    (Gamma : first_order_sequent L)
    (d : first_order_derivation L
      (map (fun t => semiformula_substitute
        (fun _ : Fin.t 1 => t) p) ts ++ Gamma)) {struct ts} :
    first_order_derivation L (Semiformula_exists p :: Gamma).
Proof.
  destruct ts as [|t ts].
  - simpl in d. apply (FODContraction d).
    apply generic_list_subset_weaken_head.
  - simpl in d.
    pose (dexists := FODExists d).
    pose (drotated := FODContraction dexists
      (@generic_list_subset_rotate_across _
        (Semiformula_exists p)
        (map (fun u => semiformula_substitute
          (fun _ : Fin.t 1 => u) p) ts) Gamma)).
    pose (drest := @first_order_derivation_exists_of_instances L
      ts p (Semiformula_exists p :: Gamma) drotated).
    exact (FODContraction drest
      (@generic_list_subset_contract_head _
        (Semiformula_exists p) Gamma)).
Defined.

Definition first_order_derivation_exists_of_instances_present {L}
    (ts : list (syntactic_term L)) (p : semiproposition L 1)
    (Gamma : first_order_sequent L)
    (d : first_order_derivation L
      (Semiformula_exists p ::
       map (fun t => semiformula_substitute
         (fun _ : Fin.t 1 => t) p) ts ++ Gamma)) :
    first_order_derivation L (Semiformula_exists p :: Gamma).
Proof.
  pose (drotated := FODContraction d
    (@generic_list_subset_rotate_across _
      (Semiformula_exists p)
      (map (fun t => semiformula_substitute
        (fun _ : Fin.t 1 => t) p) ts) Gamma)).
  pose (dall := @first_order_derivation_exists_of_instances L
    ts p (Semiformula_exists p :: Gamma) drotated).
  exact (FODContraction dall
    (@generic_list_subset_contract_head _
      (Semiformula_exists p) Gamma)).
Defined.

Lemma first_order_derivation_height_identity :
  forall L k (r : language_rel L k) v,
    first_order_derivation_height (FODIdentity r v) = 0.
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_cut :
  forall L p Gamma Delta
         (dp : first_order_derivation L (p :: Gamma))
         (dn : first_order_derivation L (semiformula_neg p :: Delta)),
    first_order_derivation_height (FODCut dp dn) =
    S (Nat.max (first_order_derivation_height dp)
               (first_order_derivation_height dn)).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_contraction :
  forall L Gamma Delta (d : first_order_derivation L Gamma) H,
    first_order_derivation_height (@FODContraction L Gamma Delta d H) =
    S (first_order_derivation_height d).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_or :
  forall L p q Gamma (d : first_order_derivation L (p :: q :: Gamma)),
    first_order_derivation_height (FODOr d) =
    S (first_order_derivation_height d).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_and :
  forall L p q Gamma
         (dp : first_order_derivation L (p :: Gamma))
         (dq : first_order_derivation L (q :: Gamma)),
    first_order_derivation_height (FODAnd dp dq) =
    S (Nat.max (first_order_derivation_height dp)
               (first_order_derivation_height dq)).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_all :
  forall L (p : semiproposition L 1) Gamma
         (d : first_order_derivation L
           (@semiformula_free L 0 p :: first_order_sequent_shift Gamma)),
    first_order_derivation_height (FODAll d) =
    S (first_order_derivation_height d).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_exists :
  forall L (p : semiproposition L 1) t Gamma
         (d : first_order_derivation L
           (semiformula_substitute (fun _ : Fin.t 1 => t) p :: Gamma)),
    first_order_derivation_height (FODExists d) =
    S (first_order_derivation_height d).
Proof. reflexivity. Qed.
