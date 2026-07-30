(**
  Term-bounded functions and their closure laws.

  This begins the port of
  [Foundation/FirstOrder/Arithmetic/Definability/BoundedDefinable.lean].
  The comparison relation and structure are explicit, and a bound carries its
  witnessing term in [Type].  Composition therefore avoids the source's
  noncomputable extraction of a finite family of existential witnesses.
*)

From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic Require Import Operator Definability.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics RewriteClosure OperatorSemantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc Hierarchy Monotone.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Basic.
From Foundation.FirstOrder.Arithmetic.Definability Require Import
  Hierarchy Definable.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record arithmetic_bounded_function {M : Type} {k}
    (Str : first_order_structure oring_language M)
    (le : M -> M -> Prop) (f : (Fin.t k -> M) -> M) : Type := {
  arithmetic_bounded_term : semiterm oring_language M k;
  arithmetic_bounded_spec : forall v,
    le (f v) (semiterm_val Str v (fun x => x) arithmetic_bounded_term)
}.

Arguments arithmetic_bounded_term {M k Str le f} _.
Arguments arithmetic_bounded_spec {M k Str le f} _ _.

Definition arithmetic_bounded_function_one {M : Type}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (f : M -> M) : Type :=
  arithmetic_bounded_function Str le
    (fun v : Fin.t 1 -> M => f (v Fin.F1)).

Definition arithmetic_bounded_function_two {M : Type}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (f : M -> M -> M) : Type :=
  arithmetic_bounded_function Str le
    (fun v : Fin.t 2 -> M => f (v Fin.F1) (v (Fin.FS Fin.F1))).

Definition arithmetic_bounded_function_three {M : Type}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (f : M -> M -> M -> M) : Type :=
  arithmetic_bounded_function Str le
    (fun v : Fin.t 3 -> M => f (v Fin.F1) (v (Fin.FS Fin.F1))
      (v (Fin.FS (Fin.FS Fin.F1)))).

Definition arithmetic_bounded_variable {M : Type} {k}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (Hrefl : forall x, le x x) (i : Fin.t k) :
    arithmetic_bounded_function Str le (fun v => v i).
Proof.
  refine {| arithmetic_bounded_term := Semiterm_bvar i |}.
  intro v. apply Hrefl.
Defined.

Definition arithmetic_bounded_constant {M : Type} {k}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (Hrefl : forall x, le x x) (c : M) :
    arithmetic_bounded_function Str le (fun _ : Fin.t k -> M => c).
Proof.
  refine {| arithmetic_bounded_term := Semiterm_fvar c |}.
  intro v. apply Hrefl.
Defined.

Definition arithmetic_bounded_term_function {M : Type} {k}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (Hrefl : forall x, le x x) (t : semiterm oring_language M k) :
    arithmetic_bounded_function Str le
      (fun v => semiterm_val Str v (fun x => x) t).
Proof.
  refine {| arithmetic_bounded_term := t |}.
  intro v. apply Hrefl.
Defined.

(** Exact bound-term substitution is the common core of retraction and
    composition. *)
Definition arithmetic_bounded_substitute_bound {M : Type} {k m}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    {f : (Fin.t k -> M) -> M}
    (Hf : arithmetic_bounded_function Str le f)
    (t : Fin.t k -> semiterm oring_language M m) :
    arithmetic_bounded_function Str le
      (fun v : Fin.t m -> M =>
        f (fun i => semiterm_val Str v (fun x => x) (t i))).
Proof.
  refine {| arithmetic_bounded_term :=
    rew_apply (rew_subst t) (arithmetic_bounded_term Hf) |}.
  intro v. rewrite semiterm_val_substitute.
  apply arithmetic_bounded_spec.
Defined.

Definition arithmetic_bounded_retraction {M : Type} {k m}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    {f : (Fin.t k -> M) -> M}
    (Hf : arithmetic_bounded_function Str le f) (e : Fin.t k -> Fin.t m) :
    arithmetic_bounded_function Str le
      (fun v : Fin.t m -> M => f (fun i => v (e i))).
Proof.
  exact (arithmetic_bounded_substitute_bound Hf
    (fun i => @Semiterm_bvar oring_language M m (e i))).
Defined.

Definition arithmetic_bounded_term_retraction {M : Type} {k m}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (Hrefl : forall x, le x x) (t : semiterm oring_language M k)
    (e : Fin.t k -> Fin.t m) :
    arithmetic_bounded_function Str le
      (fun v : Fin.t m -> M =>
        semiterm_val Str (fun i => v (e i)) (fun x => x) t) :=
  arithmetic_bounded_retraction
    (arithmetic_bounded_term_function Str (le := le) Hrefl t) e.

(** Composition only needs reflexivity and transitivity of the comparison and
    pointwise monotonicity of interpreted function symbols. *)
Definition arithmetic_bounded_compose {M : Type} {k l}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    (Hrefl : forall x, le x x)
    (Htrans : forall x y z, le x y -> le y z -> le x z)
    (Hmon : first_order_structure_monotone le Str)
    {f : (Fin.t l -> M) -> M} {g : Fin.t l -> (Fin.t k -> M) -> M}
    (Hf : arithmetic_bounded_function Str le f)
    (Hg : forall i, arithmetic_bounded_function Str le (g i)) :
    arithmetic_bounded_function Str le (fun v => f (fun i => g i v)).
Proof.
  refine {| arithmetic_bounded_term :=
    rew_apply (rew_subst (fun i => arithmetic_bounded_term (Hg i)))
      (arithmetic_bounded_term Hf) |}.
  intro v. eapply Htrans.
  - apply (arithmetic_bounded_spec Hf (fun i => g i v)).
  - rewrite semiterm_val_substitute.
    apply (semiterm_val_monotone_bound Hmon Hrefl).
    intro i. apply (arithmetic_bounded_spec (Hg i) v).
Defined.

Definition arithmetic_bounded_compose_one {M : Type} {k}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    (Hrefl : forall x, le x x)
    (Htrans : forall x y z, le x y -> le y z -> le x z)
    (Hmon : first_order_structure_monotone le Str)
    {f : M -> M} {g : (Fin.t k -> M) -> M}
    (Hf : arithmetic_bounded_function_one Str le f)
    (Hg : arithmetic_bounded_function Str le g) :
    arithmetic_bounded_function Str le (fun v => f (g v)).
Proof.
  apply (arithmetic_bounded_compose Hrefl Htrans Hmon Hf
    (g := fun _ => g)).
  intro i. exact Hg.
Defined.

Definition arithmetic_bounded_compose_two {M : Type} {k}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    (Hrefl : forall x, le x x)
    (Htrans : forall x y z, le x y -> le y z -> le x z)
    (Hmon : first_order_structure_monotone le Str)
    {f : M -> M -> M} {g h : (Fin.t k -> M) -> M}
    (Hf : arithmetic_bounded_function_two Str le f)
    (Hg : arithmetic_bounded_function Str le g)
    (Hh : arithmetic_bounded_function Str le h) :
    arithmetic_bounded_function Str le (fun v => f (g v) (h v)).
Proof.
  apply (arithmetic_bounded_compose Hrefl Htrans Hmon Hf
    (g := fin_two g h)).
  intro i. refine (@Fin.caseS' 1 i
    (fun j => arithmetic_bounded_function Str le (fin_two g h j)) Hg _).
  intro j. refine (@Fin.caseS' 0 j
    (fun q => arithmetic_bounded_function Str le (fin_two g h (Fin.FS q)))
    Hh _).
  intros q; inversion q.
Defined.

Definition fin_graph_reindex {k m} (e : Fin.t k -> Fin.t m) :
    Fin.t (S k) -> Fin.t (S m) :=
  fun i => @Fin.caseS' k i (fun _ => Fin.t (S m))
    Fin.F1 (fun j => Fin.FS (e j)).

Lemma fin_graph_reindex_zero : forall k m (e : Fin.t k -> Fin.t m),
  fin_graph_reindex e Fin.F1 = Fin.F1.
Proof. reflexivity. Qed.

Lemma fin_graph_reindex_succ : forall k m (e : Fin.t k -> Fin.t m) i,
  fin_graph_reindex e (Fin.FS i) = Fin.FS (e i).
Proof. reflexivity. Qed.

Record arithmetic_definably_bounded_function {M : Type} {k}
    (Str : first_order_structure oring_language M)
    (le : M -> M -> Prop) (f : (Fin.t k -> M) -> M) : Type := {
  arithmetic_definably_bounded_bound :
    arithmetic_bounded_function Str le f;
  arithmetic_definably_bounded_definition :
    arithmetic_sorted_definable_function Str arithmetic_sigma_zero_symbol f
}.

Definition arithmetic_interpreted_lt {M : Type}
    (Str : first_order_structure oring_language M) (x y : M) : Prop :=
  semiformula_operator_eval Str (fin_two x y)
    (semiformula_lt_operator arithmetic_lt_operator).

Definition arithmetic_definably_bounded_variable {M : Type} {k}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (Hrefl : forall x, le x x)
    (HEq : structure_interprets_eq Str arithmetic_eq_operator)
    (i : Fin.t k) :
    arithmetic_definably_bounded_function Str le (fun v => v i) :=
  {| arithmetic_definably_bounded_bound :=
      arithmetic_bounded_variable Str (le := le) Hrefl i;
     arithmetic_definably_bounded_definition :=
      arithmetic_sorted_definable_projection (Str := Str) HEq
        arithmetic_sigma_zero_symbol i |}.

Definition arithmetic_definably_bounded_constant {M : Type} {k}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (Hrefl : forall x, le x x)
    (HEq : structure_interprets_eq Str arithmetic_eq_operator)
    (c : M) :
    arithmetic_definably_bounded_function Str le
      (fun _ : Fin.t k -> M => c) :=
  {| arithmetic_definably_bounded_bound :=
      arithmetic_bounded_constant Str (le := le) Hrefl c;
     arithmetic_definably_bounded_definition :=
      arithmetic_sorted_definable_parameter_constant (Str := Str) HEq
        arithmetic_sigma_zero_symbol c |}.

Definition arithmetic_definably_bounded_term {M : Type} {k}
    (Str : first_order_structure oring_language M) (le : M -> M -> Prop)
    (Hrefl : forall x, le x x)
    (HEq : structure_interprets_eq Str arithmetic_eq_operator)
    (t : semiterm oring_language M k) :
    arithmetic_definably_bounded_function Str le
      (fun v => semiterm_val Str v (fun x => x) t) :=
  {| arithmetic_definably_bounded_bound :=
      arithmetic_bounded_term_function Str (le := le) Hrefl t;
     arithmetic_definably_bounded_definition :=
      arithmetic_sorted_definable_term_graph (Str := Str) HEq
        arithmetic_sigma_zero_symbol t |}.

Definition arithmetic_bounded_of_pointwise_eq {M : Type} {k}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    {f g : (Fin.t k -> M) -> M}
    (Hf : arithmetic_bounded_function Str le f)
    (Hfg : forall v, f v = g v) : arithmetic_bounded_function Str le g.
Proof.
  refine {| arithmetic_bounded_term := arithmetic_bounded_term Hf |}.
  intro v. rewrite <- Hfg. apply arithmetic_bounded_spec.
Defined.

Definition arithmetic_definably_bounded_of_pointwise_eq {M : Type} {k}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    {f g : (Fin.t k -> M) -> M}
    (Hf : arithmetic_definably_bounded_function Str le f)
    (Hfg : forall v, f v = g v) :
    arithmetic_definably_bounded_function Str le g.
Proof.
  destruct Hf as [Hbound Hdef]. constructor.
  - exact (arithmetic_bounded_of_pointwise_eq Hbound Hfg).
  - apply (arithmetic_sorted_definable_of_iff Hdef).
    intro w. rewrite <- (Hfg (fun i => w (Fin.FS i))). reflexivity.
Defined.

Definition arithmetic_definably_bounded_retraction {M : Type} {k m}
    {Str : first_order_structure oring_language M} {le : M -> M -> Prop}
    {f : (Fin.t k -> M) -> M}
    (Hf : arithmetic_definably_bounded_function Str le f)
    (e : Fin.t k -> Fin.t m) :
    arithmetic_definably_bounded_function Str le
      (fun v : Fin.t m -> M => f (fun i => v (e i))).
Proof.
  destruct Hf as [Hbound Hdef]. constructor.
  - exact (arithmetic_bounded_retraction Hbound e).
  - apply (arithmetic_sorted_definable_of_iff
      (arithmetic_sorted_definable_retraction Hdef (fin_graph_reindex e))).
    intro v. reflexivity.
Defined.

(** A single bounded graph witness is the common core of level-zero
    substitution.  Stating the majorant with the interpreted strict order
    makes the exact assumption used by the bounded existential constructor
    explicit; no ambient arithmetic model laws are needed. *)
Definition arithmetic_sorted_definable_substitution_one_strictly_bounded
    {M : Type} {k symbol}
    {Str : first_order_structure oring_language M}
    (P : (Fin.t k -> M) -> M -> Prop)
    (f : (Fin.t k -> M) -> M)
    (Hf : arithmetic_definably_bounded_function Str
      (arithmetic_interpreted_lt Str) f)
    (HP : arithmetic_sorted_definable Str symbol
      (fun w : Fin.t (S k) -> M =>
        P (fun i => w (Fin.FS i)) (w Fin.F1))) :
    arithmetic_sorted_definable Str symbol
      (fun v : Fin.t k -> M => P v (f v)).
Proof.
  destruct Hf as [Hbound Hgraph].
  pose proof (arithmetic_sorted_definable_of_zero Hgraph symbol)
    as Hgraph_at_symbol.
  pose proof (arithmetic_sorted_definable_and Hgraph_at_symbol HP)
    as Hbody.
  pose proof (arithmetic_sorted_definable_bex
    (R := fun v x => x = f v /\ P v x) Hbody
    (arithmetic_bounded_term Hbound)) as Hexists.
  apply (arithmetic_sorted_definable_of_iff Hexists).
  intro v. split.
  - intro HPf. exists (f v). split.
    + exact (arithmetic_bounded_spec Hbound v).
    + split; [reflexivity | exact HPf].
  - intros [x [_ [Hxf HPx]]]. now rewrite Hxf in HPx.
Defined.

(** Iterated bounded existential closure for a finite family of terms.  The
    terms depend only on the external suffix; after eliminating the head
    variable its bound is lifted across the still-free tail prefix. *)
Fixpoint arithmetic_sorted_definable_bex_vector_terms
    (n : nat) {M : Type} {k symbol}
    {Str : first_order_structure oring_language M}
    (t : Fin.t n -> semiterm oring_language M k)
    (Q : (Fin.t (n + k) -> M) -> Prop)
    (HQ : arithmetic_sorted_definable Str symbol Q) {struct n} :
    arithmetic_sorted_definable Str symbol
      (fun z : Fin.t k -> M => exists e : Fin.t n -> M,
        (forall i, arithmetic_interpreted_lt Str (e i)
          (semiterm_val Str z (fun x => x) (t i))) /\
        Q (fin_env_append n k e z)).
Proof.
  destruct n as [| n].
  - apply (arithmetic_sorted_definable_of_iff HQ).
    intro z. split.
    + intros [e [_ HQz]]. exact HQz.
    + intro HQz. exists (fun i : Fin.t 0 => match i with end).
      split.
      * intros i. inversion i.
      * exact HQz.
  - set (t0 := rew_apply
      (rew_map (Fin.R n) (fun x : M => x)) (t Fin.F1)).
    assert (HQ_normalized : arithmetic_sorted_definable Str symbol
      (fun w => Q (fin_env_cons (w Fin.F1)
        (fun i => w (Fin.FS i))))).
    { apply (arithmetic_sorted_definable_of_iff HQ).
      intro w. rewrite fin_env_cons_eta. reflexivity. }
    pose proof (arithmetic_sorted_definable_bex
      (R := fun w : Fin.t (n + k) -> M => fun x : M =>
        Q (fin_env_cons x w)) HQ_normalized t0) as Hhead.
    pose proof (@arithmetic_sorted_definable_bex_vector_terms n M k
      symbol Str (fun i => t (Fin.FS i))
      (fun w : Fin.t (n + k) -> M => exists x : M,
        arithmetic_interpreted_lt Str x
          (semiterm_val Str w (fun y => y) t0) /\
        Q (fin_env_cons x w)) Hhead) as Htail.
    apply (arithmetic_sorted_definable_of_iff Htail).
    intro z. split.
    + intros [e [Hbound HQe]].
      exists (fun i => e (Fin.FS i)). split.
      * intro i. exact (Hbound (Fin.FS i)).
      * exists (e Fin.F1). split.
        -- unfold t0. rewrite semiterm_val_map.
           rewrite fin_env_append_right_eta. exact (Hbound Fin.F1).
        -- exact HQe.
    + intros [es [Htail_bound [x [Hx HQx]]]].
      exists (fin_env_cons x es). split.
      * intro i. refine (@Fin.caseS' n i
          (fun j => arithmetic_interpreted_lt Str
            (fin_env_cons x es j)
            (semiterm_val Str z (fun y => y) (t j))) _ _).
        -- unfold t0 in Hx. rewrite semiterm_val_map in Hx.
           rewrite fin_env_append_right_eta in Hx. exact Hx.
        -- intro j. exact (Htail_bound j).
      * rewrite fin_env_append_cons. exact HQx.
Defined.

Definition arithmetic_sorted_definable_graph_family_zero
    {M : Type} {n k}
    {Str : first_order_structure oring_language M}
    (f : Fin.t n -> (Fin.t k -> M) -> M)
    (Hf : forall i, arithmetic_sorted_definable_function Str
      arithmetic_sigma_zero_symbol (f i)) :
    arithmetic_sorted_definable Str arithmetic_sigma_zero_symbol
      (fun w : Fin.t (n + k) -> M => forall i,
        w (Fin.L k i) = f i (fun j => w (Fin.R n j))).
Proof.
  apply (arithmetic_sorted_definable_finite_conj
    (R := fun i w =>
      w (Fin.L k i) = f i (fun j => w (Fin.R n j)))
    (fin_t_finite_cover n)).
  intro i.
  apply (arithmetic_sorted_definable_of_iff
    (arithmetic_sorted_definable_retraction (Hf i)
      (fin_graph_retraction i))).
  intro w. reflexivity.
Defined.

Definition arithmetic_sorted_definable_substitution_strictly_bounded_with_params
    {M : Type} {n k symbol}
    {Str : first_order_structure oring_language M}
    (P : (Fin.t k -> M) -> (Fin.t n -> M) -> Prop)
    (f : Fin.t n -> (Fin.t k -> M) -> M)
    (HP : arithmetic_sorted_definable Str symbol
      (fun w : Fin.t (n + k) -> M =>
        P (fun j => w (Fin.R n j)) (fun i => w (Fin.L k i))))
    (Hf : forall i, arithmetic_definably_bounded_function Str
      (arithmetic_interpreted_lt Str) (f i)) :
    arithmetic_sorted_definable Str symbol
      (fun z : Fin.t k -> M => P z (fun i => f i z)).
Proof.
  pose proof (arithmetic_sorted_definable_graph_family_zero (f := f)
    (fun i => arithmetic_definably_bounded_definition (Hf i)))
    as Hgraphs_zero.
  pose proof (arithmetic_sorted_definable_of_zero Hgraphs_zero symbol)
    as Hgraphs.
  pose proof (arithmetic_sorted_definable_and Hgraphs HP)
    as Hbody.
  pose proof (@arithmetic_sorted_definable_bex_vector_terms n M k
    symbol Str
    (fun i => arithmetic_bounded_term
      (arithmetic_definably_bounded_bound (Hf i)))
    (fun w : Fin.t (n + k) -> M =>
      (forall i, w (Fin.L k i) = f i (fun j => w (Fin.R n j))) /\
      P (fun j => w (Fin.R n j))
        (fun i => w (Fin.L k i))) Hbody) as Hexists.
  apply (arithmetic_sorted_definable_of_iff Hexists).
  intro z. split.
  - intro HPf. exists (fun i => f i z). split.
    + intro i. apply (arithmetic_bounded_spec
        (arithmetic_definably_bounded_bound (Hf i)) z).
    + split.
      * intro i. rewrite fin_env_append_left, fin_env_append_right_eta.
        reflexivity.
      * now rewrite fin_env_append_left_eta, fin_env_append_right_eta.
  - intros [e [_ [Hgraphs_e HPe]]].
    assert (He : e = fun i => f i z).
    { apply functional_extensionality. intro i.
      specialize (Hgraphs_e i).
      now rewrite fin_env_append_left, fin_env_append_right_eta in Hgraphs_e. }
    rewrite fin_env_append_left_eta, fin_env_append_right_eta in HPe.
    now rewrite He in HPe.
Defined.

Definition arithmetic_sorted_definable_substitution_strictly_bounded
    {M : Type} {n k symbol}
    {Str : first_order_structure oring_language M}
    (P : (Fin.t n -> M) -> Prop)
    (f : Fin.t n -> (Fin.t k -> M) -> M)
    (HP : arithmetic_sorted_definable Str symbol P)
    (Hf : forall i, arithmetic_definably_bounded_function Str
      (arithmetic_interpreted_lt Str) (f i)) :
    arithmetic_sorted_definable Str symbol
      (fun z : Fin.t k -> M => P (fun i => f i z)).
Proof.
  assert (HP_lift : arithmetic_sorted_definable Str symbol
    (fun w : Fin.t (n + k) -> M => P (fun i => w (Fin.L k i)))).
  { apply (arithmetic_sorted_definable_retraction HP (Fin.L k)). }
  exact (arithmetic_sorted_definable_substitution_strictly_bounded_with_params
    (P := fun _ e => P e) (f := f) HP_lift Hf).
Defined.

(** Place the outer graph output in the head of the external suffix and its
    argument coordinates in the bounded-witness prefix. *)
Definition arithmetic_bounded_outer_graph_reindex {n k} :
    Fin.t (S n) -> Fin.t (n + S k) :=
  fun j => @Fin.caseS' n j (fun _ => Fin.t (n + S k))
    (Fin.R n Fin.F1) (Fin.L (S k)).

Lemma arithmetic_bounded_outer_graph_reindex_head : forall n k,
  @arithmetic_bounded_outer_graph_reindex n k Fin.F1 = Fin.R n Fin.F1.
Proof. reflexivity. Qed.

Lemma arithmetic_bounded_outer_graph_reindex_tail : forall n k
    (i : Fin.t n),
  @arithmetic_bounded_outer_graph_reindex n k (Fin.FS i) =
  Fin.L (S k) i.
Proof. reflexivity. Qed.

Definition arithmetic_sorted_definable_function_substitution_strictly_bounded
    {M : Type} {n k symbol}
    {Str : first_order_structure oring_language M}
    (F : (Fin.t n -> M) -> M)
    (f : Fin.t n -> (Fin.t k -> M) -> M)
    (HF : arithmetic_sorted_definable_function Str symbol F)
    (Hf : forall i, arithmetic_definably_bounded_function Str
      (arithmetic_interpreted_lt Str) (f i)) :
    arithmetic_sorted_definable_function Str symbol
      (fun z : Fin.t k -> M => F (fun i => f i z)).
Proof.
  unfold arithmetic_sorted_definable_function in *.
  pose proof (arithmetic_sorted_definable_retraction HF
    (@arithmetic_bounded_outer_graph_reindex n k)) as Houter.
  pose proof (arithmetic_sorted_definable_substitution_strictly_bounded_with_params
    (P := fun z ys => z Fin.F1 = F ys)
    (f := fun i z => f i (fun q => z (Fin.FS q))) Houter
    (fun i => arithmetic_definably_bounded_retraction
      (Hf i) (fun q => Fin.FS q))) as Hcomposed.
  apply (arithmetic_sorted_definable_of_iff Hcomposed).
  intro w. reflexivity.
Defined.

(** A model-specific successor operation is only one way to turn a weak
    majorant into a strict one.  Factoring the exact semantic bridge through
    an arbitrary term transformation keeps the substitution layer independent
    of Peano-minus model laws. *)
Definition arithmetic_definably_bounded_lift_to_strict
    {M : Type} {k}
    {Str : first_order_structure oring_language M}
    {le : M -> M -> Prop} {f : (Fin.t k -> M) -> M}
    (lift : semiterm oring_language M k ->
      semiterm oring_language M k)
    (Hlift : forall (t : semiterm oring_language M k)
      (v : Fin.t k -> M) x,
      le x (semiterm_val Str v (fun y => y) t) ->
      arithmetic_interpreted_lt Str x
        (semiterm_val Str v (fun y => y) (lift t)))
    (Hf : arithmetic_definably_bounded_function Str le f) :
    arithmetic_definably_bounded_function Str
      (arithmetic_interpreted_lt Str) f.
Proof.
  destruct Hf as [Hbound Hgraph]. constructor.
  - refine {| arithmetic_bounded_term :=
      lift (arithmetic_bounded_term Hbound) |}.
    intro v. apply Hlift. apply arithmetic_bounded_spec.
  - exact Hgraph.
Defined.

Definition arithmetic_sorted_definable_substitution_bounded
    {M : Type} {n k symbol}
    {Str : first_order_structure oring_language M}
    {le : M -> M -> Prop}
    (lift : semiterm oring_language M k ->
      semiterm oring_language M k)
    (Hlift : forall (t : semiterm oring_language M k)
      (v : Fin.t k -> M) x,
      le x (semiterm_val Str v (fun y => y) t) ->
      arithmetic_interpreted_lt Str x
        (semiterm_val Str v (fun y => y) (lift t)))
    (P : (Fin.t n -> M) -> Prop)
    (f : Fin.t n -> (Fin.t k -> M) -> M)
    (HP : arithmetic_sorted_definable Str symbol P)
    (Hf : forall i, arithmetic_definably_bounded_function Str le (f i)) :
    arithmetic_sorted_definable Str symbol
      (fun z : Fin.t k -> M => P (fun i => f i z)).
Proof.
  apply (arithmetic_sorted_definable_substitution_strictly_bounded
    (P := P) (f := f) HP).
  intro i. exact (arithmetic_definably_bounded_lift_to_strict
    (lift := lift) Hlift (Hf i)).
Defined.

Definition arithmetic_sorted_definable_function_substitution_bounded
    {M : Type} {n k symbol}
    {Str : first_order_structure oring_language M}
    {le : M -> M -> Prop}
    (lift : semiterm oring_language M k ->
      semiterm oring_language M k)
    (Hlift : forall (t : semiterm oring_language M k)
      (v : Fin.t k -> M) x,
      le x (semiterm_val Str v (fun y => y) t) ->
      arithmetic_interpreted_lt Str x
        (semiterm_val Str v (fun y => y) (lift t)))
    (F : (Fin.t n -> M) -> M)
    (f : Fin.t n -> (Fin.t k -> M) -> M)
    (HF : arithmetic_sorted_definable_function Str symbol F)
    (Hf : forall i, arithmetic_definably_bounded_function Str le (f i)) :
    arithmetic_sorted_definable_function Str symbol
      (fun z : Fin.t k -> M => F (fun i => f i z)).
Proof.
  apply (arithmetic_sorted_definable_function_substitution_strictly_bounded
    (F := F) (f := f) HF).
  intro i. exact (arithmetic_definably_bounded_lift_to_strict
    (lift := lift) Hlift (Hf i)).
Defined.

Definition arithmetic_definably_bounded_compose
    {M : Type} {n k}
    {Str : first_order_structure oring_language M}
    {le : M -> M -> Prop}
    (Hrefl : forall x, le x x)
    (Htrans : forall x y z, le x y -> le y z -> le x z)
    (Hmon : first_order_structure_monotone le Str)
    (lift : semiterm oring_language M k ->
      semiterm oring_language M k)
    (Hlift : forall (t : semiterm oring_language M k)
      (v : Fin.t k -> M) x,
      le x (semiterm_val Str v (fun y => y) t) ->
      arithmetic_interpreted_lt Str x
        (semiterm_val Str v (fun y => y) (lift t)))
    (F : (Fin.t n -> M) -> M)
    (f : Fin.t n -> (Fin.t k -> M) -> M)
    (HF : arithmetic_definably_bounded_function Str le F)
    (Hf : forall i, arithmetic_definably_bounded_function Str le (f i)) :
    arithmetic_definably_bounded_function Str le
      (fun z : Fin.t k -> M => F (fun i => f i z)).
Proof.
  constructor.
  - apply (arithmetic_bounded_compose Hrefl Htrans Hmon
      (arithmetic_definably_bounded_bound HF)
      (fun i => arithmetic_definably_bounded_bound (Hf i))).
  - apply (arithmetic_sorted_definable_function_substitution_bounded
      (lift := lift) Hlift (F := F) (f := f)
      (arithmetic_definably_bounded_definition HF) Hf).
Defined.

(** In a Peano-minus model the successor term is the canonical strict lift of
    a weak majorant.  This discharges the abstract bridge above without baking
    model laws into the generic substitution proof. *)
Definition arithmetic_peano_minus_majorant_lift {M : Type} {k}
    (t : semiterm oring_language M k) : semiterm oring_language M k :=
  semiterm_add_one
    (semiterm_one_operator_of_language
      (language_oring_one oring_language_structure))
    (semiterm_add_operator_of_language
      (language_oring_add oring_language_structure)) t.

Lemma arithmetic_peano_minus_majorant_lift_spec : forall M k
    (Str : first_order_structure oring_language M)
    (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  forall (t : semiterm oring_language M k) (v : Fin.t k -> M) x,
    peano_minus_le O x (semiterm_val Str v (fun y => y) t) ->
    arithmetic_interpreted_lt Str x
      (semiterm_val Str v (fun y => y)
        (arithmetic_peano_minus_majorant_lift t)).
Proof.
  intros M k Str O Horing Hpa t v x Hle.
  unfold arithmetic_peano_minus_majorant_lift.
  rewrite (@semiterm_val_add_one oring_language M M k Str v
    (fun y => y)
    (semiterm_one_operator_of_language
      (language_oring_one oring_language_structure))
    (semiterm_add_operator_of_language
      (language_oring_add oring_language_structure))
    (oring_one O) (oring_add O) t
    (structure_oring_one Horing) (structure_oring_add Horing)).
  unfold arithmetic_interpreted_lt.
  apply (proj2 (structure_relation_operator
    (structure_oring_lt Horing) x
    (oring_add O (semiterm_val Str v (fun y => y) t) (oring_one O)))).
  now apply (peano_minus_le_lt_add_one Hpa).
Qed.

Definition arithmetic_sorted_definable_substitution_peano_minus
    {M : Type} {n k symbol}
    {Str : first_order_structure oring_language M}
    {O : oring_carrier M}
    (Horing : structure_interprets_oring Str oring_language_structure O)
    (Hpa : peano_minus_laws O)
    (P : (Fin.t n -> M) -> Prop)
    (f : Fin.t n -> (Fin.t k -> M) -> M)
    (HP : arithmetic_sorted_definable Str symbol P)
    (Hf : forall i, arithmetic_definably_bounded_function Str
      (peano_minus_le O) (f i)) :
    arithmetic_sorted_definable Str symbol
      (fun z : Fin.t k -> M => P (fun i => f i z)) :=
  arithmetic_sorted_definable_substitution_bounded
    (lift := arithmetic_peano_minus_majorant_lift)
    (arithmetic_peano_minus_majorant_lift_spec Horing Hpa)
    (P := P) (f := f) HP Hf.

Definition arithmetic_sorted_definable_function_substitution_peano_minus
    {M : Type} {n k symbol}
    {Str : first_order_structure oring_language M}
    {O : oring_carrier M}
    (Horing : structure_interprets_oring Str oring_language_structure O)
    (Hpa : peano_minus_laws O)
    (F : (Fin.t n -> M) -> M)
    (f : Fin.t n -> (Fin.t k -> M) -> M)
    (HF : arithmetic_sorted_definable_function Str symbol F)
    (Hf : forall i, arithmetic_definably_bounded_function Str
      (peano_minus_le O) (f i)) :
    arithmetic_sorted_definable_function Str symbol
      (fun z : Fin.t k -> M => F (fun i => f i z)) :=
  arithmetic_sorted_definable_function_substitution_bounded
    (lift := arithmetic_peano_minus_majorant_lift)
    (arithmetic_peano_minus_majorant_lift_spec Horing Hpa)
    (F := F) (f := f) HF Hf.

Definition arithmetic_definably_bounded_compose_peano_minus
    {M : Type} {n k}
    {Str : first_order_structure oring_language M}
    {O : oring_carrier M}
    (Horing : structure_interprets_oring Str oring_language_structure O)
    (Hpa : peano_minus_laws O)
    (F : (Fin.t n -> M) -> M)
    (f : Fin.t n -> (Fin.t k -> M) -> M)
    (HF : arithmetic_definably_bounded_function Str
      (peano_minus_le O) F)
    (Hf : forall i, arithmetic_definably_bounded_function Str
      (peano_minus_le O) (f i)) :
    arithmetic_definably_bounded_function Str (peano_minus_le O)
      (fun z : Fin.t k -> M => F (fun i => f i z)) :=
  arithmetic_definably_bounded_compose
    (fun x => peano_minus_le_refl x)
    (peano_minus_le_trans Hpa)
    (peano_minus_structure_monotone Horing Hpa)
    (lift := arithmetic_peano_minus_majorant_lift)
    (arithmetic_peano_minus_majorant_lift_spec Horing Hpa)
    (F := F) (f := f) HF Hf.

Definition arithmetic_sorted_definable_compose_predicate_one_strictly_bounded
    {M : Type} {k symbol}
    {Str : first_order_structure oring_language M}
    (P : M -> Prop)
    (f : (Fin.t k -> M) -> M)
    (HP : arithmetic_sorted_definable Str symbol
      (fun v : Fin.t 1 -> M => P (v Fin.F1)))
    (Hf : arithmetic_definably_bounded_function Str
      (arithmetic_interpreted_lt Str) f) :
    arithmetic_sorted_definable Str symbol
      (fun v : Fin.t k -> M => P (f v)).
Proof.
  apply (arithmetic_sorted_definable_substitution_one_strictly_bounded
    (P := fun _ x => P x) (f := f) Hf).
  apply (arithmetic_sorted_definable_retraction HP
    (fun _ : Fin.t 1 => Fin.F1)).
Defined.
