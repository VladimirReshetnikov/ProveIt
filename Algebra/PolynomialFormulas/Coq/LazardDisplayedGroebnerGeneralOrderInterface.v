From Stdlib Require Import Wellfounded.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardDisplayedGroebnerGeneralIdeal
  LazardDisplayedGroebnerGeneralConcrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The order-theoretic interface for the arbitrary-order Coq half of
    Lazard's Lemmas 1 and 2.

    MathComp's [mpoly] fixes degree-reverse-lexicographic order in its
    definitions of [mlead] and [mleadc].  In particular it does not provide a
    type of arbitrary admissible monomial orders or a Buchberger theorem
    parameterized by one.  It would therefore be misleading to formulate the
    paper's theorem with [mlead].  This file instead describes an admissible
    order explicitly on the combined monomials

      [(root exponent, formal-e exponent)].

    The literal polynomial is retained in the nested but equivalent
    presentation [F[e_1,...,e_n][x_0,...,x_(n-1)]].  Its coefficient at a
    combined monomial is obtained by two successive [mcoeff] operations.

    The record [literal_reduced_groebner_certificate] below is the smallest
    certificate used here for the phrase "monic reduced Groebner basis":

    - the displayed family generates the Vieta ideal;
    - every displayed polynomial has the claimed monic leading monomial;
    - distinct displayed leading monomials do not divide one another;
    - no monomial in any tail is divisible by a displayed leading monomial;
    - every leading monomial of a nonzero ideal member is divisible by one of
      the displayed leading monomials.

    The last field is the initial-ideal property.  It does not follow merely
    from equality of generated ideals, monic incomparable leading terms, and
    reduced tails.  For example, in lexicographic order with [x > y], the
    monic family [x^2 + y, x*y + 1] has incomparable leading monomials and
    reduced tails, but its S-polynomial is [y^2 - x], whose leading monomial
    is divisible by neither.  [displayed_division_normal_form]
    exposes a standard sufficient interface: a unique standard remainder
    which preserves an irreducible leading coefficient.  The theorem
    [division_normal_form_initial_divisibility] derives the initial-ideal
    property from that interface.

    This interface file deliberately does not postulate an inhabitant of
    [displayed_division_normal_form].  The separate
    [LazardDisplayedGroebnerGeneralOrderPort] constructs one by well-founded
    monic division for every decidably represented paper order and proves
    uniqueness by Artin separation.

    For Lemma 2 the independent Reynolds construction also retains its honest
    hypothesis [(#|G| : F) != 0].  The paper's global assumption
    [char(F) != 2,5] does not imply this for arbitrary [d] and [G]; nothing in
    this interface weakens or hides that hypothesis. *)
Module PolynomialFormulasLazardDisplayedGroebnerGeneralOrderInterface.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope mpoly_scope.

Module GI := PolynomialFormulasLazardDisplayedGroebnerGeneralIdeal.
Module GC := PolynomialFormulasLazardDisplayedGroebnerGeneralConcrete.

Section CombinedOrder.

Variables (F : fieldType) (n : nat).

Local Notation Coeff := {mpoly F[n]}.
Local Notation Ambient := {mpoly Coeff[n]}.

(** Root exponents are the first component and formal elementary-symmetric
    exponents are the second component. *)
Definition combined_monomial : Type :=
  ('X_{1..n} * 'X_{1..n})%type.

Definition combined_zero : combined_monomial := (0%MM, 0%MM).

Definition combined_add
    (a b : combined_monomial) : combined_monomial :=
  ((a.1 + b.1)%MM, (a.2 + b.2)%MM).

Definition combined_root_degree (a : combined_monomial) : nat :=
  mdeg a.1.

Definition combined_root_variable (i : 'I_n) : combined_monomial :=
  (U_(i)%MM, 0%MM).

Definition combined_coefficient_variable (i : 'I_n) : combined_monomial :=
  (0%MM, U_(i)%MM).

(** Coefficient extraction in the literal combined ring, represented as a
    nested multivariate polynomial. *)
Definition combined_coefficient
    (p : Ambient) (a : combined_monomial) : F :=
  (p @_ a.1) @_ a.2.

Definition combined_support
    (p : Ambient) (a : combined_monomial) : Prop :=
  combined_coefficient p a <> 0.

(** The actual nested monomial corresponding to a combined exponent. *)
Definition combined_monomial_polynomial
    (a : combined_monomial) : Ambient :=
  ('X_[F, a.2] : Coeff) *: ('X_[Coeff, a.1] : Ambient).

(** Monomial divisibility is componentwise divisibility in the two blocks. *)
Definition combined_divides
    (a b : combined_monomial) : bool :=
  (a.1 <= b.1)%MM && (a.2 <= b.2)%MM.

(** The relation indexed by [k] has root degree [k+1], uses the first
    [n-k] root variables, and has pivot [x_(n-1-k)]. *)
Definition displayed_pivot (k : 'I_n) : 'I_n := rev_ord k.

Definition displayed_leading_monomial
    (k : 'I_n) : combined_monomial :=
  ((U_(displayed_pivot k) *+ k.+1)%MM, 0%MM).

Definition literal_displayed_family : 'I_n -> Ambient :=
  @GC.conventional_printed_displayed_J F n.

Definition literal_vieta_family : 'I_n -> Ambient :=
  @GC.concrete_vieta_relation F n.

Definition literal_displayed_tail (k : 'I_n) : Ambient :=
  literal_displayed_family k -
    combined_monomial_polynomial (displayed_leading_monomial k).

Definition literal_displayed_ideal (p : Ambient) : Prop :=
  @GI.generated_by Ambient n literal_displayed_family p.

Definition literal_vieta_ideal (p : Ambient) : Prop :=
  @GI.generated_by Ambient n literal_vieta_family p.

(** An admissible monomial order, stated independently of MathComp's fixed
    canonical order.  [amo_add_compat] is translation compatibility; together
    with total antisymmetry it is the usual multiplicative compatibility for
    monomials. *)
Record admissible_monomial_order := AdmissibleMonomialOrder {
  amo_le : combined_monomial -> combined_monomial -> Prop;
  amo_le_refl : forall a, amo_le a a;
  amo_le_antisym : forall a b, amo_le a b -> amo_le b a -> a = b;
  amo_le_trans : forall a b c, amo_le a b -> amo_le b c -> amo_le a c;
  amo_le_total : forall a b, amo_le a b \/ amo_le b a;
  amo_zero_le : forall a, amo_le combined_zero a;
  amo_add_compat : forall a b c,
    amo_le a b <-> amo_le (combined_add a c) (combined_add b c);
  amo_lt_well_founded :
    well_founded (fun a b => amo_le a b /\ a <> b)
}.

Definition amo_lt (O : admissible_monomial_order)
    (a b : combined_monomial) : Prop :=
  amo_le O a b /\ a <> b.

(** Exactly the two additional hypotheses printed before Lemma 1: root
    degree is the primary block, and the root variables are ordered by their
    indices.  No desired leading term is included in this record. *)
Record paper_order_hypotheses (O : admissible_monomial_order) : Prop :=
  PaperOrderHypotheses {
    poh_root_degree_primary : forall a b,
      (combined_root_degree a < combined_root_degree b)%N -> amo_lt O a b;
    poh_root_variables_strict : forall i j : 'I_n,
      (i < j)%N ->
      amo_lt O (combined_root_variable i) (combined_root_variable j)
  }.

(** An admissible order on the formal-[e] exponent block alone.  Lazard's
    Lemma 2 leaves this order arbitrary, but explicitly gives this block
    priority after root total degree. *)
Record admissible_exponent_order := AdmissibleExponentOrder {
  aeo_le : 'X_{1..n} -> 'X_{1..n} -> Prop;
  aeo_le_refl : forall a, aeo_le a a;
  aeo_le_antisym : forall a b,
    aeo_le a b -> aeo_le b a -> a = b;
  aeo_le_trans : forall a b c,
    aeo_le a b -> aeo_le b c -> aeo_le a c;
  aeo_le_total : forall a b, aeo_le a b \/ aeo_le b a;
  aeo_zero_le : forall a, aeo_le 0%MM a;
  aeo_add_compat : forall a b c,
    aeo_le a b <-> aeo_le (a + c)%MM (b + c)%MM;
  aeo_lt_well_founded :
    well_founded (fun a b => aeo_le a b /\ a <> b)
}.

Definition aeo_lt (O : admissible_exponent_order)
    (a b : 'X_{1..n}) : Prop :=
  aeo_le O a b /\ a <> b.

(** Lazard's complete order refinement for Lemma 2.  When root degrees are
    equal and the formal exponents differ, the formal block decides the
    comparison.  Equal formal exponents are left to the ambient admissible
    order's root tie breaker.  The current leading-term theorem uses only
    the inherited Lemma-1 hypotheses because its whole top row is already
    formal-[e]-free, but this record makes the literal quantified scope
    explicit. *)
Record paper_lemma_two_order_hypotheses
    (O : admissible_monomial_order) : Type :=
  PaperLemmaTwoOrderHypotheses {
    plto_lemma_one_order : paper_order_hypotheses O;
    plto_formal_order : admissible_exponent_order;
    plto_formal_block_primary : forall a b : combined_monomial,
      combined_root_degree a = combined_root_degree b ->
      a.2 <> b.2 ->
      (amo_lt O a b <-> aeo_lt plto_formal_order a.2 b.2)
  }.

Definition is_leading_monomial (O : admissible_monomial_order)
    (p : Ambient) (a : combined_monomial) : Prop :=
  combined_support p a /\
  forall b, combined_support p b -> b <> a -> amo_lt O b a.

(** Finite support and totality imply this selection property.  It is kept as
    a separate interface until the nested-support enumeration lemma has been
    written, so that the final certificate cannot use a vacuous universally
    quantified "leading monomial" clause. *)
Record combined_leading_selection
    (O : admissible_monomial_order) : Prop := CombinedLeadingSelection {
  cls_leading_exists : forall p : Ambient,
    p <> 0 -> exists a, is_leading_monomial O p a
}.

Definition literal_standard (p : Ambient) : Prop :=
  forall a, combined_support p a ->
    forall k : 'I_n,
      ~ combined_divides (displayed_leading_monomial k) a.

Lemma combined_zero_not_support (a : combined_monomial) :
  ~ combined_support (0 : Ambient) a.
Proof.
move=> ha; apply: ha.
by rewrite /combined_coefficient !mcoeff0.
Qed.

Lemma literal_standard0 : literal_standard (0 : Ambient).
Proof.
move=> a ha.
exact: False_rect _ (combined_zero_not_support ha).
Qed.

(** Order-dependent support facts for the literal displayed family.  The
    eventual concrete proof of this record must derive [lod_leading] from the
    two fields of [paper_order_hypotheses], using the weak-composition support
    theorem for [GC.conventional_prefix_h]. *)
Record literal_order_data (O : admissible_monomial_order) : Prop :=
  LiteralOrderData {
    lod_paper_order : paper_order_hypotheses O;
    lod_monic : forall k : 'I_n,
      combined_coefficient (literal_displayed_family k)
        (displayed_leading_monomial k) = 1;
    lod_leading : forall k : 'I_n,
      is_leading_monomial O (literal_displayed_family k)
        (displayed_leading_monomial k);
    lod_leading_minimal : forall i j : 'I_n,
      i <> j ->
      ~ combined_divides
          (displayed_leading_monomial i)
          (displayed_leading_monomial j);
    lod_reduced_tails : forall k : 'I_n,
      literal_standard (literal_displayed_tail k)
  }.

(** The normal-form interface which is sufficient to turn ideal equality and
    the order-dependent support calculation into the initial-ideal theorem.

    [dnf_preserves_irreducible_leading] is the essential division fact: if the
    leading monomial of [p] is not reducible by a displayed leading monomial,
    division leaves its coefficient unchanged.  Neither ideal equality nor
    abstract Artin-basis independence proves this order-sensitive fact by
    itself. *)
Record displayed_division_normal_form
    (O : admissible_monomial_order) : Type := DisplayedDivisionNormalForm {
  dnf : Ambient -> Ambient;
  dnf_standard : forall p, literal_standard (dnf p);
  dnf_congruent : forall p, literal_displayed_ideal (p - dnf p);
  dnf_unique : forall p s,
    literal_standard s ->
    literal_displayed_ideal (p - s) ->
    s = dnf p;
  dnf_preserves_irreducible_leading : forall p a,
    is_leading_monomial O p a ->
    (forall k : 'I_n,
      ~ combined_divides (displayed_leading_monomial k) a) ->
    combined_coefficient (dnf p) a = combined_coefficient p a
}.

Lemma division_normal_form_member_iff_zero
    (O : admissible_monomial_order)
    (N : displayed_division_normal_form O) p :
  literal_displayed_ideal p <-> dnf N p = 0.
Proof.
split.
- move=> hp.
  have hzero : literal_displayed_ideal (p - 0) by
    rewrite subr0.
  have h := @dnf_unique O N p 0 literal_standard0 hzero.
  exact: esym h.
- move=> hzero.
  have h := dnf_congruent N p.
  by rewrite hzero subr0 in h.
Qed.

(** The missing initial-ideal conclusion follows honestly from the normal-form
    preservation property; it is not bundled into an opaque assumption. *)
Theorem division_normal_form_initial_divisibility
    (O : admissible_monomial_order)
    (N : displayed_division_normal_form O)
    (p : Ambient) (a : combined_monomial) :
  literal_displayed_ideal p ->
  p <> 0 ->
  is_leading_monomial O p a ->
  exists k : 'I_n,
    combined_divides (displayed_leading_monomial k) a.
Proof.
move=> hp _ hlead.
case hexists: [exists k : 'I_n,
    combined_divides (displayed_leading_monomial k) a].
- have /existsP [k hk] := hexists.
  by exists k.
- have hnone : ~ exists k : 'I_n,
      combined_divides (displayed_leading_monomial k) a.
    move=> [k hk].
    have hcontra : [exists j : 'I_n,
        combined_divides (displayed_leading_monomial j) a].
      apply/existsP; by exists k.
    by rewrite hexists in hcontra.
have hnot k :
    ~ combined_divides (displayed_leading_monomial k) a.
  move=> hk; apply: hnone; by exists k.
have hpreserve := dnf_preserves_irreducible_leading N hlead hnot.
have hnf0 := (@division_normal_form_member_iff_zero O N p).1 hp.
rewrite hnf0 /combined_coefficient !mcoeff0 in hpreserve.
have hnonzero := hlead.1.
apply: False_rect _ (hnonzero (esym hpreserve)).
Qed.

(** The exact, literal reduced-Groebner certificate.  In particular
    [lrg_initial_divisibility] is present, so this record is strictly stronger
    than a change-of-generators or unique-quotient statement. *)
Record literal_reduced_groebner_certificate
    (O : admissible_monomial_order) : Prop :=
  LiteralReducedGroebnerCertificate {
    lrg_paper_order : paper_order_hypotheses O;
    lrg_generated_ideal : forall p,
      literal_displayed_ideal p <-> literal_vieta_ideal p;
    lrg_monic : forall k : 'I_n,
      combined_coefficient (literal_displayed_family k)
        (displayed_leading_monomial k) = 1;
    lrg_leading : forall k : 'I_n,
      is_leading_monomial O (literal_displayed_family k)
        (displayed_leading_monomial k);
    lrg_leading_minimal : forall i j : 'I_n,
      i <> j ->
      ~ combined_divides
          (displayed_leading_monomial i)
          (displayed_leading_monomial j);
    lrg_reduced_tails : forall k : 'I_n,
      literal_standard (literal_displayed_tail k);
    lrg_leading_exists : forall p : Ambient,
      p <> 0 -> exists a, is_leading_monomial O p a;
    lrg_initial_divisibility : forall p a,
      literal_displayed_ideal p ->
      p <> 0 ->
      is_leading_monomial O p a ->
      exists k : 'I_n,
        combined_divides (displayed_leading_monomial k) a
  }.

(** Nonvacuous defining initial-ideal statement extracted from the bundled
    certificate. *)
Theorem nonzero_ideal_member_has_divisible_leading
    (O : admissible_monomial_order)
    (C : literal_reduced_groebner_certificate O)
    (p : Ambient) :
  literal_displayed_ideal p -> p <> 0 ->
  exists (a : combined_monomial) (k : 'I_n),
    is_leading_monomial O p a /\
    combined_divides (displayed_leading_monomial k) a.
Proof.
move=> hp hp0.
have [a ha] := lrg_leading_exists C hp0.
have [k hk] := lrg_initial_divisibility C hp hp0 ha.
by exists a, k.
Qed.

(** Modular endpoint for Lemma 1.  The ideal-equality field is discharged by
    the concrete all-degrees theorem.  Its downstream port constructs
    [literal_order_data], finite-support leading selection, and
    [displayed_division_normal_form] from the paper-order hypotheses. *)
Theorem literal_reduced_groebner_of_order_and_division
    (O : admissible_monomial_order)
    (D : literal_order_data O)
    (S : combined_leading_selection O)
    (N : displayed_division_normal_form O) :
  literal_reduced_groebner_certificate O.
Proof.
constructor.
- exact: lod_paper_order D.
- move=> p.
  exact: GC.conventional_printed_generated_ideal_eq_vieta.
- exact: lod_monic D.
- exact: lod_leading D.
- exact: lod_leading_minimal D.
- exact: lod_reduced_tails D.
- exact: cls_leading_exists S.
- exact: division_normal_form_initial_divisibility.
Qed.

(** * The last order-theoretic step in Lemma 2

    The intrinsic Reynolds development proves a stronger property than the
    paper's single-leading-term claim: no row lies above [d], the entire row
    [d] has ground-field coefficients, and some coefficient in that row is
    nonzero.  The following order-free record expresses precisely those three
    statements for the literal combined support. *)
Record literal_top_row_constant
    (p : Ambient) (d : nat) : Prop := LiteralTopRowConstant {
  ltr_degree_le : forall a,
    combined_support p a -> (combined_root_degree a <= d)%N;
  ltr_top_exists : exists a,
    combined_support p a /\
    combined_root_degree a = d /\ a.2 = 0%MM;
  ltr_top_coefficients_constant : forall a,
    combined_support p a ->
    combined_root_degree a = d ->
    a.2 = 0%MM
}.

(** Any actual leading monomial of such a representative has root degree [d]
    and contains no formal [e] variable.  Root-degree primacy alone is enough
    here: the stronger whole-top-row certificate makes the paper's extra
    equal-degree tie breaker unnecessary for this final implication. *)
Theorem leading_monomial_root_degree_and_coefficient_part_zero
    (O : admissible_monomial_order)
    (hpaper : paper_order_hypotheses O)
    (p : Ambient) (d : nat) (a : combined_monomial) :
  literal_top_row_constant p d ->
  is_leading_monomial O p a ->
  combined_root_degree a = d /\ a.2 = 0%MM.
Proof.
move=> htop hlead.
have hadeg : (combined_root_degree a <= d)%N :=
  ltr_degree_le htop hlead.1.
have [b [hbsupport [hbdeg _]]] := ltr_top_exists htop.
have hadeq : combined_root_degree a = d.
  move: hadeg; rewrite leq_eqVlt => /orP [/eqP hadeq | hadlt].
  - exact: hadeq.
  - have hab : amo_lt O a b.
      apply: (@poh_root_degree_primary O hpaper a b).
      by rewrite hbdeg.
    have hba : amo_lt O b a.
      apply: hlead.2.
      - exact: hbsupport.
      - move=> hbaeq.
        move: hab; rewrite hbaeq /amo_lt.
        by move=> [_ hne]; exact: hne erefl.
    have heq : a = b :=
      @amo_le_antisym O a b hab.1 hba.1.
    exact: False_rect _ (hab.2 heq).
split; first exact: hadeq.
exact (@ltr_top_coefficients_constant p d htop a hlead.1 hadeq).
Qed.

(** Backwards-compatible projection of the exact combined-leading theorem. *)
Theorem leading_monomial_coefficient_part_zero
    (O : admissible_monomial_order)
    (hpaper : paper_order_hypotheses O)
    (p : Ambient) (d : nat) (a : combined_monomial) :
  literal_top_row_constant p d ->
  is_leading_monomial O p a ->
  a.2 = 0%MM.
Proof.
move=> htop hlead.
exact: (leading_monomial_root_degree_and_coefficient_part_zero
  hpaper htop hlead).2.
Qed.

(** Exact-paper-order corollary.  The formal-block field is deliberately
    unused: the stronger whole-top-row certificate proves a conclusion
    independent of every equal-root-degree tie breaker. *)
Theorem leading_monomial_of_paper_lemma_two_order
    (O : admissible_monomial_order)
    (hpaper : paper_lemma_two_order_hypotheses O)
    (p : Ambient) (d : nat) (a : combined_monomial) :
  literal_top_row_constant p d ->
  is_leading_monomial O p a ->
  combined_root_degree a = d /\ a.2 = 0%MM.
Proof.
move=> htop hlead.
exact (@leading_monomial_root_degree_and_coefficient_part_zero
  O (plto_lemma_one_order hpaper) p d a htop hlead).
Qed.

End CombinedOrder.

End PolynomialFormulasLazardDisplayedGroebnerGeneralOrderInterface.
