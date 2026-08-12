From HB Require Import structures.
From Stdlib Require Import Ring Wellfounded.Inverse_Image.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantMultinomials
  LazardInvariantFiniteFree
  LazardInvariantSymmetricModule
  LazardInvariantArtinSuccessor
  LazardInvariantVietaReduction
  LazardDisplayedGroebnerGeneralOrderInterface.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The constructive part of the arbitrary-order Coq port of Lazard's
    displayed Groebner argument.

    This file does not use MathComp's fixed [mlead] order.  It supplies the
    two order-independent pieces which were still abstract in
    [LazardDisplayedGroebnerGeneralOrderInterface]:

    - finite nested support really has a greatest member for every decidable
      admissible order, so leading-monomial selection is not an assumption;
    - a standard polynomial in the displayed ideal is zero.  The latter is
      proved in every degree over a field by reversing the already proved
      all-degree Artin basis and specializing the formal [e_i] to the actual
      elementary symmetric polynomials.

    The direct support calculation for the printed family is kept visible in
    [literal_order_support_data]: monicity, support dominance, and reduced
    tails are not smuggled into the order axioms.  This file constructs that
    record from the recursive complete-homogeneous formula.  It also exposes
    the output of ordinary monic multivariate division through the modular
    record [literal_division_existence], and then constructs that record by
    well-founded reduction.  Uniqueness is *not* a field of the latter; it is
    proved below from Artin-basis separation.  Thus no Buchberger or division
    API is postulated under another name, and the final endpoint takes only
    the paper's order hypotheses and decidability of the order relation. *)
Module PolynomialFormulasLazardDisplayedGroebnerGeneralOrderPort.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module FF := PolynomialFormulasLazardInvariantFiniteFree.
Module SM := PolynomialFormulasLazardInvariantSymmetricModule.
Module AS := PolynomialFormulasLazardInvariantArtinSuccessor.
Module VR := PolynomialFormulasLazardInvariantVietaReduction.
Module OI := PolynomialFormulasLazardDisplayedGroebnerGeneralOrderInterface.
Module GI := OI.GI.
Module GC := OI.GC.

Arguments OI.displayed_pivot n k : clear implicits.
Arguments OI.displayed_leading_monomial n k : clear implicits.
Arguments OI.combined_root_variable n i : clear implicits.
Arguments OI.combined_monomial_polynomial F n a : clear implicits.
Arguments OI.literal_displayed_family F n k : clear implicits.
Arguments OI.literal_vieta_family F n k : clear implicits.
Arguments OI.literal_displayed_tail F n k : clear implicits.
Arguments OI.literal_standard F n p : clear implicits.
Arguments OI.literal_displayed_ideal F n p : clear implicits.
Arguments OI.literal_vieta_ideal F n p : clear implicits.
Arguments GC.root_x R n i : clear implicits.
Arguments GC.prefix_root_tuple R n k : clear implicits.
Arguments GC.conventional_prefix_h R n k r : clear implicits.
Arguments GC.prefix_index {n} k j.

(** * Finite-support leading selection *)

Section LeadingSelection.

Variables (F : fieldType) (n : nat).

Local Notation Coeff := {mpoly F[n]}.
Local Notation Ambient := {mpoly Coeff[n]}.
Local Notation Monomial := (OI.combined_monomial n).

(** The literal support of the nested presentation, enumerated as pairs of
    outer/root and inner/formal-coefficient exponents. *)
Definition combined_support_sequence (p : Ambient) : seq Monomial :=
  flatten
    [seq [seq (u, v) | v <- msupp (p @_ u)] | u <- msupp p].

Lemma combined_support_sequenceP (p : Ambient) (a : Monomial) :
  reflect (OI.combined_support p a)
    (a \in combined_support_sequence p).
Proof.
apply: (iffP idP).
- rewrite /combined_support_sequence.
  move/flattenP=> [s /mapP [u hu ->] /mapP [v hv ->]].
  rewrite /OI.combined_support /OI.combined_coefficient.
  change ((p @_ u) @_ v <> 0).
  move=> hv0.
  move: hv.
  by rewrite mcoeff_msupp hv0 eqxx.
- move=> ha.
  rewrite /combined_support_sequence.
  apply/flattenP.
  exists [seq (a.1, v) | v <- msupp (p @_ a.1)].
  + apply/mapP; exists a.1 => //.
    rewrite mcoeff_msupp.
    apply/negP=> /eqP houter.
    apply: ha.
    by rewrite /OI.combined_coefficient houter mcoeff0.
  + apply/mapP; exists a.2 => //.
    rewrite mcoeff_msupp.
    apply/negP=> /eqP hzero.
    apply: ha.
    exact: hzero.
case: a ha => a1 a2 /= ha.
exact: erefl.
Qed.

Lemma combined_support_sequence_nonempty (p : Ambient) :
  p <> 0 -> combined_support_sequence p != [::].
Proof.
move=> hp0; apply/eqP=> hs0.
apply: hp0; apply/mpolyP=> u.
rewrite mcoeff0; apply/eqP; rewrite mcoeff_eq0; apply/negP=> hu.
have houter : p @_ u != 0 by rewrite -mcoeff_msupp.
have hv : mlead (p @_ u) \in msupp (p @_ u) :=
  mlead_supp houter.
have hpairs : (u, mlead (p @_ u)) \in combined_support_sequence p.
  apply/combined_support_sequenceP.
  rewrite /OI.combined_support /OI.combined_coefficient.
  change ((p @_ u) @_ (mlead (p @_ u)) <> 0).
  move=> hzero.
  move: hv.
  by rewrite mcoeff_msupp hzero eqxx.
by rewrite hs0 in hpairs.
Qed.

(** Decidability is kept explicit.  Every concrete monomial order used in a
    Groebner calculation has it, whereas the Prop-valued order interface by
    itself intentionally does not invoke classical choice. *)
Record decidable_admissible_order
    (O : OI.admissible_monomial_order n) : Type :=
  DecidableAdmissibleOrder {
    dao_le_dec : forall a b : Monomial,
      {OI.amo_le O a b} + {~ OI.amo_le O a b}
  }.

Definition choose_larger
    (O : OI.admissible_monomial_order n)
    (D : decidable_admissible_order O) (a b : Monomial) : Monomial :=
  if dao_le_dec D a b then b else a.

Lemma choose_larger_left_le
    (O : OI.admissible_monomial_order n)
    (D : decidable_admissible_order O) a b :
  OI.amo_le O a (choose_larger D a b).
Proof.
rewrite /choose_larger; case: dao_le_dec=> hab.
- exact: hab.
- exact: OI.amo_le_refl O a.
Qed.

Lemma choose_larger_right_le
    (O : OI.admissible_monomial_order n)
    (D : decidable_admissible_order O) a b :
  OI.amo_le O b (choose_larger D a b).
Proof.
rewrite /choose_larger; case: dao_le_dec=> hab.
- exact: OI.amo_le_refl O b.
- have [hab'|hba] := OI.amo_le_total O a b.
  + exact: False_rect _ (hab hab').
  + exact: hba.
Qed.

Lemma choose_larger_cases
    (O : OI.admissible_monomial_order n)
    (D : decidable_admissible_order O) a b :
  choose_larger D a b = a \/ choose_larger D a b = b.
Proof.
rewrite /choose_larger; case: dao_le_dec; by [right | left].
Qed.

Fixpoint maximum_from
    (O : OI.admissible_monomial_order n)
    (D : decidable_admissible_order O)
    (a : Monomial) (s : seq Monomial) : Monomial :=
  if s is b :: s' then maximum_from D (choose_larger D a b) s'
  else a.

Lemma maximum_from_mem
    (O : OI.admissible_monomial_order n)
    (D : decidable_admissible_order O) a s :
  maximum_from D a s \in a :: s.
Proof.
elim: s a=> [|b s ih] a /=.
- by rewrite in_cons eqxx.
- have hm := ih (choose_larger D a b).
  move: hm; rewrite in_cons=> /orP [/eqP hm|hm].
  + rewrite hm !in_cons.
    have [->|->] := choose_larger_cases D a b;
      by rewrite eqxx ?orbT.
  + by rewrite !in_cons hm !orbT.
Qed.

Lemma maximum_from_upper
    (O : OI.admissible_monomial_order n)
    (D : decidable_admissible_order O) a s x :
  (x = a \/ x \in s) ->
  OI.amo_le O x (maximum_from D a s).
Proof.
elim: s a x=> [|b s ih] a x /=.
- move=> [->|hx]; first exact: OI.amo_le_refl O a.
  by move: hx; rewrite in_nil.
- move=> [->|hx].
  + eapply OI.amo_le_trans.
    { exact: choose_larger_left_le D a b. }
    { exact: (ih _ _ (or_introl erefl)). }
  + move: hx; rewrite in_cons=> /orP [/eqP ->|hx].
    * eapply OI.amo_le_trans.
      { exact: choose_larger_right_le D a b. }
      { exact: (ih _ _ (or_introl erefl)). }
    * exact: (ih _ _ (or_intror hx)).
Qed.

(** A computational leading monomial, with [combined_zero] as the harmless
    value on the zero polynomial. *)
Definition combined_leading_monomial
    (O : OI.admissible_monomial_order n)
    (D : decidable_admissible_order O) (p : Ambient) : Monomial :=
  match combined_support_sequence p with
  | [::] => OI.combined_zero n
  | a :: s => maximum_from D a s
  end.

Lemma combined_leading_monomialP
    (O : OI.admissible_monomial_order n)
    (D : decidable_admissible_order O) p :
  p <> 0 ->
  OI.is_leading_monomial O p (combined_leading_monomial D p).
Proof.
move=> hp0.
have hsne := combined_support_sequence_nonempty hp0.
case hs: (combined_support_sequence p) hsne=> [|a s] //= _.
split.
- apply/combined_support_sequenceP.
  rewrite /combined_leading_monomial hs.
  exact: maximum_from_mem.
- move=> b hb hba; split; last exact: hba.
  rewrite /combined_leading_monomial hs.
  apply: maximum_from_upper.
  have hbs : b \in a :: s.
    move/combined_support_sequenceP: hb.
    by rewrite hs.
  move: hbs; rewrite in_cons=> /orP [/eqP ->|hbs].
  + exact: or_introl erefl.
  + exact: or_intror hbs.
Qed.

Lemma is_leading_monomial_upper
    (O : OI.admissible_monomial_order n)
    (p : Ambient) (a b : Monomial) :
  OI.is_leading_monomial O p a -> OI.combined_support p b ->
  OI.amo_le O b a.
Proof.
move=> ha hb; case: (boolP (b == a))=> [/eqP ->|hba].
- exact: OI.amo_le_refl O a.
- apply: (ha.2 b hb _).1 => h.
  move: hba.
  by rewrite h eqxx.
Qed.

Lemma is_leading_monomial_unique
    (O : OI.admissible_monomial_order n)
    (p : Ambient) (a b : Monomial) :
  OI.is_leading_monomial O p a ->
  OI.is_leading_monomial O p b -> a = b.
Proof.
move=> ha hb.
apply: OI.amo_le_antisym.
- exact: is_leading_monomial_upper hb ha.1.
- exact: is_leading_monomial_upper ha hb.1.
Qed.

(** Finite support discharges [combined_leading_selection] for every
    decidable admissible order. *)
Theorem combined_leading_selection_of_decidable_order
    (O : OI.admissible_monomial_order n)
    (D : decidable_admissible_order O) :
  @OI.combined_leading_selection F n O.
Proof.
constructor=> p hp0.
exists (combined_leading_monomial D p).
exact: combined_leading_monomialP hp0.
Qed.

End LeadingSelection.

(** The displayed leading powers use distinct pivot variables, hence their
    monomials are automatically incomparable for divisibility.  This field
    of [literal_order_data] is therefore not part of the remaining support
    calculation. *)
Section LeadingMinimality.

Variables (F : fieldType) (n : nat).

Lemma displayed_leading_monomials_incomparable (i j : 'I_n) :
  i <> j ->
  ~ OI.combined_divides
      (OI.displayed_leading_monomial n i)
      (OI.displayed_leading_monomial n j).
Proof.
move=> hij /andP [hroot _].
have hpneq : OI.displayed_pivot n j != OI.displayed_pivot n i.
  apply/negP=> /eqP hp.
  apply: hij.
  move: hp; rewrite /OI.displayed_pivot => hp.
  symmetry.
  exact: rev_ord_inj hp.
have hcoord := mnm_lepP hroot (OI.displayed_pivot n i).
move: hcoord.
by rewrite /OI.displayed_leading_monomial
  !mulmnE !mnm1E eqxx (negbTE hpneq) mul1n mul0n leqn0.
Qed.

(** The genuinely support-sensitive portion of [literal_order_data]. *)
Record literal_order_support_data
    (O : OI.admissible_monomial_order n) : Prop :=
  LiteralOrderSupportData {
    losd_paper_order : OI.paper_order_hypotheses O;
    losd_monic : forall k : 'I_n,
      OI.combined_coefficient (OI.literal_displayed_family F n k)
        (OI.displayed_leading_monomial n k) = (1%R : F);
    losd_leading : forall k : 'I_n,
      OI.is_leading_monomial O (OI.literal_displayed_family F n k)
        (OI.displayed_leading_monomial n k);
    losd_reduced_tails : forall k : 'I_n,
      OI.literal_standard F n (OI.literal_displayed_tail F n k)
  }.

Theorem literal_order_data_of_support_data
    (O : OI.admissible_monomial_order n)
    (D : literal_order_support_data O) :
  @OI.literal_order_data F n O.
Proof.
constructor.
- exact: losd_paper_order D.
- exact: losd_monic D.
- exact: losd_leading D.
- exact: displayed_leading_monomials_incomparable.
- exact: losd_reduced_tails D.
Qed.

End LeadingMinimality.

(** * Support of the literal complete-homogeneous coefficients *)

Section LiteralCompleteHomogeneousSupport.

Variables (F : fieldType) (n : nat).

Local Notation Coeff := {mpoly F[n]}.
Local Notation Ambient := {mpoly Coeff[n]}.

Lemma complete_homogeneous_seq_dhomog
    (xs : seq Ambient) r :
  (forall x, x \in xs -> x \is 1.-homog) ->
  GC.complete_homogeneous_seq xs r \is r.-homog.
Proof.
elim: xs r=> [|x xs ih] r hxs /=.
- case: r=> [|r] /=.
  + exact: dhomog1.
  + exact: dhomog0.
- apply/rpred_sum=> i _.
  have hx : x \is 1.-homog := hxs x (mem_head x xs).
  have hxi := dhomogMn (i : nat) hx.
  rewrite mul1n in hxi.
  have htail :
      GC.complete_homogeneous_seq xs (r - i) \is (r - i).-homog.
    apply: ih=> y hy.
    apply: hxs.
    by rewrite in_cons hy orbT.
  have hproduct := dhomogM hxi htail.
  move: hproduct.
  have hir : ((i : nat) <= r)%N by exact: ltn_ord i.
  by rewrite addnC (subnK hir).
Qed.

Lemma root_x_dhomog (i : 'I_n) :
  GC.root_x F n i \is 1.-homog.
Proof.
rewrite /GC.root_x dhomogX.
apply/eqP.
exact: mdeg1 i.
Qed.

Lemma conventional_prefix_h_dhomog (k : 'I_n) r :
  GC.conventional_prefix_h F n k r \is r.-homog.
Proof.
rewrite /GC.conventional_prefix_h.
apply: complete_homogeneous_seq_dhomog=> x.
rewrite /GC.prefix_root_tuple=> hx.
move/mapP: hx=> [j _ ->].
exact: root_x_dhomog.
Qed.

Lemma conventional_prefix_h_support_degree (k : 'I_n) r u :
  u \in msupp (GC.conventional_prefix_h F n k r) -> mdeg u = r.
Proof.
move=> hu.
have hh := @conventional_prefix_h_dhomog k r.
exact: (dhomog_mf hh (x := u) hu).
Qed.

Lemma mpolyC_support_zero (c : Coeff) (u : 'X_{1..n}) :
  u \in msupp c%:MP -> u = 0%MM.
Proof.
rewrite msuppC; case: eqP=> _.
- by rewrite in_nil.
- by rewrite mem_seq1=> /eqP.
Qed.

(** The same constant-support fact one coefficient layer lower.  Keeping the
    two statements separate makes the nested coefficient ring explicit and
    prevents Coq from trying to use the outer specialization at an inner
    support goal. *)
Lemma base_mpolyC_support_zero (c : F) (u : 'X_{1..n}) :
  u \in msupp (c%:MP : Coeff) -> u = 0%MM.
Proof.
rewrite msuppC; case: eqP=> _.
- by rewrite in_nil.
- by rewrite mem_seq1=> /eqP.
Qed.

Lemma complete_homogeneous_seq_support_bound
    (xs : seq Ambient) r (pivot : 'I_n)
    (hxs : forall x, x \in xs -> exists i : 'I_n,
      x = GC.root_x F n i /\ (i <= pivot)%N)
    u (hu : u \in msupp (GC.complete_homogeneous_seq xs r))
    (j : 'I_n) (hpj : (pivot < j)%N) :
  u j = 0%N.
Proof.
elim: xs r hxs u hu=> [|x xs ih] r hxs u /=.
- move=> hu0.
  case hr: (r == 0) in hu0.
  + move: hu0; rewrite /= msupp1 mem_seq1=> /eqP ->.
    by rewrite mnm0E.
  + by move: hu0; rewrite /= msupp0 in_nil.
- move/msupp_sum_le/flattenP=> [s].
  move/mapP=> [i _ ->] hu.
  move/msuppM_le: hu=> /allpairsP [[u1 u2]] [hu1 hu2 ->].
  have [ix [hx hix]] := hxs x (mem_head x xs).
  rewrite hx /GC.root_x mpolyXn in hu1.
  move/mem_msuppXP: hu1=> <-.
  have hixj : (ix < j)%N := leq_ltn_trans hix hpj.
  have htail : u2 j = 0%N.
    apply: (ih (r - (i : nat))%N).
    + move=> y hy.
      apply: hxs.
      by rewrite in_cons hy orbT.
    + exact: hu2.
  rewrite mnmDE mulmnE mnm1E eqE /=.
  by rewrite (ltn_eqF hixj) mul0n htail add0n.
Qed.

Lemma prefix_index_le_pivot (k : 'I_n) (j : 'I_(n - k)) :
  (GC.prefix_index k j <= OI.displayed_pivot n k)%N.
Proof.
rewrite /GC.prefix_index /GC.suffix_total_eq
  /OI.displayed_pivot /=.
pose jj : nat := j.
change (jj <= (n - k.+1)%N)%N.
have hk : ((n - k.+1)%N).+1 = (n - (k : nat))%N :=
  subnSK (ltn_ord k).
have hj : (jj < (n - (k : nat))%N)%N := ltn_ord j.
move: hj.
by rewrite -hk ltnS.
Qed.

Lemma conventional_prefix_h_support_bound (k : 'I_n) r u
    (hu : u \in msupp (GC.conventional_prefix_h F n k r))
    (j : 'I_n) (hkj : (OI.displayed_pivot n k < j)%N) :
  u j = 0%N.
Proof.
apply: (complete_homogeneous_seq_support_bound
  (pivot := OI.displayed_pivot n k)).
- move=> x.
  rewrite /GC.prefix_root_tuple=> hx.
  move/mapP: hx=> [i _ ->].
  exists (GC.prefix_index k i); split=> //.
  exact: prefix_index_le_pivot.
- exact: hu.
- exact: hkj.
Qed.

(** It is useful below to retain the actual list of root indices, rather
    than only the numerical upper bound on them. *)
Definition root_index_sequence (idxs : seq 'I_n) : seq Ambient :=
  [seq GC.root_x F n i | i <- idxs].

Lemma complete_homogeneous_root_sequence_support_absent
    (idxs : seq 'I_n) r u
    (hu : u \in msupp
      (GC.complete_homogeneous_seq (root_index_sequence idxs) r))
    (j : 'I_n) (hj : j \notin idxs) :
  u j = 0%N.
Proof.
elim: idxs r u hu hj=> [|i idxs ih] r u /=.
- move=> hu0 _.
  case hr: (r == 0) in hu0.
  + move: hu0; rewrite /= msupp1 mem_seq1=> /eqP ->.
    by rewrite mnm0E.
  + by move: hu0; rewrite /= msupp0 in_nil.
- move/msupp_sum_le/flattenP=> [s].
  move/mapP=> [a _ ->] hu.
  move/msuppM_le: hu=> /allpairsP [[u1 u2]] [hu1 hu2 ->].
  rewrite /GC.root_x mpolyXn in hu1.
  move/mem_msuppXP: hu1=> <-.
  rewrite in_cons negb_or=> /andP [hji hjis].
  have htail : u2 j = 0%N.
    apply: ih.
    + exact: hu2.
    + exact: hjis.
  have hij : i != j by rewrite eq_sym.
  by rewrite mnmDE mulmnE mnm1E (negbTE hij) mul0n htail add0n.
Qed.

Lemma complete_homogeneous_root_sequence_absent_coefficient
    (idxs : seq 'I_n) p r :
  p \notin idxs -> (0 < r)%N ->
  ((GC.complete_homogeneous_seq (root_index_sequence idxs) r)
      @_ (U_(p) *+ r)%MM) = 0.
Proof.
move=> hp hr; apply/eqP; rewrite mcoeff_eq0; apply/negP=> hu.
have hcoord := complete_homogeneous_root_sequence_support_absent hu hp.
have hr0 : r = 0%N.
  move: hcoord.
  by rewrite mulmnE mnm1E eqxx mul1n.
by move: hr; rewrite hr0.
Qed.

(** Multiplication by a root variable shifts the corresponding pure power
    by one.  A different root variable cannot contribute to that pure
    coefficient. *)
Lemma mcoeff_root_x_mul_pure_same
    (p : 'I_n) (q : Ambient) (r : nat) :
  ((GC.root_x F n p * q) @_ (U_(p) *+ r.+1)%MM) =
    q @_ (U_(p) *+ r)%MM.
Proof.
rewrite /GC.root_x mulrC mulmS.
exact: mcoeffMX.
Qed.

Lemma mcoeff_root_x_mul_pure_ne
    (i p : 'I_n) (q : Ambient) (r : nat) :
  i != p ->
  ((GC.root_x F n i * q) @_ (U_(p) *+ r.+1)%MM) = 0.
Proof.
move=> hip; apply/eqP; rewrite mcoeff_eq0; apply/negP=> hu.
move/msuppM_le: hu=> /allpairsP [[u1 u2]] [hu1 hu2 heq].
rewrite /GC.root_x in hu1.
move/mem_msuppXP: hu1=> hu1.
rewrite -hu1 in heq.
have hcoord := congr1 (fun u : 'X_{1..n} => u i) heq.
have hpi : p != i by rewrite eq_sym.
move: hcoord.
rewrite mulmnE mnm1E (negbTE hpi) mul0n.
rewrite mnmDE mnm1E eqxx.
by case: (u2 i).
Qed.

(** Every pure power of a root which occurs in a duplicate-free root list
    has coefficient one in the corresponding complete homogeneous
    polynomial.  The proof follows the defining recurrence, so no closed
    coefficient formula is assumed. *)
Lemma complete_homogeneous_root_sequence_pure_coefficient
    (idxs : seq 'I_n) (p : 'I_n) r :
  uniq idxs -> p \in idxs ->
  ((GC.complete_homogeneous_seq (root_index_sequence idxs) r)
      @_ (U_(p) *+ r)%MM) = (1%R : Coeff).
Proof.
elim: idxs p r=> [|i idxs ih] p r //=.
move=> /andP [hi his].
case hip: (i == p).
- move/eqP: hip=> hip _; subst i.
  elim: r=> [|r ihr].
  + have h0 :
        GC.complete_homogeneous_seq (root_index_sequence (p :: idxs)) 0 =
          (1%R : Ambient) :=
      @GC.complete_homogeneous_seq0 F n
        (root_index_sequence (p :: idxs)).
    change
      (mcoeff ((U_(p) *+ 0)%MM)
        (GC.complete_homogeneous_seq
          (root_index_sequence (p :: idxs)) 0) = (1%R : Coeff)).
    rewrite h0 mulm0n.
    change (((1%R : Ambient) @_ 0%MM) = (1%R : Coeff)).
    by rewrite mcoeff1 eqxx.
  + change
      (mcoeff ((U_(p) *+ r.+1)%MM)
        (GC.complete_homogeneous_seq
          (root_index_sequence (p :: idxs)) r.+1) = (1%R : Coeff)).
    rewrite (@GC.complete_homogeneous_seq_consS F n
      (GC.root_x F n p) (root_index_sequence idxs) r) mcoeffD.
    have habs :
        mcoeff ((U_(p) *+ r.+1)%MM)
          (GC.complete_homogeneous_seq (root_index_sequence idxs) r.+1) =
            (0%R : Coeff) :=
      complete_homogeneous_root_sequence_absent_coefficient hi (ltn0Sn r).
    rewrite habs.
    rewrite mcoeff_root_x_mul_pure_same ihr add0r.
    exact: erefl.
- have hpi : p != i by rewrite eq_sym hip.
  move=> hp; move: hp; rewrite in_cons (negbTE hpi) orFb=> hp.
  case: r=> [|r].
  + have h0 :
        GC.complete_homogeneous_seq (root_index_sequence (i :: idxs)) 0 =
          (1%R : Ambient) :=
      @GC.complete_homogeneous_seq0 F n
        (root_index_sequence (i :: idxs)).
    change
      (mcoeff ((U_(p) *+ 0)%MM)
        (GC.complete_homogeneous_seq
          (root_index_sequence (i :: idxs)) 0) = (1%R : Coeff)).
    rewrite h0 mulm0n.
    change (((1%R : Ambient) @_ 0%MM) = (1%R : Coeff)).
    by rewrite mcoeff1 eqxx.
  + change
      (mcoeff ((U_(p) *+ r.+1)%MM)
        (GC.complete_homogeneous_seq
          (root_index_sequence (i :: idxs)) r.+1) = (1%R : Coeff)).
    rewrite (@GC.complete_homogeneous_seq_consS F n
      (GC.root_x F n i) (root_index_sequence idxs) r) mcoeffD.
    have hne :
        mcoeff ((U_(p) *+ r.+1)%MM)
          (GC.root_x F n i *
            GC.complete_homogeneous_seq
              (root_index_sequence (i :: idxs)) r) = (0%R : Coeff).
      apply: mcoeff_root_x_mul_pure_ne.
      by rewrite hip.
    by rewrite (ih p r.+1 his hp) hne addr0.
Qed.

Definition prefix_index_sequence (k : 'I_n) : seq 'I_n :=
  [seq GC.prefix_index k j | j : 'I_(n - k)].

Lemma prefix_index_injective (k : 'I_n) :
  injective (GC.prefix_index k).
Proof.
move=> i j hij; apply/val_inj.
move: (congr1 val hij).
by rewrite /GC.prefix_index /=.
Qed.

Lemma prefix_index_sequence_uniq (k : 'I_n) :
  uniq (prefix_index_sequence k).
Proof.
rewrite /prefix_index_sequence map_inj_uniq ?enum_uniq //.
exact: prefix_index_injective.
Qed.

Lemma prefix_last_index_bound (k : 'I_n) :
  ((n - k.+1)%N < (n - (k : nat))%N)%N.
Proof.
have hk : ((n - k.+1)%N).+1 = (n - (k : nat))%N :=
  subnSK (ltn_ord k).
rewrite -hk.
exact: ltnSn _.
Qed.

Definition prefix_last_index (k : 'I_n) : 'I_((n - k)%N) :=
  @Ordinal ((n - (k : nat))%N) ((n - k.+1)%N)
    (prefix_last_index_bound k).

Lemma prefix_index_last (k : 'I_n) :
  GC.prefix_index k (prefix_last_index k) =
    OI.displayed_pivot n k.
Proof.
apply/val_inj.
rewrite /GC.prefix_index /GC.suffix_total_eq
  /OI.displayed_pivot /prefix_last_index /=.
exact: erefl.
Qed.

Lemma displayed_pivot_mem_prefix_index_sequence (k : 'I_n) :
  OI.displayed_pivot n k \in prefix_index_sequence k.
Proof.
apply/mapP; exists (prefix_last_index k); first exact: mem_enum.
symmetry.
exact: prefix_index_last.
Qed.

Lemma prefix_root_tupleE (k : 'I_n) :
  val (GC.prefix_root_tuple F n k) =
    root_index_sequence (prefix_index_sequence k).
Proof.
rewrite /GC.prefix_root_tuple /root_index_sequence
  /prefix_index_sequence /mktuple /= ?val_ord_tuple -map_comp.
rewrite -map_comp /=.
rewrite /comp.
by rewrite enumT.
Qed.

Lemma conventional_prefix_h_pure_pivot_coefficient (k : 'I_n) r :
  ((GC.conventional_prefix_h F n k r)
      @_ (U_(OI.displayed_pivot n k) *+ r)%MM) = (1%R : Coeff).
Proof.
rewrite /GC.conventional_prefix_h prefix_root_tupleE.
apply: complete_homogeneous_root_sequence_pure_coefficient.
- exact: prefix_index_sequence_uniq.
- exact: displayed_pivot_mem_prefix_index_sequence.
Qed.

(** Erase all positive-degree formal-coefficient monomials.  Constant-term
    extraction and the constant-polynomial embedding are ring morphisms, so
    their composite is an honest coefficient-ring endomorphism. *)
Definition ground_coefficient_projection (c : Coeff) : Coeff :=
  (c @_ 0%MM)%:MP.

Lemma ground_coefficient_projection_is_additive :
  additive ground_coefficient_projection.
Proof.
move=> c d.
by rewrite /ground_coefficient_projection mcoeffB rmorphB.
Qed.

HB.instance Definition _ :=
  GRing.isAdditive.Build Coeff Coeff ground_coefficient_projection
    ground_coefficient_projection_is_additive.

Lemma ground_coefficient_projection_is_multiplicative :
  multiplicative ground_coefficient_projection.
Proof.
split=> [c d|].
- rewrite /ground_coefficient_projection.
  have hmul :
      ((c * d) @_ 0%MM) =
        (((c @_ 0%MM) * (d @_ 0%MM))%R : F) :=
    (mcoeff0_is_multiplicative n F).1 c d.
  rewrite hmul.
  exact: mpolyCM.
- rewrite /ground_coefficient_projection.
  have hone : ((1%R : Coeff) @_ 0%MM) = (1%R : F) :=
    (mcoeff0_is_multiplicative n F).2.
  rewrite hone.
  exact: mpolyC1.
Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build Coeff Coeff ground_coefficient_projection
    ground_coefficient_projection_is_multiplicative.

Definition outer_coefficients_ground (p : Ambient) : Prop :=
  map_mpoly ground_coefficient_projection p = p.

Lemma complete_homogeneous_root_sequence_ground
    (idxs : seq 'I_n) r :
  outer_coefficients_ground
    (GC.complete_homogeneous_seq (root_index_sequence idxs) r).
Proof.
elim: idxs r=> [|i idxs ih] r /=.
- by rewrite /outer_coefficients_ground rmorph_nat.
- rewrite /outer_coefficients_ground rmorph_sum.
  apply: eq_bigr=> a _.
  change
    (map_mpoly ground_coefficient_projection
      ((GC.root_x F n i ^+ (a : nat))%R *
        GC.complete_homogeneous_seq (root_index_sequence idxs)
          (r - (a : nat))%N)%R =
    ((GC.root_x F n i ^+ (a : nat))%R *
      GC.complete_homogeneous_seq (root_index_sequence idxs)
        (r - (a : nat))%N)%R).
  have hpow :
      map_mpoly ground_coefficient_projection
        (GC.root_x F n i ^+ (a : nat))%R =
      (GC.root_x F n i ^+ (a : nat))%R.
    by rewrite /GC.root_x !mpolyXn map_mpolyX.
  have htail := ih (r - (a : nat))%N.
  rewrite /outer_coefficients_ground in htail.
  have hmul :
      map_mpoly ground_coefficient_projection
        ((GC.root_x F n i ^+ (a : nat))%R *
          GC.complete_homogeneous_seq (root_index_sequence idxs)
            (r - (a : nat))%N)%R =
      (map_mpoly ground_coefficient_projection
          (GC.root_x F n i ^+ (a : nat))%R *
        map_mpoly ground_coefficient_projection
          (GC.complete_homogeneous_seq (root_index_sequence idxs)
            (r - (a : nat))%N))%R :=
    (map_mpoly_is_multiplicative n ground_coefficient_projection).1 _ _.
  by rewrite hmul hpow htail.
Qed.

Lemma conventional_prefix_h_ground (k : 'I_n) r :
  outer_coefficients_ground (GC.conventional_prefix_h F n k r).
Proof.
rewrite /GC.conventional_prefix_h prefix_root_tupleE.
exact: complete_homogeneous_root_sequence_ground.
Qed.

Lemma conventional_prefix_h_inner_support_zero
    (k : 'I_n) r u v :
  OI.combined_support (GC.conventional_prefix_h F n k r) (u, v) ->
  v = 0%MM.
Proof.
move=> huv.
have hv : v \in msupp ((GC.conventional_prefix_h F n k r) @_ u).
  rewrite mcoeff_msupp; apply/negP=> /eqP hv0.
  apply: huv.
  by rewrite /OI.combined_coefficient hv0.
have hfix := congr1 (fun p : Ambient => p @_ u)
  (conventional_prefix_h_ground k r).
rewrite mcoeff_map_mpoly in hfix.
move: hv; rewrite -hfix /ground_coefficient_projection.
exact: base_mpolyC_support_zero.
Qed.

End LiteralCompleteHomogeneousSupport.

(** * Whole-family support calculation *)

Section LiteralDisplayedFamilySupport.

Variables (F : fieldType) (n : nat).

Local Notation Coeff := {mpoly F[n]}.
Local Notation Ambient := {mpoly Coeff[n]}.
Local Notation Monomial := (OI.combined_monomial n).

Lemma mpolyC_outer_dhomog0 (c : Coeff) :
  (c%:MP : Ambient) \is 0.-homog.
Proof.
apply/dhomogP=> u /mpolyC_support_zero ->.
exact: mdeg0.
Qed.

Lemma concrete_formal_e_outer_dhomog0 r :
  GC.concrete_formal_e F n r \is 0.-homog.
Proof.
case: r=> [|r].
- exact: dhomog1.
- rewrite /GC.concrete_formal_e /=.
  case: insub=> [i|].
  + exact: mpolyC_outer_dhomog0.
  + exact: dhomog0.
Qed.

Lemma signed_formal_e_factor_outer_dhomog0 (r : nat) :
  (((-1 : Ambient) ^+ (r : nat))%R * GC.concrete_formal_e F n r)%R
    \is 0.-homog.
Proof.
have hminus : (-1 : Ambient) \is 0.-homog.
  rewrite dhomogN.
  exact: dhomog1.
have hpow := dhomogMn r hminus.
have hformal := concrete_formal_e_outer_dhomog0 r.
move: (dhomogM hpow hformal).
by rewrite mul0n add0n.
Qed.

Lemma signed_formal_e_factor_support_zero (r : nat) u :
  u \in msupp
      (((-1 : Ambient) ^+ (r : nat))%R *
        GC.concrete_formal_e F n r)%R ->
  u = 0%MM.
Proof.
move=> hu.
have hdeg := dhomog_mf
  (signed_formal_e_factor_outer_dhomog0 r) hu.
by apply/eqP; rewrite -mdeg_eq0 hdeg eqxx.
Qed.

Lemma combined_support_outer_support (p : Ambient) u v :
  OI.combined_support p (u, v) -> u \in msupp p.
Proof.
move=> huv; rewrite mcoeff_msupp; apply/negP=> /eqP hu0.
apply: huv.
by rewrite /OI.combined_coefficient hu0 mcoeff0.
Qed.

(** Every root monomial in the printed relation has degree at most [k+1]
    and uses no root variable above its displayed pivot. *)
Lemma literal_displayed_family_outer_support_shape
    (k : 'I_n) u :
  u \in msupp (OI.literal_displayed_family F n k) ->
  (mdeg u <= k.+1)%N /\
  (forall j : 'I_n,
    (OI.displayed_pivot n k < j)%N -> u j = 0%N).
Proof.
rewrite /OI.literal_displayed_family
  /GC.conventional_printed_displayed_J /GI.printed_displayed_J.
move/msupp_sum_le/flattenP=> [s].
move/mapP=> [r _ ->] hu.
move/msuppM_le: hu=> /allpairsP [[u1 u2]] [hu1 hu2 ->].
have hu1zero := signed_formal_e_factor_support_zero hu1.
rewrite hu1zero add0m.
split.
- rewrite (conventional_prefix_h_support_degree hu2).
  exact: leq_subr.
- move=> j hkj.
  exact: (@conventional_prefix_h_support_bound F n k
    (k.+1 - (r : nat))%N (u1, u2).2 hu2 j hkj).
Qed.

Lemma literal_displayed_family_combined_support_shape
    (k : 'I_n) (a : Monomial) :
  OI.combined_support (OI.literal_displayed_family F n k) a ->
  (mdeg a.1 <= k.+1)%N /\
  (forall j : 'I_n,
    (OI.displayed_pivot n k < j)%N -> a.1 j = 0%N).
Proof.
move=> ha.
exact: literal_displayed_family_outer_support_shape
  (combined_support_outer_support ha).
Qed.

Lemma printed_summand_root_dhomog (k : 'I_n) (r : nat) :
  (((((-1 : Ambient) ^+ r)%R * GC.concrete_formal_e F n r)%R *
      GC.conventional_prefix_h F n k (k.+1 - r)%N)%R)
    \is ((k.+1 - r)%N).-homog.
Proof.
have hfactor := signed_formal_e_factor_outer_dhomog0 r.
have hprefix := conventional_prefix_h_dhomog F k (k.+1 - r)%N.
move: (dhomogM hfactor hprefix).
by rewrite add0n.
Qed.

(** At the top root degree only the [r=0] summand survives. *)
Lemma literal_displayed_family_outer_coefficient_top
    (k : 'I_n) u :
  mdeg u = k.+1 ->
  ((OI.literal_displayed_family F n k) @_ u) =
    ((GC.conventional_prefix_h F n k k.+1) @_ u).
Proof.
move=> hdegree.
rewrite /OI.literal_displayed_family
  /GC.conventional_printed_displayed_J /GI.printed_displayed_J
  raddf_sum (bigD1 (0 : 'I_k.+2)) //=.
rewrite expr0 !mul1r.
rewrite big1 ?addr0 // => r hr0.
have hhom := printed_summand_root_dhomog k r.
apply: (@dhomog_nemf_coeff n Coeff mdeg _ _ u hhom).
apply/negP=> /eqP hsame.
have hrpos : (0 < r)%N by rewrite lt0n.
have hlt : (k.+1 - r < k.+1)%N.
  by rewrite ltn_subrL hrpos ltn0Sn.
have heq : k.+1 = (k.+1 - r)%N := etrans (esym hdegree) hsame.
by move: hlt; rewrite -heq ltnn.
Qed.

Lemma literal_displayed_family_top_inner_support_zero
    (k : 'I_n) (a : Monomial) :
  OI.combined_support (OI.literal_displayed_family F n k) a ->
  mdeg a.1 = k.+1 ->
  a.2 = 0%MM.
Proof.
move=> ha hdegree.
have htop :
    ((OI.literal_displayed_family F n k) @_ a.1) =
      ((GC.conventional_prefix_h F n k k.+1) @_ a.1) :=
  literal_displayed_family_outer_coefficient_top hdegree.
apply: (@conventional_prefix_h_inner_support_zero F n
  k k.+1 a.1 a.2).
rewrite /OI.combined_support /OI.combined_coefficient.
move: ha.
by rewrite /OI.combined_support /OI.combined_coefficient
  htop.
Qed.

Lemma literal_displayed_family_leading_root_coefficient (k : 'I_n) :
  ((OI.literal_displayed_family F n k)
      @_ (U_(OI.displayed_pivot n k) *+ k.+1)%MM) = (1%R : Coeff).
Proof.
rewrite literal_displayed_family_outer_coefficient_top.
- exact: conventional_prefix_h_pure_pivot_coefficient.
- by rewrite mdegMn mdeg1 mul1n.
Qed.

Lemma literal_displayed_family_monic (k : 'I_n) :
  OI.combined_coefficient (OI.literal_displayed_family F n k)
      (OI.displayed_leading_monomial n k) = (1%R : F).
Proof.
by rewrite /OI.combined_coefficient /OI.displayed_leading_monomial /=
  literal_displayed_family_leading_root_coefficient mcoeff1 eqxx.
Qed.

End LiteralDisplayedFamilySupport.

(** * Dominance for every paper order *)

Section LiteralDisplayedFamilyOrder.

Variables (F : fieldType) (n : nat).

Local Notation Coeff := {mpoly F[n]}.
Local Notation Ambient := {mpoly Coeff[n]}.
Local Notation Monomial := (OI.combined_monomial n).

Definition combined_root_embedding (u : 'X_{1..n}) : Monomial :=
  (u, 0%MM).

Lemma combined_addC (a b : Monomial) :
  OI.combined_add a b = OI.combined_add b a.
Proof.
case: a=> [a1 a2]; case: b=> [b1 b2].
rewrite /OI.combined_add /=.
have h1 : (a1 + b1)%MM = (b1 + a1)%MM := addmC _ _.
have h2 : (a2 + b2)%MM = (b2 + a2)%MM := addmC _ _.
by rewrite h1 h2.
Qed.

Lemma amo_add_mono
    (O : OI.admissible_monomial_order n) a b c d :
  OI.amo_le O a b -> OI.amo_le O c d ->
  OI.amo_le O (OI.combined_add a c) (OI.combined_add b d).
Proof.
move=> hab hcd.
have habc := (OI.amo_add_compat O a b c).1 hab.
have hcdb := (OI.amo_add_compat O c d b).1 hcd.
rewrite [OI.combined_add c b]combined_addC
  [OI.combined_add d b]combined_addC in hcdb.
exact: OI.amo_le_trans habc hcdb.
Qed.

Lemma paper_root_variable_le
    (O : OI.admissible_monomial_order n)
    (H : OI.paper_order_hypotheses O) (i p : 'I_n) :
  (i <= p)%N ->
  OI.amo_le O (OI.combined_root_variable n i)
    (OI.combined_root_variable n p).
Proof.
rewrite leq_eqVlt=> /orP [/eqP hip|hip].
- have hipord : i = p := val_inj hip.
  subst p.
  exact: OI.amo_le_refl O _.
- exact: (OI.poh_root_variables_strict H hip).1.
Qed.

Lemma paper_root_variable_power_le
    (O : OI.admissible_monomial_order n)
    (H : OI.paper_order_hypotheses O) (i p : 'I_n) c :
  (i <= p)%N ->
  OI.amo_le O
    (combined_root_embedding (U_(i) *+ c)%MM)
    (combined_root_embedding (U_(p) *+ c)%MM).
Proof.
move=> hip; elim: c=> [|c ih].
- exact: OI.amo_le_refl O _.
- rewrite !mulmSr.
  have hstep := amo_add_mono ih (paper_root_variable_le H hip).
  move: hstep.
  by rewrite /OI.combined_add /combined_root_embedding
    /OI.combined_root_variable /= !add0m.
Qed.

Lemma paper_root_sum_le_pivot
    (O : OI.admissible_monomial_order n)
    (H : OI.paper_order_hypotheses O)
    (p : 'I_n) (u : 'X_{1..n}) (s : seq 'I_n) :
  (forall i : 'I_n, i \in s -> u i != 0 -> (i <= p)%N) ->
  OI.amo_le O
    (combined_root_embedding
      (\sum_(i <- s) (U_(i) *+ u i))%MM)
    (combined_root_embedding
      (\sum_(i <- s) (U_(p) *+ u i))%MM).
Proof.
elim: s=> [|i s ih] hsupport /=.
- rewrite !big_nil.
  exact: OI.amo_le_refl O _.
- have hhead : OI.amo_le O
      (combined_root_embedding (U_(i) *+ u i)%MM)
      (combined_root_embedding (U_(p) *+ u i)%MM).
    case hi0: (u i == 0).
    + move/eqP: hi0=> hi0; rewrite hi0 !mulm0n.
      exact: OI.amo_le_refl O _.
    + apply: (paper_root_variable_power_le H (u i)).
      have hii : i \in i :: s := mem_head i s.
      have hi0n : u i != 0 by rewrite hi0.
      exact: hsupport i hii hi0n.
  have htail : OI.amo_le O
      (combined_root_embedding
        (\sum_(j <- s) (U_(j) *+ u j))%MM)
      (combined_root_embedding
        (\sum_(j <- s) (U_(p) *+ u j))%MM).
    apply: ih=> j hjs hj0.
    have hjs' : j \in i :: s by rewrite in_cons hjs orbT.
    exact: hsupport j hjs' hj0.
  have hstep := amo_add_mono hhead htail.
  move: hstep.
  by rewrite !big_cons /OI.combined_add /combined_root_embedding /= !add0m.
Qed.

Lemma root_pivot_sumE (p : 'I_n) (u : 'X_{1..n}) :
  (\sum_i (U_(p) *+ u i))%MM = (U_(p) *+ mdeg u)%MM.
Proof.
apply/mnmP=> j.
rewrite mnm_sumE mulmnE mdegE big_distrr.
apply: eq_bigr=> i _.
by rewrite mulmnE mnm1E.
Qed.

(** Coq counterpart of Lean's [rootMonomial_le_purePivot]. *)
Lemma root_monomial_le_pure_pivot
    (O : OI.admissible_monomial_order n)
    (H : OI.paper_order_hypotheses O)
    (p : 'I_n) (u : 'X_{1..n}) :
  (forall i : 'I_n, u i != 0 -> (i <= p)%N) ->
  OI.amo_le O (combined_root_embedding u)
    (combined_root_embedding (U_(p) *+ mdeg u)%MM).
Proof.
move=> hsupport.
have hsum := paper_root_sum_le_pivot (p := p) (u := u)
  (s := enum 'I_n) H
  (fun i _ => hsupport i).
move: hsum.
rewrite !big_enum.
by rewrite -(multinomUE_id u) root_pivot_sumE.
Qed.

Lemma literal_displayed_family_leading
    (O : OI.admissible_monomial_order n)
    (H : OI.paper_order_hypotheses O) (k : 'I_n) :
  OI.is_leading_monomial O (OI.literal_displayed_family F n k)
    (OI.displayed_leading_monomial n k).
Proof.
split.
- rewrite /OI.combined_support literal_displayed_family_monic.
  move=> hone.
  by move: (@oner_neq0 F); rewrite hone eqxx.
- move=> [u v] huv hne.
  have [hdegree hbound] :=
    literal_displayed_family_combined_support_shape huv.
  case htop: (mdeg u == k.+1).
  + move/eqP: htop=> htop.
    have hvzero : v = 0%MM :=
      literal_displayed_family_top_inner_support_zero huv htop.
    rewrite hvzero in hne *.
    have hsupport i (hi : u i != 0) :
        (i <= OI.displayed_pivot n k)%N.
      rewrite leqNgt; apply/negP=> hgt.
      have hzero := hbound i hgt.
      by move: hi; rewrite hzero eqxx.
    have hle := root_monomial_le_pure_pivot
      (p := OI.displayed_pivot n k) (u := u) H hsupport.
    rewrite htop in hle.
    rewrite /OI.displayed_leading_monomial /=.
    split; first exact: hle.
    move=> heq; apply: hne.
    exact: heq.
  + have hlt : (mdeg u < k.+1)%N.
      by rewrite ltn_neqAle htop hdegree.
    have hdegree_lt :
        (OI.combined_root_degree (u, v) <
          OI.combined_root_degree (OI.displayed_leading_monomial n k))%N.
      by rewrite /OI.combined_root_degree
        /OI.displayed_leading_monomial /= mdegMn mdeg1 mul1n.
    exact: (@OI.poh_root_degree_primary n O H (u, v)
      (OI.displayed_leading_monomial n k) hdegree_lt).
Qed.

End LiteralDisplayedFamilyOrder.

(** * Reduced tails *)

Section LiteralDisplayedReducedTails.

Variables (F : fieldType) (n : nat).

Local Notation Coeff := {mpoly F[n]}.
Local Notation Ambient := {mpoly Coeff[n]}.
Local Notation Monomial := (OI.combined_monomial n).

Lemma displayed_pivot_strict_reverse (i j : 'I_n) :
  (i < j)%N ->
  (OI.displayed_pivot n j < OI.displayed_pivot n i)%N.
Proof.
move=> hij.
rewrite /OI.displayed_pivot /=.
have hj : (j.+1 <= n)%N := ltn_ord j.
by rewrite (ltn_sub2lE (m := n) (p := j.+1) i.+1 hj) ltnS.
Qed.

Lemma support_combined_monomial_coefficient_same a :
  OI.combined_coefficient
    (OI.combined_monomial_polynomial F n a) a = 1%R.
Proof.
case: a=> [u v].
by rewrite /OI.combined_coefficient
  /OI.combined_monomial_polynomial /= mcoeffZ mcoeffX eqxx
  mulr1 mcoeffX eqxx.
Qed.

Lemma support_combined_monomial_support_single a b :
  OI.combined_support
      (OI.combined_monomial_polynomial F n a) b -> b = a.
Proof.
case: a=> [u v]; case: b=> [u' v'] /=.
rewrite /OI.combined_support /OI.combined_coefficient
  /OI.combined_monomial_polynomial /= mcoeffZ mcoeffX.
case hu: (u == u').
- move/eqP: hu=> ->.
  rewrite mulr1 mcoeffX.
  case hv: (v == v').
  + by move/eqP: hv=> ->.
  + by rewrite /=.
- by rewrite /= mulr0 mcoeff0.
Qed.

Lemma support_combined_coefficientB (p q : Ambient) (a : Monomial) :
  OI.combined_coefficient (p - q) a =
    OI.combined_coefficient p a - OI.combined_coefficient q a.
Proof.
case: a=> [u v].
by rewrite /OI.combined_coefficient /= !mcoeffB.
Qed.

Lemma support_combined_supportB_cases (p q : Ambient) (a : Monomial) :
  OI.combined_support (p - q) a ->
  OI.combined_support p a \/ OI.combined_support q a.
Proof.
move=> ha.
case hp0: (OI.combined_coefficient p a == 0).
- right; move=> hq0; apply: ha.
  rewrite /OI.combined_support support_combined_coefficientB
    (eqP hp0) hq0 subrr.
  exact: erefl.
- left; move=> hpz.
  by move: hp0; rewrite hpz eqxx.
Qed.

Lemma literal_displayed_tail_not_leading_support (k : 'I_n) :
  ~ OI.combined_support (OI.literal_displayed_tail F n k)
      (OI.displayed_leading_monomial n k).
Proof.
move=> hsupport; apply: hsupport.
rewrite /OI.literal_displayed_tail support_combined_coefficientB
  literal_displayed_family_monic
  support_combined_monomial_coefficient_same subrr.
exact: erefl.
Qed.

Lemma literal_displayed_tail_support_family (k : 'I_n) a :
  OI.combined_support (OI.literal_displayed_tail F n k) a ->
  OI.combined_support (OI.literal_displayed_family F n k) a /\
  a <> OI.displayed_leading_monomial n k.
Proof.
move=> ha.
case: (support_combined_supportB_cases ha)=> [hfamily|hmono].
- split=> // heq; subst a.
  exact: literal_displayed_tail_not_leading_support ha.
- have heq := support_combined_monomial_support_single hmono.
  subst a.
  exact: False_rect _ (literal_displayed_tail_not_leading_support ha).
Qed.

Lemma multinom_eq_pure_of_le_degree
    (u : 'X_{1..n}) (p : 'I_n) d :
  ((U_(p) *+ d)%MM <= u)%MM -> (mdeg u <= d)%N ->
  u = (U_(p) *+ d)%MM.
Proof.
move=> hdiv hdegree.
have hsplit := submK hdiv.
have hdegree_split := congr1 mdeg hsplit.
rewrite mdegD mdegMn mdeg1 mul1n in hdegree_split.
  have hres_le : (mdeg (u - (U_(p) *+ d)%MM) <= 0)%N.
  move: hdegree.
  rewrite -hdegree_split -[d]add0n leq_add2r.
  exact.
have hres : (u - (U_(p) *+ d)%MM)%MM = 0%MM.
  apply/eqP; rewrite -mdeg_eq0.
  by rewrite eqn_leq hres_le leq0n.
move: hsplit; rewrite hres add0m=> hpure.
exact: esym hpure.
Qed.

Lemma literal_displayed_tail_not_divisible
    (k : 'I_n) (a : Monomial) :
  OI.combined_support (OI.literal_displayed_tail F n k) a ->
  forall j : 'I_n,
    ~ OI.combined_divides (OI.displayed_leading_monomial n j) a.
Proof.
case: a=> [u v]; move=> ha j hdiv.
have [hfamily hne] := literal_displayed_tail_support_family ha.
have [hdegree hbound] :=
  literal_displayed_family_combined_support_shape hfamily.
move/andP: hdiv=> [hroot _].
have hpivot := mnm_lepP hroot (OI.displayed_pivot n j).
rewrite /OI.displayed_leading_monomial /=
  mulmnE mnm1E eqxx mul1n in hpivot.
case hjk: (j < k)%N.
- have hpivots := displayed_pivot_strict_reverse hjk.
  have hzero := hbound _ hpivots.
  by move: hpivot; rewrite hzero.
- have hkj : (k <= j)%N by rewrite leqNgt hjk.
  have hcoord_degree :
      (u (OI.displayed_pivot n j) <= mdeg u)%N.
    rewrite mdegE (bigD1 (OI.displayed_pivot n j)) //=.
    exact: leq_addr.
  have hjdegree : (j.+1 <= k.+1)%N :=
    leq_trans (leq_trans hpivot hcoord_degree) hdegree.
  have hjk' : (j <= k)%N := hjdegree.
  have hjeq : j = k.
    apply/val_inj; apply: anti_leq.
    by rewrite hjk' hkj.
  subst j.
  have hlower : (k.+1 <= mdeg u)%N :=
    leq_trans hpivot hcoord_degree.
  have htop : mdeg u = k.+1.
    apply: anti_leq.
    by rewrite hdegree hlower.
  have hroot_eq :
      u = (U_(OI.displayed_pivot n k) *+ k.+1)%MM :=
    multinom_eq_pure_of_le_degree hroot hdegree.
  have hcoeff_eq : v = 0%MM :=
    literal_displayed_family_top_inner_support_zero hfamily htop.
  apply: hne.
  by rewrite hroot_eq hcoeff_eq /OI.displayed_leading_monomial.
Qed.

Lemma literal_displayed_tail_standard (k : 'I_n) :
  OI.literal_standard F n (OI.literal_displayed_tail F n k).
Proof.
move=> a ha j.
exact: literal_displayed_tail_not_divisible ha j.
Qed.

End LiteralDisplayedReducedTails.

(** The support record is now a theorem of the literal displayed formula,
    rather than input supplied by a caller. *)
Theorem constructed_literal_order_support_data
    (F : fieldType) (n : nat)
    (O : OI.admissible_monomial_order n)
    (H : OI.paper_order_hypotheses O) :
  @literal_order_support_data F n O.
Proof.
constructor.
- exact: H.
- move=> k; exact: literal_displayed_family_monic k.
- move=> k; exact: literal_displayed_family_leading H k.
- move=> k; exact: literal_displayed_tail_standard k.
Qed.

(** * The all-degree, paper-oriented Artin staircase *)

Section PaperArtinBasis.

Variables (F : fieldType) (n : nat).

Local Notation Coeff := {mpoly F[n]}.
Local Notation Ambient := {mpoly Coeff[n]}.
Local Notation RootRing := {mpoly F[n]}.
Local Notation Monomial := (OI.combined_monomial n).
Local Notation SymmetricModule :=
  (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
    F n).
Local Notation ReverseArtin :=
  (FF.ffd_index
    (@AS.lazard_reverse_artin_finite_free_decomposition F n)).
Local Notation widen := (widen_ord (leqnSn _)).

(** The recursive Artin construction bounds the exponent of raw variable
    [i] by [i+1].  This is the all-degree replacement for the old quintic
    [vm_compute] table. *)
Lemma reverse_artin_exponent_coordinate_bound : forall m
    (a : FF.ffd_index
      (@AS.lazard_reverse_artin_finite_free_decomposition F m))
    (i : 'I_m),
  (@AS.lazard_reverse_artin_exponent F m a i < i.+1)%N.
Proof.
elim=> [a i|m ih [a j] i]; first by case: i.
case: (unliftP ord_max i)=> [q ->|->].
- have hlift : lift ord_max q = widen q.
    apply/val_inj.
    change ((lift ord_max q : nat) = (widen q : nat)).
    by rewrite lift_max.
  rewrite hlift /AS.lazard_reverse_artin_exponent /=
    mnmDE mnmwiden_widen mulmnE mnm1E eqE /=.
  rewrite (gtn_eqF (ltn_ord q)) mul0n addn0.
  exact: ih.
- rewrite /AS.lazard_reverse_artin_exponent /=
    mnmDE mnmwiden_ordmax mulmnE mnm1E eqxx mul1n add0n.
  exact: ltn_ord j.
Qed.

Lemma reverse_artin_exponent_injective : forall m,
  injective
    (@AS.lazard_reverse_artin_exponent F m).
Proof.
elim=> [a b _|m ih [a i] [b j] hab].
- by apply/val_inj; rewrite !ord1.
- have hij : i = j.
    apply/val_inj.
    move: (congr1 (fun u : 'X_{1..m.+1} => u ord_max) hab).
    rewrite /AS.lazard_reverse_artin_exponent /=
      !mnmDE !mnmwiden_ordmax !mulmnE !mnm1E !eqxx
      !mul1n !add0n.
    exact.
  subst j.
  have hab' : a = b.
    apply: ih; apply/mnmP=> q.
    move: (congr1 (fun u : 'X_{1..m.+1} => u (widen q)) hab).
    rewrite /AS.lazard_reverse_artin_exponent /=
      !mnmDE !mnmwiden_widen !mulmnE !mnm1E !eqE /=
      !(gtn_eqF (ltn_ord q)) !mul0n !addn0.
    exact.
  by subst b.
Qed.

Definition paper_reverse_perm : 'S_n := perm (@rev_ord_inj n).

Lemma paper_reverse_permE i :
  paper_reverse_perm i = rev_ord i.
Proof. by rewrite /paper_reverse_perm permE. Qed.

Lemma paper_reverse_permV :
  (paper_reverse_perm^-1)%g = paper_reverse_perm.
Proof.
apply: (mulIg paper_reverse_perm).
rewrite mulVg.
apply/permP=> i.
by rewrite perm1 permM !paper_reverse_permE rev_ordK.
Qed.

Lemma paper_reverse_perm_invE i :
  (paper_reverse_perm^-1)%g i = rev_ord i.
Proof. by rewrite paper_reverse_permV paper_reverse_permE. Qed.

Definition paper_artin_exponent (a : ReverseArtin) : 'X_{1..n} :=
  [multinom
    (@AS.lazard_reverse_artin_exponent F n a) (rev_ord i) | i < n].

Lemma paper_artin_exponent_standard a i :
  (paper_artin_exponent a i < n - i)%N.
Proof.
rewrite /paper_artin_exponent mnmE.
move: (reverse_artin_exponent_coordinate_bound a (rev_ord i)).
by rewrite /= (subnSK (ltn_ord i)).
Qed.

Lemma paper_artin_exponent_injective : injective paper_artin_exponent.
Proof.
move=> a b hab.
apply: reverse_artin_exponent_injective.
apply/mnmP=> i.
move: (congr1 (fun u : 'X_{1..n} => u (rev_ord i)) hab).
by rewrite /paper_artin_exponent !mnmE !rev_ordK.
Qed.

Definition paper_artin_index (a : ReverseArtin) : IM.artin_index n :=
  [ffun i : 'I_n => @Ordinal (n - i)%N (paper_artin_exponent a i)
    (paper_artin_exponent_standard a i)].

Lemma paper_artin_index_injective : injective paper_artin_index.
Proof.
move=> a b hab; apply: paper_artin_exponent_injective.
apply/mnmP=> i.
move: (congr1 (fun c : IM.artin_index n => (c i : nat)) hab).
by rewrite /paper_artin_index !ffunE.
Qed.

Lemma paper_artin_index_bijective : bijective paper_artin_index.
Proof.
apply: (inj_card_bij paper_artin_index_injective).
by rewrite IM.card_artin_index AS.lazard_reverse_artin_index_card.
Qed.

Definition artin_index_of_standard (u : 'X_{1..n})
    (hu : forall i : 'I_n, (u i < n - i)%N) : IM.artin_index n :=
  [ffun i : 'I_n => @Ordinal (n - i)%N (u i) (hu i)].

Lemma paper_artin_exponent_complete (u : 'X_{1..n})
    (hu : forall i : 'I_n, (u i < n - i)%N) :
  exists a : ReverseArtin, paper_artin_exponent a = u.
Proof.
pose b := artin_index_of_standard (u := u) hu.
have [g _ hsurj] := paper_artin_index_bijective.
exists (g b); apply/mnmP=> i.
move: (congr1 (fun c : IM.artin_index n => (c i : nat)) (hsurj b)).
by rewrite /paper_artin_index /b /artin_index_of_standard !ffunE.
Qed.

Definition paper_artin_basis (a : ReverseArtin) :
    SymmetricModule :=
  msym paper_reverse_perm
    (FF.ffd_basis
      (@AS.lazard_reverse_artin_finite_free_decomposition F n) a).

Lemma paper_artin_basisE a :
  paper_artin_basis a = 'X_[F, paper_artin_exponent a].
Proof.
rewrite /paper_artin_basis AS.lazard_reverse_artin_basisE msymX.
congr 'X_[_]; apply/mnmP=> i.
rewrite /paper_artin_exponent !mnmE paper_reverse_perm_invE.
exact: erefl.
Qed.

Lemma msym_sym_eval (s : 'S_n) (c : Coeff) :
  msym s (IM.sym_eval c) = IM.sym_eval c.
Proof.
have /issymP h := IM.sym_eval_symmetric c.
exact: h s.
Qed.

Lemma paper_artin_unreverse (c : Coeff) (a : ReverseArtin) :
  msym (paper_reverse_perm^-1)%g
    ((c *: paper_artin_basis a)%R) =
  (c *: (FF.ffd_basis
    (@AS.lazard_reverse_artin_finite_free_decomposition F n) a))%R.
Proof.
rewrite !SM.symmetric_scalarE /paper_artin_basis msymM
  msym_sym_eval -msymMm mulgV msym1m.
exact: erefl.
Qed.

(** Independence of the paper-oriented staircase is inherited from the
    recursive reverse Artin decomposition by undoing the reversal. *)
Lemma paper_artin_basis_independent (c : ReverseArtin -> Coeff) :
  (\sum_a ((c a) *: paper_artin_basis a)%R = 0) ->
  forall a, c a = 0.
Proof.
move=> hzero.
have hzero' := congr1 (msym (paper_reverse_perm^-1)%g) hzero.
rewrite msym0 raddf_sum in hzero'.
have hsumE :
    (\sum_a msym (paper_reverse_perm^-1)%g
      (((c a) *: paper_artin_basis a)%R)) =
    (\sum_a ((c a) *: (FF.ffd_basis
      (@AS.lazard_reverse_artin_finite_free_decomposition F n) a))%R).
  apply: eq_bigr=> a _.
  exact: paper_artin_unreverse.
have hzero'' :
    (\sum_a ((c a) *: (FF.ffd_basis
      (@AS.lazard_reverse_artin_finite_free_decomposition F n) a))%R) = 0.
  by rewrite -hsumE.
exact: (FF.ffd_basis_independent
  (D := @AS.lazard_reverse_artin_finite_free_decomposition F n) hzero'').
Qed.

Lemma mpoly_expansion_over_monomials
    (T : finType) (f : T -> 'X_{1..n})
    (finj : injective f) (p : Ambient)
    (hcover : forall u, u \in msupp p -> exists a, f a = u) :
  p = \sum_a ((p @_ (f a)) *: 'X_[Coeff, f a])%R.
Proof.
apply/mpolyP=> u; rewrite raddf_sum.
case hsu: (u \in msupp p).
- have [a ha] := hcover u hsu.
  rewrite (bigD1 a) //= mcoeffZ mcoeffX ha eqxx mulr1.
  rewrite big1 ?addr0 // => b hba.
  rewrite mcoeffZ mcoeffX.
  have hfb : f b != u.
    apply/negP=> /eqP hfb.
    have hba' : b = a.
      apply: finj.
      exact: etrans hfb (esym ha).
    by move: hba; rewrite hba' eqxx.
  by rewrite (negbTE hfb) mulr0.
- have hcoeff : p @_ u = 0.
    apply/eqP; by rewrite mcoeff_eq0 hsu.
  rewrite hcoeff big1 // => a _.
  change ((((p @_ (f a)) *: 'X_[Coeff, f a])%R) @_ u = 0).
  rewrite mcoeffZ mcoeffX.
  case hfa: (f a == u).
  + move/eqP: hfa=> ->; by rewrite hcoeff mul0r.
  + by rewrite /= mulr0.
Qed.

Definition paper_standard (p : Ambient) : Prop :=
  forall u, u \in msupp p ->
    forall i : 'I_n, (u i < n - i)%N.

Theorem paper_standard_expansion p :
  paper_standard p ->
  p = \sum_a ((p @_ (paper_artin_exponent a)) *:
    'X_[Coeff, paper_artin_exponent a])%R.
Proof.
move=> hp.
apply: (mpoly_expansion_over_monomials paper_artin_exponent_injective).
move=> u hu.
exact: paper_artin_exponent_complete (hp u hu).
Qed.

(** * Formal elementary-symmetric specialization *)

Definition formal_specialization (p : Ambient) : RootRing :=
  mmap (@IM.sym_eval F n) (fun i => ('X_i : RootRing)) p.

Lemma formal_specialization0 : formal_specialization 0 = 0.
Proof. exact: mmap0. Qed.

Lemma formal_specializationD :
  {morph formal_specialization : p q / p + q}.
Proof. exact: mmapD. Qed.

Lemma formal_specializationN :
  {morph formal_specialization : p / - p}.
Proof. exact: mmapN. Qed.

Lemma formal_specializationB :
  {morph formal_specialization : p q / p - q}.
Proof. exact: mmapB. Qed.

Lemma formal_specializationM :
  {morph formal_specialization : p q / (p * q)%R}.
Proof. exact: rmorphM. Qed.

Lemma formal_specialization_formal_e (i : 'I_n) :
  formal_specialization
      (GC.concrete_formal_e F n i.+1) =
    mesym n F i.+1.
Proof.
rewrite GC.concrete_formal_e_succ /formal_specialization.
rewrite (mmapC (fun i0 : 'I_n => ('X_i0 : RootRing))
  (IM.sym_eval (n := n)) ('X_i : Coeff)).
rewrite /IM.sym_eval /IM.elementary_symmetric_tuple.
change ((('X_i : RootRing) \mPo
  [tuple mesym n F j.+1 | j < n]) = mesym n F i.+1).
rewrite comp_mpolyXU.
by rewrite -tnth_nth tnth_mktuple.
Qed.

Lemma formal_specialization_mesym k :
  formal_specialization (mesym n Coeff k) = mesym n F k.
Proof.
rewrite /formal_specialization !mesymE raddf_sum.
apply: eq_bigr=> u _.
change (mmap (IM.sym_eval (n := n))
  (fun i : 'I_n => ('X_i : RootRing))
  ('X_[Coeff, mesym1 u]) = 'X_[F, mesym1 u]).
rewrite (mmapX (fun i : 'I_n => ('X_i : RootRing))
  (IM.sym_eval (n := n)) (mesym1 u)).
by rewrite mmap1_id.
Qed.

Lemma formal_specialization_vieta_generator (i : 'I_n) :
  formal_specialization (OI.literal_vieta_family F n i) = 0.
Proof.
rewrite /OI.literal_vieta_family /GC.concrete_vieta_relation
  /GI.vieta_relation /GC.concrete_sigma.
by rewrite formal_specializationB formal_specialization_mesym
  formal_specialization_formal_e subrr.
Qed.

Lemma formal_specialization_vieta_ideal_zero p :
  OI.literal_vieta_ideal F n p -> formal_specialization p = 0.
Proof.
move=> [c ->].
rewrite /formal_specialization raddf_sum.
apply: big1=> i _.
change (formal_specialization
  ((c i) * OI.literal_vieta_family F n i)%R = 0).
rewrite formal_specializationM.
by rewrite formal_specialization_vieta_generator mulr0.
Qed.

Lemma formal_specialization_displayed_ideal_zero p :
  OI.literal_displayed_ideal F n p -> formal_specialization p = 0.
Proof.
move=> hp.
apply: formal_specialization_vieta_ideal_zero.
exact: (GC.conventional_printed_generated_ideal_eq_vieta p).1 hp.
Qed.

(** The reverse kernel inclusion is constructive as well.  We first replace
    every formal coefficient variable [e_i] by the corresponding elementary
    symmetric polynomial, one monomial at a time.  The resulting polynomial
    is the canonical root lift of [formal_specialization p]. *)
Definition literal_vieta_congruent (p q : Ambient) : Prop :=
  OI.literal_vieta_ideal F n (p - q).

Lemma literal_vieta_congruent_refl (p : Ambient) :
  literal_vieta_congruent p p.
Proof.
rewrite /literal_vieta_congruent subrr.
exact: GI.generated_by0.
Qed.

Lemma literal_vieta_congruent_add (p q r s : Ambient) :
  literal_vieta_congruent p q -> literal_vieta_congruent r s ->
  literal_vieta_congruent (p + r) (q + s).
Proof.
rewrite /literal_vieta_congruent=> hpq hrs.
have h := GI.generated_byD hpq hrs.
have heq : ((p + r) - (q + s))%R = ((p - q) + (r - s))%R.
  by rewrite opprD addrACA.
by rewrite heq.
Qed.

Lemma literal_vieta_congruent_mul (p q r s : Ambient) :
  literal_vieta_congruent p q -> literal_vieta_congruent r s ->
  literal_vieta_congruent (p * r) (q * s).
Proof.
rewrite /literal_vieta_congruent=> hpq hrs.
have h1 := GI.generated_by_mul_left p hrs.
have h2 := GI.generated_by_mul_left s hpq.
have h := GI.generated_byD h1 h2.
have heq : (p * r - q * s)%R = (p * (r - s) + s * (p - q))%R.
  by rewrite !mulrBr (mulrC s p) (mulrC s q) subrKA.
by rewrite heq.
Qed.

Lemma literal_vieta_congruent_exp (p q : Ambient) (d : nat) :
  literal_vieta_congruent p q ->
  literal_vieta_congruent (p ^+ d) (q ^+ d).
Proof.
move=> hpq; elim: d=> [|d ih].
- exact: literal_vieta_congruent_refl.
- rewrite !exprS.
  exact: literal_vieta_congruent_mul hpq ih.
Qed.

Lemma literal_vieta_congruent_prod (T : finType) (p q : T -> Ambient) :
  (forall i, literal_vieta_congruent (p i) (q i)) ->
  literal_vieta_congruent (\prod_i p i) (\prod_i q i).
Proof.
move=> h.
elim/big_ind2: _ => [|a b c d hab hcd|i _].
- exact (literal_vieta_congruent_refl (1 : Ambient)).
- exact: literal_vieta_congruent_mul hab hcd.
- exact: h i.
Qed.

(** Two embeddings of a coefficient polynomial in the nested ring: the
    literal formal one, and elementary-symmetric substitution followed by a
    lift back to the root-polynomial ring. *)
Definition formal_root_lift (q : RootRing) : Ambient :=
  map_mpoly (@mpolyC n F) q.

Definition formal_coefficient_embedding (c : Coeff) : Ambient := c%:MP.

Definition substituted_coefficient_embedding (c : Coeff) : Ambient :=
  formal_root_lift (IM.sym_eval c).

Lemma formal_coefficient_embedding0 :
  formal_coefficient_embedding 0 = 0.
Proof. by rewrite /formal_coefficient_embedding mpolyC0. Qed.

Lemma formal_coefficient_embeddingD c d :
  formal_coefficient_embedding (c + d) =
    formal_coefficient_embedding c + formal_coefficient_embedding d.
Proof. exact: rmorphD. Qed.

Lemma formal_coefficient_embeddingM c d :
  formal_coefficient_embedding ((c * d)%R) =
    (formal_coefficient_embedding c * formal_coefficient_embedding d)%R.
Proof. exact: rmorphM. Qed.

Lemma substituted_coefficient_embedding0 :
  substituted_coefficient_embedding 0 = 0.
Proof.
by rewrite /substituted_coefficient_embedding /formal_root_lift
  IM.sym_eval0 raddf0.
Qed.

Lemma substituted_coefficient_embeddingD c d :
  substituted_coefficient_embedding (c + d) =
    substituted_coefficient_embedding c +
      substituted_coefficient_embedding d.
Proof.
by rewrite /substituted_coefficient_embedding /formal_root_lift
  IM.sym_evalD raddfD.
Qed.

Lemma substituted_coefficient_embeddingM c d :
  substituted_coefficient_embedding ((c * d)%R) =
    (substituted_coefficient_embedding c *
      substituted_coefficient_embedding d)%R.
Proof.
by rewrite /substituted_coefficient_embedding /formal_root_lift
  IM.sym_evalM rmorphM.
Qed.

Lemma formal_coefficient_embedding_base (c : F) :
  formal_coefficient_embedding c%:MP =
    substituted_coefficient_embedding c%:MP.
Proof.
rewrite /formal_coefficient_embedding /substituted_coefficient_embedding
  /formal_root_lift /IM.sym_eval comp_mpolyC map_mpolyC.
exact: erefl.
Qed.

Lemma formal_coefficient_embedding_X i :
  formal_coefficient_embedding ('X_i) =
    GC.concrete_formal_e F n i.+1.
Proof. by rewrite GC.concrete_formal_e_succ. Qed.

Lemma substituted_coefficient_embedding_X i :
  substituted_coefficient_embedding ('X_i) = mesym n Coeff i.+1.
Proof.
rewrite /substituted_coefficient_embedding /formal_root_lift /IM.sym_eval
  /IM.elementary_symmetric_tuple comp_mpolyXU
  -tnth_nth tnth_mktuple.
exact: VR.map_mpoly_mesym.
Qed.

Lemma formal_variables_literal_vieta_congruent i :
  literal_vieta_congruent
    (formal_coefficient_embedding ('X_i))
    (substituted_coefficient_embedding ('X_i)).
Proof.
rewrite formal_coefficient_embedding_X
  substituted_coefficient_embedding_X /literal_vieta_congruent.
have h := GI.generated_byN
  (GI.generated_by_generator (OI.literal_vieta_family F n) i).
rewrite /OI.literal_vieta_family /GC.concrete_vieta_relation
  /GI.vieta_relation /GC.concrete_sigma opprB in h.
exact h.
Qed.

Lemma formal_coefficient_embedding_monomial (u : 'X_{1..n}) :
  formal_coefficient_embedding ('X_[F, u]) =
    (\prod_i ((formal_coefficient_embedding ('X_i)) ^+ (u i))%R)%R.
Proof.
rewrite /formal_coefficient_embedding mpolyXE_id rmorph_prod.
apply: eq_bigr=> i _.
by rewrite rmorphXn.
Qed.

Lemma substituted_coefficient_embedding_monomial (u : 'X_{1..n}) :
  substituted_coefficient_embedding ('X_[F, u]) =
    (\prod_i ((substituted_coefficient_embedding ('X_i)) ^+ (u i))%R)%R.
Proof.
rewrite /substituted_coefficient_embedding /formal_root_lift /IM.sym_eval
  comp_mpolyX rmorph_prod.
apply: eq_bigr=> i _.
rewrite rmorphXn /IM.elementary_symmetric_tuple.
rewrite tnth_mktuple /substituted_coefficient_embedding
  /formal_root_lift /IM.sym_eval comp_mpolyXU
  -tnth_nth tnth_mktuple.
exact: erefl.
Qed.

Lemma formal_monomials_literal_vieta_congruent u :
  literal_vieta_congruent
    (formal_coefficient_embedding ('X_[F, u]))
    (substituted_coefficient_embedding ('X_[F, u])).
Proof.
rewrite formal_coefficient_embedding_monomial
  substituted_coefficient_embedding_monomial.
apply: literal_vieta_congruent_prod=> i.
exact: literal_vieta_congruent_exp
  (formal_variables_literal_vieta_congruent i).
Qed.

Theorem formal_coefficients_literal_vieta_congruent c :
  literal_vieta_congruent (formal_coefficient_embedding c)
    (substituted_coefficient_embedding c).
Proof.
elim/mpolyind: c=> [|a u p hu ha ih].
- rewrite formal_coefficient_embedding0
    substituted_coefficient_embedding0.
  exact: literal_vieta_congruent_refl.
- rewrite -mul_mpolyC formal_coefficient_embeddingD
    formal_coefficient_embeddingM substituted_coefficient_embeddingD
    substituted_coefficient_embeddingM.
  apply: literal_vieta_congruent_add.
  + apply: literal_vieta_congruent_mul.
    * rewrite formal_coefficient_embedding_base.
      exact: literal_vieta_congruent_refl.
    * exact: formal_monomials_literal_vieta_congruent.
  + exact: ih.
Qed.

Lemma formal_root_lift0 : formal_root_lift 0 = 0.
Proof. by rewrite /formal_root_lift raddf0. Qed.

Lemma formal_root_liftD q r :
  formal_root_lift (q + r) = formal_root_lift q + formal_root_lift r.
Proof. exact: raddfD. Qed.

Lemma formal_root_liftM q r :
  formal_root_lift ((q * r)%R) =
    (formal_root_lift q * formal_root_lift r)%R.
Proof. exact: rmorphM. Qed.

Lemma formal_root_lift_monomial u :
  formal_root_lift ('X_[F, u]) = 'X_[Coeff, u].
Proof. exact: map_mpolyX. Qed.

Lemma formal_root_lift_specialization_term c u :
  formal_root_lift
    (formal_specialization ((c *: 'X_[Coeff, u])%R)) =
  (substituted_coefficient_embedding c * 'X_[Coeff, u])%R.
Proof.
rewrite /formal_specialization.
rewrite (mmapZ (fun i : 'I_n => ('X_i : RootRing))
  (IM.sym_eval (n := n)) c ('X_[Coeff, u])).
rewrite (mmapX (fun i : 'I_n => ('X_i : RootRing))
  (IM.sym_eval (n := n)) u) mmap1_id
  formal_root_liftM formal_root_lift_monomial.
exact: erefl.
Qed.

(** Every nested polynomial is Vieta-congruent to the root lift of its
    specialization.  This is the missing reverse inclusion in the kernel
    theorem, proved structurally rather than assumed as an evaluation API. *)
Theorem formal_polynomial_literal_vieta_congruent p :
  literal_vieta_congruent p
    (formal_root_lift (formal_specialization p)).
Proof.
elim/mpolyind: p=> [|c u q hu hc ih].
- rewrite formal_specialization0 formal_root_lift0.
  exact: literal_vieta_congruent_refl.
- rewrite formal_specializationD formal_root_liftD.
  apply: literal_vieta_congruent_add.
  + rewrite formal_root_lift_specialization_term -mul_mpolyC.
    apply: literal_vieta_congruent_mul.
    * exact: formal_coefficients_literal_vieta_congruent.
    * exact: literal_vieta_congruent_refl.
  + exact: ih.
Qed.

(** Exact all-degree specialization kernel for the literal printed family. *)
Theorem formal_specialization_kernel_displayed p :
  formal_specialization p = 0 <-> OI.literal_displayed_ideal F n p.
Proof.
split.
- move=> hp.
  have h := formal_polynomial_literal_vieta_congruent p.
  rewrite /literal_vieta_congruent hp formal_root_lift0 subr0 in h.
  exact: (GC.conventional_printed_generated_ideal_eq_vieta p).2 h.
- exact: formal_specialization_displayed_ideal_zero.
Qed.

Theorem formal_specialization_standard_expansion p :
  paper_standard p ->
  formal_specialization p =
    \sum_a ((p @_ (paper_artin_exponent a)) *: paper_artin_basis a)%R.
Proof.
move=> hp.
rewrite {1}(paper_standard_expansion hp)
  /formal_specialization raddf_sum.
apply: eq_bigr=> a _.
change (mmap (IM.sym_eval (n := n))
  (fun i : 'I_n => ('X_i : RootRing))
  (((p @_ (paper_artin_exponent a)) *:
    'X_[Coeff, paper_artin_exponent a])%R) =
  ((p @_ (paper_artin_exponent a)) *: paper_artin_basis a)%R).
rewrite (mmapZ (fun i : 'I_n => ('X_i : RootRing))
  (IM.sym_eval (n := n)) (p @_ (paper_artin_exponent a))
  ('X_[Coeff, paper_artin_exponent a])).
rewrite (mmapX (fun i : 'I_n => ('X_i : RootRing))
  (IM.sym_eval (n := n)) (paper_artin_exponent a))
  mmap1_id paper_artin_basisE
  SM.symmetric_scalarE.
exact: erefl.
Qed.

Theorem formal_specialization_paper_standard_injective p :
  paper_standard p -> formal_specialization p = 0 -> p = 0.
Proof.
move=> hp hzero.
have hsum := formal_specialization_standard_expansion hp.
rewrite hzero in hsum.
have hcoeff : forall a, p @_ (paper_artin_exponent a) = 0.
  apply: paper_artin_basis_independent.
  exact (esym hsum).
rewrite (paper_standard_expansion hp).
apply: big1=> a _.
by rewrite hcoeff scale0r.
Qed.

(** Coordinates in the paper-oriented Artin basis.  The recursive basis is
    expressed in the reverse variable order, so coordinates are taken after
    undoing that reversal. *)
Definition paper_artin_coordinate (q : RootRing) (a : ReverseArtin) : Coeff :=
  FF.ffd_coeff
    (@AS.lazard_reverse_artin_finite_free_decomposition F n)
    (msym (paper_reverse_perm^-1)%g q) a.

Lemma paper_artin_reverse c a :
  msym paper_reverse_perm
    ((c *: (FF.ffd_basis
        (@AS.lazard_reverse_artin_finite_free_decomposition F n) a))%R) =
  (c *: paper_artin_basis a)%R.
Proof.
rewrite !SM.symmetric_scalarE /paper_artin_basis msymM msym_sym_eval.
exact: erefl.
Qed.

Theorem paper_artin_coordinates_reconstruct q :
  q = \sum_a ((paper_artin_coordinate q a) *: paper_artin_basis a)%R.
Proof.
have h := FF.ffd_reconstruct
  (@AS.lazard_reverse_artin_finite_free_decomposition F n)
  (msym (paper_reverse_perm^-1)%g q).
have h' := congr1 (msym paper_reverse_perm) h.
rewrite -msymMm mulVg msym1m raddf_sum in h'.
have hsum :
    (\sum_a msym paper_reverse_perm
      (((FF.ffd_coeff
          (@AS.lazard_reverse_artin_finite_free_decomposition F n)
          (msym (paper_reverse_perm^-1)%g q) a) *:
        (FF.ffd_basis
          (@AS.lazard_reverse_artin_finite_free_decomposition F n) a))%R)) =
    \sum_a ((paper_artin_coordinate q a) *: paper_artin_basis a)%R.
  apply: eq_bigr=> a _.
  exact: paper_artin_reverse.
rewrite hsum in h'.
exact: h'.
Qed.

(** The explicit Artin normal representative in the nested formal ring. *)
Definition formal_artin_remainder (q : RootRing) : Ambient :=
  \sum_a ((paper_artin_coordinate q a) *:
    'X_[Coeff, paper_artin_exponent a])%R.

Lemma formal_artin_remainder_paper_standard q :
  paper_standard (formal_artin_remainder q).
Proof.
move=> u.
move/msupp_sum_le/flattenP=> [s].
move/mapP=> [a _ ->] hu i.
move/msuppZ_le: hu=> /mem_msuppXP <-.
exact: paper_artin_exponent_standard.
Qed.

Lemma formal_specialization_formal_artin_remainder q :
  formal_specialization (formal_artin_remainder q) = q.
Proof.
rewrite /formal_artin_remainder /formal_specialization raddf_sum.
rewrite {2}(paper_artin_coordinates_reconstruct q).
apply: eq_bigr=> a _.
change (mmap (IM.sym_eval (n := n))
  (fun i : 'I_n => ('X_i : RootRing))
  (((paper_artin_coordinate q a) *:
    'X_[Coeff, paper_artin_exponent a])%R) =
  ((paper_artin_coordinate q a) *: paper_artin_basis a)%R).
rewrite (mmapZ (fun i : 'I_n => ('X_i : RootRing))
  (IM.sym_eval (n := n)) (paper_artin_coordinate q a)
  ('X_[Coeff, paper_artin_exponent a])).
rewrite (mmapX (fun i : 'I_n => ('X_i : RootRing))
  (IM.sym_eval (n := n)) (paper_artin_exponent a))
  mmap1_id paper_artin_basisE
  SM.symmetric_scalarE.
exact: erefl.
Qed.

(** A displayed leading monomial at [rev_ord i] divides [(u,v)] as soon
    as the exponent of root [i] reaches the forbidden staircase bound. *)
Lemma displayed_leading_divides_of_root_bound
    (u v : 'X_{1..n}) (i : 'I_n) :
  (n - i <= u i)%N ->
  OI.combined_divides
    (OI.displayed_leading_monomial n (rev_ord i)) (u, v).
Proof.
move=> hui; apply/andP; split.
- apply/mnm_lepP=> j.
  rewrite /OI.displayed_leading_monomial /OI.displayed_pivot
    mulmnE mnm1E rev_ordK.
  case: eqP=> [hij|_].
  + rewrite /rev_ord /= (subnSK (ltn_ord i)) -hij mul1n.
    exact hui.
  + exact: leq0n _.
- apply/mnm_lepP=> j.
  by rewrite mnm0E.
Qed.

(** The interface's combined standardness implies the root staircase
    condition used by the Artin basis. *)
Lemma literal_standard_implies_paper_standard p :
  OI.literal_standard F n p -> paper_standard p.
Proof.
move=> hp u hu i.
have houter : p @_ u != 0 by rewrite -mcoeff_msupp.
pose v := mlead (p @_ u).
have hv : v \in msupp (p @_ u) := mlead_supp houter.
have huv : OI.combined_support p (u, v).
  rewrite /OI.combined_support /OI.combined_coefficient.
  move=> hzero.
  by move: hv; rewrite mcoeff_msupp /= hzero eqxx.
apply/negP=> hnot.
have hui : (n - i <= u i)%N.
  rewrite leqNgt.
  apply/negP.
  exact hnot.
apply: (hp (u, v) huv (rev_ord i)).
exact: displayed_leading_divides_of_root_bound hui.
Qed.

(** Conversely, the staircase inequalities exclude every displayed leading
    power.  Hence [paper_standard] and the literal combined standardness
    predicate coincide; the formal-coefficient component is irrelevant
    because every displayed leading monomial has coefficient part zero. *)
Lemma paper_standard_implies_literal_standard p :
  paper_standard p -> OI.literal_standard F n p.
Proof.
move=> hp [u v] huv k /andP [hroot _].
have hu : u \in msupp p.
  rewrite mcoeff_msupp; apply/negP=> /eqP hu0.
  apply: huv.
  by rewrite /OI.combined_support /OI.combined_coefficient hu0 mcoeff0.
have hbound := hp u hu (rev_ord k).
have hcoord := mnm_lepP hroot (OI.displayed_pivot n k).
move: hcoord; rewrite /OI.displayed_leading_monomial /OI.displayed_pivot
  mulmnE mnm1E eqxx mul1n=> hcoord.
move: hbound; rewrite /rev_ord /= (subKn (ltn_ord k))=> hbound.
have hfalse : (k.+1 < k.+1)%N := leq_ltn_trans hcoord hbound.
by rewrite ltnn in hfalse.
Qed.

Lemma literal_standard_iff_paper_standard p :
  OI.literal_standard F n p <-> paper_standard p.
Proof.
split.
- exact: literal_standard_implies_paper_standard.
- exact: paper_standard_implies_literal_standard.
Qed.

Lemma formal_artin_remainder_literal_standard q :
  OI.literal_standard F n (formal_artin_remainder q).
Proof.
apply: paper_standard_implies_literal_standard.
exact: formal_artin_remainder_paper_standard.
Qed.

(** Every formal polynomial has a fully explicit standard representative,
    and its congruence is certified by the exact specialization-kernel
    theorem above. *)
Theorem exists_canonical_literal_standard_remainder p :
  OI.literal_standard F n
      (formal_artin_remainder (formal_specialization p)) /\
  OI.literal_displayed_ideal F n
      (p - formal_artin_remainder (formal_specialization p)).
Proof.
split.
- exact: formal_artin_remainder_literal_standard.
- apply: (formal_specialization_kernel_displayed
      (p - formal_artin_remainder (formal_specialization p))).1.
  by rewrite formal_specializationB
    formal_specialization_formal_artin_remainder subrr.
Qed.

(** The order-independent Artin separation theorem. *)
Theorem literal_standard_displayed_ideal_zero p :
  OI.literal_standard F n p ->
  OI.literal_displayed_ideal F n p -> p = 0.
Proof.
move=> hp hideal.
apply: formal_specialization_paper_standard_injective.
- exact: literal_standard_implies_paper_standard hp.
- exact: formal_specialization_displayed_ideal_zero hideal.
Qed.

Lemma literal_standardB p q :
  OI.literal_standard F n p -> OI.literal_standard F n q ->
  OI.literal_standard F n (p - q).
Proof.
move=> hp hq a ha k.
have hor : OI.combined_support p a \/ OI.combined_support q a.
  case hp0: (OI.combined_coefficient p a == 0).
  + have hpz := eqP hp0.
    right; move=> hq0; apply: ha.
    rewrite /OI.combined_coefficient in hpz hq0.
    by rewrite /OI.combined_support /OI.combined_coefficient
      !mcoeffB hpz hq0 subrr.
  + left; move=> hpz.
    by move: hp0; rewrite hpz eqxx.
case: hor=> hs.
- exact: hp a hs k.
- exact: hq a hs k.
Qed.

Lemma literal_standardD p q :
  OI.literal_standard F n p -> OI.literal_standard F n q ->
  OI.literal_standard F n (p + q).
Proof.
move=> hp hq a ha k.
have hor : OI.combined_support p a \/ OI.combined_support q a.
  case hp0: (OI.combined_coefficient p a == 0).
  + have hpz := eqP hp0.
    right; move=> hq0; apply: ha.
    rewrite /OI.combined_coefficient in hpz hq0.
    by rewrite /OI.combined_support /OI.combined_coefficient
      !mcoeffD hpz hq0 add0r.
  + left; move=> hpz.
    by move: hp0; rewrite hpz eqxx.
case: hor=> hs.
- exact: hp a hs k.
- exact: hq a hs k.
Qed.

(** * Combined-monomial arithmetic for monic division *)

Lemma combined_addA (a b c : Monomial) :
  OI.combined_add a (OI.combined_add b c) =
  OI.combined_add (OI.combined_add a b) c.
Proof.
case: a=> [u v]; case: b=> [u' v']; case: c=> [u'' v''].
by rewrite /OI.combined_add /= !addmA.
Qed.

Definition combined_sub (a b : Monomial) : Monomial :=
  ((a.1 - b.1)%MM, (a.2 - b.2)%MM).

Lemma combined_subK a b :
  OI.combined_divides b a ->
  OI.combined_add (combined_sub a b) b = a.
Proof.
move=> /andP [hroot hcoeff].
case: a hroot hcoeff=> [u v] /= hroot hcoeff.
case: b hroot hcoeff=> [u' v'] /= hroot hcoeff.
rewrite /OI.combined_add /combined_sub /=.
by rewrite (submK hroot) (submK hcoeff).
Qed.

Lemma combined_add_le_compat
    (O : OI.admissible_monomial_order n) a b c :
  OI.amo_le O a b ->
  OI.amo_le O (OI.combined_add c a) (OI.combined_add c b).
Proof.
move=> hab.
rewrite ![OI.combined_add c _]combined_addC.
exact: (OI.amo_add_compat O a b c).1 hab.
Qed.

Lemma combined_add_lt_compat
    (O : OI.admissible_monomial_order n) a b c :
  OI.amo_lt O a b ->
  OI.amo_lt O (OI.combined_add c a) (OI.combined_add c b).
Proof.
move=> [hab hne]; split.
- exact: combined_add_le_compat hab.
- move=> hadd.
  apply: hne.
  clear hab.
  case: a hadd=> [u v]; case: b=> [u' v']; case: c=> [w z].
  rewrite /OI.combined_add /= => hadd.
  have hu : u = u' := addmI (congr1 fst hadd).
  have hv : v = v' := addmI (congr1 snd hadd).
  by subst u'; subst v'.
Qed.

Lemma combined_monomial_coefficient_same a :
  OI.combined_coefficient
    (OI.combined_monomial_polynomial F n a) a = (1%R : F).
Proof.
case: a=> [u v].
by rewrite /OI.combined_coefficient
  /OI.combined_monomial_polynomial /= mcoeffZ mcoeffX eqxx
  mulr1 mcoeffX eqxx.
Qed.

Lemma combined_monomial_support_single a b :
  OI.combined_support
      (OI.combined_monomial_polynomial F n a) b -> b = a.
Proof.
case: a=> [u v]; case: b=> [u' v'] /=.
rewrite /OI.combined_support /OI.combined_coefficient
  /OI.combined_monomial_polynomial /= mcoeffZ mcoeffX.
case hu: (u == u').
- move/eqP: hu=> ->.
  rewrite mulr1 mcoeffX.
  case hv: (v == v').
  + by move/eqP: hv=> ->.
  + move=> hzero; exfalso; apply: hzero.
    exact: erefl.
- rewrite mulr0 mcoeff0=> hzero; exfalso; apply: hzero.
  exact: erefl.
Qed.

Lemma combined_coefficient_monomial_mul p q a :
  OI.combined_coefficient
      (OI.combined_monomial_polynomial F n q * p)
      (OI.combined_add q a) =
    OI.combined_coefficient p a.
Proof.
case: q=> [u v]; case: a=> [u' v'].
rewrite /OI.combined_coefficient /OI.combined_monomial_polynomial
  /OI.combined_add /=.
rewrite -scalerAl mcoeffZ.
rewrite [(('X_[Coeff, u] * p)%R)]mulrC mcoeffMX.
rewrite [(('X_[F, v] * (p @_ u'))%R)]mulrC mcoeffMX.
exact: erefl.
Qed.

Lemma combined_support_monomial_mul p q z :
  OI.combined_support
      (OI.combined_monomial_polynomial F n q * p) z ->
  exists a,
    OI.combined_support p a /\ z = OI.combined_add q a.
Proof.
case: q=> [u v]; case: z=> [w z] /=.
rewrite /OI.combined_support /OI.combined_coefficient
  /OI.combined_monomial_polynomial /= -scalerAl mcoeffZ.
move=> hcoeff.
have hroot : ('X_[Coeff, u] * p) @_ w != 0.
  apply/negP=> /eqP hzero; apply: hcoeff.
  by rewrite hzero mulr0 mcoeff0.
have hw : w \in msupp (p * 'X_[Coeff, u]).
  rewrite mcoeff_msupp.
  by rewrite mulrC.
move: hw; rewrite (perm_mem (msuppMX p u)).
move/mapP=> [u' hu' hw].
rewrite hw in hcoeff.
have hz : z \in msupp ((p @_ u') * 'X_[F, v]).
  rewrite mcoeff_msupp.
  move: hcoeff.
  rewrite [(('X_[Coeff, u] * p)%R)]mulrC.
  rewrite mcoeffMX=> hne.
  rewrite mulrC in hne.
  apply/negP=> /eqP hzero.
  exact: hne hzero.
move: hz; rewrite (perm_mem (msuppMX (p @_ u') v)).
move/mapP=> [v' hv' ->].
exists (u', v'); split.
- rewrite /OI.combined_support /OI.combined_coefficient.
  move=> hzero.
  by move: hv'; rewrite mcoeff_msupp hzero eqxx.
- by rewrite /OI.combined_add /= hw.
Qed.

(** Scalar multiplication by the ground field, made explicit through the
    constant-polynomial embedding into the nested coefficient ring. *)
Definition ambient_scale (c : F) (p : Ambient) : Ambient :=
  ((c%:MP : Coeff) *: p)%R.

Lemma ambient_scale_mul c p q :
  (ambient_scale c p * q)%R = ambient_scale c ((p * q)%R).
Proof. by rewrite /ambient_scale scalerAl. Qed.

Lemma combined_support_scale (c : F) p a :
  OI.combined_support (ambient_scale c p) a ->
  OI.combined_support p a.
Proof.
case: a=> [u v].
rewrite /OI.combined_support /OI.combined_coefficient
  /ambient_scale /= mcoeffZ mcoeffCM.
move=> h hp0; apply: h.
by rewrite hp0 mulr0.
Qed.

Lemma combined_coefficient_scale (c : F) p a :
  OI.combined_coefficient (ambient_scale c p) a =
    (c * OI.combined_coefficient p a)%R.
Proof.
case: a=> [u v].
by rewrite /OI.combined_coefficient /ambient_scale /= mcoeffZ mcoeffCM.
Qed.

Lemma combined_coefficientD (p q : Ambient) (a : Monomial) :
  OI.combined_coefficient (p + q) a =
    OI.combined_coefficient p a + OI.combined_coefficient q a.
Proof.
case: a=> [u v].
by rewrite /OI.combined_coefficient /= !mcoeffD.
Qed.

Lemma combined_coefficientB (p q : Ambient) (a : Monomial) :
  OI.combined_coefficient (p - q) a =
    OI.combined_coefficient p a - OI.combined_coefficient q a.
Proof.
case: a=> [u v].
by rewrite /OI.combined_coefficient /= !mcoeffB.
Qed.

Lemma combined_monomial_standard a :
  (forall k : 'I_n,
    ~ OI.combined_divides (OI.displayed_leading_monomial n k) a) ->
  OI.literal_standard F n
    (OI.combined_monomial_polynomial F n a).
Proof.
move=> ha b hb k.
have -> := combined_monomial_support_single hb.
exact: ha k.
Qed.

Lemma combined_supportB_cases (p q : Ambient) (a : Monomial) :
  OI.combined_support (p - q) a ->
  OI.combined_support p a \/ OI.combined_support q a.
Proof.
move=> ha.
case hp0: (OI.combined_coefficient p a == 0).
- right; move=> hq0; apply: ha.
  case: a hp0 hq0=> [u v] /=.
  rewrite /OI.combined_support /OI.combined_coefficient /=
    !mcoeffB=> hp0 hq0.
  by rewrite (eqP hp0) hq0 subrr.
- left; move=> hpz.
  by move: hp0; rewrite hpz eqxx.
Qed.

Lemma combined_supportD_cases (p q : Ambient) (a : Monomial) :
  OI.combined_support (p + q) a ->
  OI.combined_support p a \/ OI.combined_support q a.
Proof.
move=> ha.
case hp0: (OI.combined_coefficient p a == 0).
- right; move=> hq0; apply: ha.
  case: a hp0 hq0=> [u v] /=.
  rewrite /OI.combined_support /OI.combined_coefficient /=
    !mcoeffD=> hp0 hq0.
  by rewrite (eqP hp0) hq0 add0r.
- left; move=> hpz.
  by move: hp0; rewrite hpz eqxx.
Qed.

Lemma leading_cancellation_support_upper
    (O : OI.admissible_monomial_order n)
    (p t : Ambient) a :
  OI.is_leading_monomial O p a ->
  (forall b, OI.combined_support t b -> OI.amo_le O b a) ->
  forall b, OI.combined_support (p - t) b -> OI.amo_le O b a.
Proof.
move=> hp ht b hb.
case: (combined_supportB_cases hb)=> hs.
- exact: is_leading_monomial_upper hp hs.
- exact: ht b hs.
Qed.

Lemma leading_cancellation_coefficient_zero (p t : Ambient) (a : Monomial) :
  OI.combined_coefficient t a = OI.combined_coefficient p a ->
  OI.combined_coefficient (p - t) a = (0%R : F).
Proof.
move=> hcoeff; case: a hcoeff=> [u v] /=.
rewrite /OI.combined_coefficient /= !mcoeffB=> hcoeff.
by rewrite hcoeff subrr.
Qed.

Lemma leading_cancellation_strict
    (O : OI.admissible_monomial_order n)
    (C : decidable_admissible_order O)
    (p t : Ambient) a :
  OI.is_leading_monomial O p a ->
  OI.combined_coefficient t a = OI.combined_coefficient p a ->
  (forall b, OI.combined_support t b -> OI.amo_le O b a) ->
  p - t <> 0 ->
  OI.amo_lt O (combined_leading_monomial C (p - t)) a.
Proof.
move=> hp hcoeff ht hnonzero; split.
- apply: leading_cancellation_support_upper.
  + exact: hp.
  + exact: ht.
  + exact: (combined_leading_monomialP C hnonzero).1.
- move=> heq.
  have hs := (combined_leading_monomialP C hnonzero).1.
  rewrite heq /OI.combined_support
    (leading_cancellation_coefficient_zero hcoeff) in hs.
  exact: hs erefl.
Qed.

Section MonicDivisionSteps.

Variable O : OI.admissible_monomial_order n.
Variable D : literal_order_support_data F O.
Variable C : decidable_admissible_order O.

Definition selected_leading (p : Ambient) : Monomial :=
  combined_leading_monomial C p.

Definition selected_coefficient (p : Ambient) : F :=
  OI.combined_coefficient p (selected_leading p).

Definition leading_term (p : Ambient) : Ambient :=
  ambient_scale (selected_coefficient p)
    (OI.combined_monomial_polynomial F n (selected_leading p)).

Definition reducible_pivot (a : Monomial) : option 'I_n :=
  [pick k : 'I_n |
    OI.combined_divides (OI.displayed_leading_monomial n k) a].

Definition reduction_term (p : Ambient) (k : 'I_n) : Ambient :=
  (ambient_scale (selected_coefficient p)
      (OI.combined_monomial_polynomial F n
        (combined_sub (selected_leading p)
          (OI.displayed_leading_monomial n k)))) *
    OI.literal_displayed_family F n k.

Lemma selected_leadingP p :
  p <> 0 -> OI.is_leading_monomial O p (selected_leading p).
Proof. exact: combined_leading_monomialP. Qed.

Lemma selected_coefficient_nonzero p :
  p <> 0 -> selected_coefficient p <> 0.
Proof.
move=> hp0.
exact: (selected_leadingP hp0).1.
Qed.

Lemma leading_term_coefficient p :
  OI.combined_coefficient (leading_term p) (selected_leading p) =
    OI.combined_coefficient p (selected_leading p).
Proof.
rewrite /leading_term /selected_coefficient combined_coefficient_scale
  combined_monomial_coefficient_same mulr1.
exact: erefl.
Qed.

Lemma leading_term_support_upper p b :
  OI.combined_support (leading_term p) b ->
  OI.amo_le O b (selected_leading p).
Proof.
move/combined_support_scale.
move/combined_monomial_support_single=> ->.
exact: OI.amo_le_refl O _.
Qed.

Lemma leading_term_standard p :
  (forall k : 'I_n,
    ~ OI.combined_divides
      (OI.displayed_leading_monomial n k) (selected_leading p)) ->
  OI.literal_standard F n (leading_term p).
Proof.
move=> hnone a ha k.
have -> : a = selected_leading p.
  apply: combined_monomial_support_single.
  exact: combined_support_scale ha.
exact: hnone k.
Qed.

Lemma reduction_term_coefficient p k
    (hk : OI.combined_divides
      (OI.displayed_leading_monomial n k) (selected_leading p)) :
  OI.combined_coefficient (reduction_term p k) (selected_leading p) =
    OI.combined_coefficient p (selected_leading p).
Proof.
rewrite /reduction_term ambient_scale_mul combined_coefficient_scale.
set d := combined_sub (selected_leading p)
  (OI.displayed_leading_monomial n k).
have hd : OI.combined_add d (OI.displayed_leading_monomial n k) =
    selected_leading p.
  rewrite /d.
  exact: combined_subK hk.
have hmono :
    OI.combined_coefficient
      ((OI.combined_monomial_polynomial F n d *
        OI.literal_displayed_family F n k)%R)
      (selected_leading p) =
    OI.combined_coefficient (OI.literal_displayed_family F n k)
      (OI.displayed_leading_monomial n k).
  rewrite -hd.
  exact: combined_coefficient_monomial_mul.
rewrite hmono (losd_monic D) mulr1.
exact: erefl.
Qed.

Lemma reduction_term_support_upper p k
    (hk : OI.combined_divides
      (OI.displayed_leading_monomial n k) (selected_leading p)) b :
  OI.combined_support (reduction_term p k) b ->
  OI.amo_le O b (selected_leading p).
Proof.
rewrite /reduction_term ambient_scale_mul.
move/combined_support_scale.
move/combined_support_monomial_mul=> [a [ha ->]].
have halead : OI.amo_le O a (OI.displayed_leading_monomial n k).
  exact: is_leading_monomial_upper (losd_leading D k) ha.
have hadd := @combined_add_le_compat O a
  (OI.displayed_leading_monomial n k)
  (combined_sub (selected_leading p)
    (OI.displayed_leading_monomial n k)) halead.
by rewrite (combined_subK hk) in hadd.
Qed.

Lemma leading_term_remainder_strict p :
  p <> 0 -> p - leading_term p <> 0 ->
  OI.amo_lt O (selected_leading (p - leading_term p))
    (selected_leading p).
Proof.
move=> hp0 hstep.
apply: leading_cancellation_strict.
- exact: selected_leadingP hp0.
- exact: leading_term_coefficient.
- exact: leading_term_support_upper.
- exact: hstep.
Qed.

Lemma reduction_remainder_strict p k
    (hk : OI.combined_divides
      (OI.displayed_leading_monomial n k) (selected_leading p)) :
  p <> 0 -> p - reduction_term p k <> 0 ->
  OI.amo_lt O (selected_leading (p - reduction_term p k))
    (selected_leading p).
Proof.
move=> hp0 hstep.
apply: leading_cancellation_strict.
- exact: selected_leadingP hp0.
- exact: reduction_term_coefficient hk.
- exact: reduction_term_support_upper hk.
- exact: hstep.
Qed.

Lemma reduction_term_in_displayed_ideal p k :
  OI.literal_displayed_ideal F n (reduction_term p k).
Proof.
rewrite /reduction_term.
exact: GI.generated_by_mul_left
  (GI.generated_by_generator (OI.literal_displayed_family F n) k).
Qed.

End MonicDivisionSteps.

(** The recursive output carries the two invariants needed in the only
    delicate branch: no term in the remainder rises above the input leading
    monomial, and an irreducible input leading coefficient is retained. *)
Section ConstructiveMonicDivision.

Variable O : OI.admissible_monomial_order n.
Variable D : literal_order_support_data F O.
Variable C : decidable_admissible_order O.

Record monic_division_result (p : Ambient) : Type :=
  MonicDivisionResult {
    mdr_remainder : Ambient;
    mdr_standard : OI.literal_standard F n mdr_remainder;
    mdr_congruent : OI.literal_displayed_ideal F n (p - mdr_remainder);
    mdr_support_upper : p <> 0 -> forall b,
      OI.combined_support mdr_remainder b ->
      OI.amo_le O b (selected_leading C p);
    mdr_preserves_selected : p <> 0 ->
      (forall k : 'I_n,
        ~ OI.combined_divides
          (OI.displayed_leading_monomial n k) (selected_leading C p)) ->
      OI.combined_coefficient mdr_remainder (selected_leading C p) =
        OI.combined_coefficient p (selected_leading C p);
    mdr_zero : p = 0 -> mdr_remainder = 0
  }.

Definition division_polynomial_lt (p q : Ambient) : Prop :=
  OI.amo_lt O (selected_leading C p) (selected_leading C q).

Lemma division_polynomial_lt_well_founded :
  well_founded division_polynomial_lt.
Proof.
exact: (@wf_inverse_image Ambient Monomial (OI.amo_lt O)
  (selected_leading C) (OI.amo_lt_well_founded O)).
Qed.

Definition monic_division_step (p : Ambient)
    (rec : forall q : Ambient,
      division_polynomial_lt q p -> monic_division_result q) :
    monic_division_result p.
Proof.
case hpzero: (p == 0).
- move/eqP: hpzero=> ->.
  refine {| mdr_remainder := 0 |}.
  + exact: OI.literal_standard0.
  + by rewrite subrr; exact: GI.generated_by0.
  + move=> hzero.
    exact: False_rect _ (hzero erefl).
  + move=> hzero.
    exact: False_rect _ (hzero erefl).
  + exact: id.
- have hp0 : p <> 0.
    move=> hp.
    by move: hpzero; rewrite hp eqxx.
  case: (pickP [pred k : 'I_n |
      OI.combined_divides
        (OI.displayed_leading_monomial n k) (selected_leading C p)]) =>
      [k hk|hnone].
  + pose q := p - reduction_term C p k.
    case hqzero: (q == 0).
    * have hq0 : q = 0 := eqP hqzero.
      refine {| mdr_remainder := 0 |}.
      -- exact: OI.literal_standard0.
      -- rewrite subr0.
         have hpterm : p = reduction_term C p k.
           apply/eqP; rewrite -subr_eq0.
           apply/eqP.
           exact hq0.
         rewrite hpterm.
         exact: reduction_term_in_displayed_ideal.
      -- move=> _ b hb.
         exact: False_rect _ (OI.combined_zero_not_support hb).
      -- move=> _ hnone'.
         exact: False_rect _ (hnone' k hk).
      -- move=> hp.
         exact: False_rect _ (hp0 hp).
    * have hq0 : q <> 0.
        move=> hq.
        by move: hqzero; rewrite hq eqxx.
      have hlt : division_polynomial_lt q p.
        exact (reduction_remainder_strict D hk hp0 hq0).
      pose Rq := rec q hlt.
      refine {| mdr_remainder := mdr_remainder Rq |}.
      -- exact: mdr_standard Rq.
      -- have h := GI.generated_byD
           (reduction_term_in_displayed_ideal C p k)
           (mdr_congruent Rq).
         have heq : (p - mdr_remainder Rq)%R =
             (reduction_term C p k +
               (q - mdr_remainder Rq))%R.
           apply: (addIr (mdr_remainder Rq)).
           rewrite subrK addrA subrK /q.
           by rewrite addrC subrK.
         rewrite heq.
         exact h.
      -- move=> _ b hb.
         eapply OI.amo_le_trans.
         ++ exact: mdr_support_upper Rq hq0 b hb.
         ++ exact: hlt.1.
      -- move=> _ hnone'.
         exact: False_rect _ (hnone' k hk).
      -- move=> hp.
         exact: False_rect _ (hp0 hp).
  + have hnone' k :
        ~ OI.combined_divides
          (OI.displayed_leading_monomial n k) (selected_leading C p).
      move=> hk.
      have hfalse := hnone k.
      change (OI.combined_divides
        (OI.displayed_leading_monomial n k)
        (selected_leading C p) = false) in hfalse.
      by move: hfalse; rewrite hk.
    pose q := p - leading_term C p.
    case hqzero: (q == 0).
    * have hq0 : q = 0 := eqP hqzero.
      refine {| mdr_remainder := leading_term C p |}.
      -- exact: leading_term_standard hnone'.
      -- change (OI.literal_displayed_ideal F n q).
         rewrite hq0.
         exact: GI.generated_by0.
      -- move=> _ b hb.
         exact: leading_term_support_upper hb.
      -- move=> _ _.
         exact: leading_term_coefficient.
      -- move=> hp.
         exact: False_rect _ (hp0 hp).
    * have hq0 : q <> 0.
        move=> hq.
        by move: hqzero; rewrite hq eqxx.
      have hlt : division_polynomial_lt q p.
        exact (leading_term_remainder_strict hp0 hq0).
      pose Rq := rec q hlt.
      refine {| mdr_remainder :=
        leading_term C p + mdr_remainder Rq |}.
      -- apply: literal_standardD.
         ++ exact: leading_term_standard hnone'.
         ++ exact: mdr_standard Rq.
      -- have h := mdr_congruent Rq.
         have heq :
             (p - (leading_term C p + mdr_remainder Rq))%R =
             (q - mdr_remainder Rq)%R.
           rewrite /q opprD.
           by rewrite addrA.
         rewrite heq.
         exact h.
      -- move=> _ b hb.
         case: (combined_supportD_cases hb)=> hs.
         ++ exact: leading_term_support_upper hs.
         ++ eapply OI.amo_le_trans.
            ** exact: mdr_support_upper Rq hq0 b hs.
            ** exact: hlt.1.
      -- move=> _ _.
         rewrite combined_coefficientD leading_term_coefficient.
         have hrzero :
             OI.combined_coefficient (mdr_remainder Rq)
               (selected_leading C p) = 0.
           case hzero: (OI.combined_coefficient (mdr_remainder Rq)
               (selected_leading C p) == 0).
           ++ exact: eqP hzero.
           ++ have hs : OI.combined_support (mdr_remainder Rq)
                 (selected_leading C p).
                move=> hs0.
                by rewrite hs0 eqxx in hzero.
              have hle := @mdr_support_upper q Rq hq0
                (selected_leading C p) hs.
              have heq := OI.amo_le_antisym hle hlt.1.
              exact: False_rect _ (hlt.2 (esym heq)).
         by rewrite hrzero addr0.
      -- move=> hp.
         exact: False_rect _ (hp0 hp).
Defined.

Definition constructed_monic_division_result (p : Ambient) :
    monic_division_result p :=
  @Fix Ambient division_polynomial_lt
    division_polynomial_lt_well_founded
    (fun q => monic_division_result q) monic_division_step p.

Definition constructed_division_remainder (p : Ambient) : Ambient :=
  mdr_remainder (constructed_monic_division_result p).

Lemma constructed_division_standard p :
  OI.literal_standard F n (constructed_division_remainder p).
Proof. exact: mdr_standard (constructed_monic_division_result p). Qed.

Lemma constructed_division_congruent p :
  OI.literal_displayed_ideal F n
    (p - constructed_division_remainder p).
Proof. exact: mdr_congruent (constructed_monic_division_result p). Qed.

Lemma constructed_division_preserves_irreducible_leading p a :
  OI.is_leading_monomial O p a ->
  (forall k : 'I_n,
    ~ OI.combined_divides
      (OI.displayed_leading_monomial n k) a) ->
  OI.combined_coefficient (constructed_division_remainder p) a =
    OI.combined_coefficient p a.
Proof.
move=> ha hnone.
have hp0 : p <> 0.
  move=> hp; subst p.
  exact: OI.combined_zero_not_support ha.1.
have hselected := selected_leadingP C hp0.
have hea : selected_leading C p = a :=
  is_leading_monomial_unique hselected ha.
subst a.
exact: mdr_preserves_selected
  (constructed_monic_division_result p) hp0 hnone.
Qed.

End ConstructiveMonicDivision.

(** * Constructed arbitrary-order division interface *)

(** Unlike [OI.displayed_division_normal_form], this record does not ask the
    caller to certify uniqueness.  It is exactly the constructive output of
    monic division for the displayed family. *)
Record literal_division_existence
    (O : OI.admissible_monomial_order n) : Type :=
  LiteralDivisionExistence {
    lde_remainder : Ambient -> Ambient;
    lde_standard : forall p,
      OI.literal_standard F n (lde_remainder p);
    lde_congruent : forall p,
      OI.literal_displayed_ideal F n (p - lde_remainder p);
    lde_preserves_irreducible_leading : forall p a,
      OI.is_leading_monomial O p a ->
      (forall k : 'I_n,
        ~ OI.combined_divides
          (OI.displayed_leading_monomial n k) a) ->
      OI.combined_coefficient (lde_remainder p) a =
        OI.combined_coefficient p a
  }.

(** Ordinary monic division is now an inhabitant, not an exposed
    certificate.  Its recursion is the well-founded construction above. *)
Definition constructed_literal_division_existence
    (O : OI.admissible_monomial_order n)
    (D : literal_order_support_data F O)
    (C : decidable_admissible_order O) :
    literal_division_existence O.
Proof.
refine {| lde_remainder := constructed_division_remainder D C |}.
- exact: constructed_division_standard D C.
- exact: constructed_division_congruent D C.
- exact: constructed_division_preserves_irreducible_leading D C.
Defined.

(** Artin separation proves uniqueness of the division output, so the
    stronger normal-form interface follows without another certificate. *)
Theorem displayed_division_normal_form_of_existence
    (O : OI.admissible_monomial_order n)
    (E : literal_division_existence O) :
  @OI.displayed_division_normal_form F n O.
Proof.
refine {| OI.dnf := lde_remainder E |}.
- exact: (@lde_standard O E).
- exact: (@lde_congruent O E).
- move=> p s hs hps.
  have hsr : OI.literal_displayed_ideal F n
      (s - lde_remainder E p).
    have h := GI.generated_byB (@lde_congruent O E p) hps.
    have heq :
        (((p - lde_remainder E p) - (p - s))%R) =
        (s - lde_remainder E p)%R.
      by rewrite opprB addrC subrKA.
    rewrite heq in h.
    exact h.
  have hzero := literal_standard_displayed_ideal_zero
    (literal_standardB hs (@lde_standard O E p)) hsr.
  exact (subr0_eq hzero).
- exact: (@lde_preserves_irreducible_leading O E).
Qed.

(** The well-founded monic construction together with Artin separation gives
    a named normal-form object.  In particular no uniqueness record is
    supplied by a downstream caller. *)
Definition constructed_displayed_division_normal_form
    (O : OI.admissible_monomial_order n)
    (D : literal_order_support_data F O)
    (C : decidable_admissible_order O) :
  @OI.displayed_division_normal_form F n O :=
  displayed_division_normal_form_of_existence
    (constructed_literal_division_existence D C).

(** Explicit existence and uniqueness of the standard remainder for every
    paper order represented by a decidable comparison.  This conclusion is
    kept next to the reduced-Groebner endpoint so that "normal form" cannot
    be inferred merely from ideal equality or reduced tails. *)
Theorem exists_unique_literal_standard_remainder_of_paper_order
    (O : OI.admissible_monomial_order n)
    (H : OI.paper_order_hypotheses O)
    (C : decidable_admissible_order O) (p : Ambient) :
  exists r : Ambient,
    OI.literal_standard F n r /\
    OI.literal_displayed_ideal F n (p - r) /\
    forall s : Ambient,
      OI.literal_standard F n s ->
      OI.literal_displayed_ideal F n (p - s) -> s = r.
Proof.
pose D := @constructed_literal_order_support_data F n O H.
pose N := constructed_displayed_division_normal_form D C.
exists (OI.dnf N p); split.
- exact: OI.dnf_standard N p.
- split.
  + exact: OI.dnf_congruent N p.
  + move=> s hs hps.
    exact: OI.dnf_unique N p s hs hps.
Qed.

(** Compatibility endpoint retaining both records for downstream clients
    which already construct them explicitly. *)
Theorem literal_reduced_groebner_of_order_and_division_existence
    (O : OI.admissible_monomial_order n)
    (D : literal_order_support_data F O)
    (C : decidable_admissible_order O)
    (E : literal_division_existence O) :
  @OI.literal_reduced_groebner_certificate F n O.
Proof.
exact (OI.literal_reduced_groebner_of_order_and_division
  (literal_order_data_of_support_data D)
  (combined_leading_selection_of_decidable_order F C)
  (displayed_division_normal_form_of_existence E)).
Qed.

(** The division input of the preceding modular theorem is fully discharged. *)
Theorem literal_reduced_groebner_of_support_data
    (O : OI.admissible_monomial_order n)
    (D : literal_order_support_data F O)
    (C : decidable_admissible_order O) :
  @OI.literal_reduced_groebner_certificate F n O.
Proof.
exact: literal_reduced_groebner_of_order_and_division_existence
  D C (constructed_literal_division_existence D C).
Qed.

(** Full arbitrary-degree, arbitrary-paper-order endpoint.  Both formerly
    exposed mathematical certificate records are instantiated from the
    displayed formula and well-founded monic division.  The remaining
    arguments are exactly the paper's order hypotheses and a decision
    procedure for the order relation. *)
Theorem literal_reduced_groebner_of_paper_order
    (O : OI.admissible_monomial_order n)
    (H : OI.paper_order_hypotheses O)
    (C : decidable_admissible_order O) :
  @OI.literal_reduced_groebner_certificate F n O.
Proof.
pose D := @constructed_literal_order_support_data F n O H.
exact: literal_reduced_groebner_of_support_data D C.
Qed.

(** A constructive paper order bundles the mathematical admissible order,
    Lazard's two extra hypotheses, and the comparison procedure used to
    compute finite-support maxima.  All ordinary concrete monomial orders
    are represented this way.  Keeping this as data is honest about Coq's
    constructive scope: without classical choice, a completely arbitrary
    Prop-valued order does not yield a remainder function in [Type]. *)
Record decidable_paper_order : Type := DecidablePaperOrder {
  dpo_order : OI.admissible_monomial_order n;
  dpo_hypotheses : OI.paper_order_hypotheses dpo_order;
  dpo_decidable : decidable_admissible_order dpo_order
}.

(** Single-input form of the full arbitrary-degree constructive endpoint.
    No separate support, division, leading-term, or uniqueness certificate
    is exposed. *)
Theorem literal_reduced_groebner_of_decidable_paper_order
    (P : decidable_paper_order) :
  @OI.literal_reduced_groebner_certificate F n (dpo_order P).
Proof.
exact: literal_reduced_groebner_of_paper_order
  (dpo_hypotheses P) (dpo_decidable P).
Qed.

Theorem exists_unique_literal_standard_remainder_of_decidable_paper_order
    (P : decidable_paper_order) (p : Ambient) :
  exists r : Ambient,
    OI.literal_standard F n r /\
    OI.literal_displayed_ideal F n (p - r) /\
    forall s : Ambient,
      OI.literal_standard F n s ->
      OI.literal_displayed_ideal F n (p - s) -> s = r.
Proof.
exact: exists_unique_literal_standard_remainder_of_paper_order
  (dpo_hypotheses P) (dpo_decidable P) p.
Qed.

(** * Prop-only division: removal of the decidability restriction

    The computable remainder function above necessarily asks for a decision
    procedure for the Prop-valued order.  The mathematical Groebner theorem
    itself lives in [Prop], however.  Finite-support maxima and well-founded
    division can therefore be constructed existentially using only totality
    in [Prop], with no classical-choice axiom. *)

Lemma sequence_maximum_exists
    (O : OI.admissible_monomial_order n)
    (a : Monomial) (s : seq Monomial) :
  exists z : Monomial,
    z \in a :: s /\
    forall x, x \in a :: s -> OI.amo_le O x z.
Proof.
elim: s a=> [|b s ih] a.
- exists a; split; first by rewrite in_cons eqxx.
  move=> x; rewrite in_cons in_nil orbF=> /eqP ->.
  exact: OI.amo_le_refl O a.
- have [z [hz hmax]] := ih b.
  have [haz|hza] := OI.amo_le_total O a z.
  + exists z; split.
    * rewrite in_cons; apply/orP; right.
      exact hz.
    * move=> x; rewrite in_cons=> /orP [/eqP ->|hx].
      -- exact: haz.
      -- exact: hmax x hx.
  + exists a; split; first by rewrite in_cons eqxx.
    move=> x; rewrite in_cons=> /orP [/eqP ->|hx].
    * exact: OI.amo_le_refl O a.
    * exact (OI.amo_le_trans (hmax x hx) hza).
Qed.

(** A leading monomial exists for every nonzero finite polynomial even when
    the order comparison is not supplied as computational data. *)
Theorem combined_leading_selection_of_order
    (O : OI.admissible_monomial_order n) :
  @OI.combined_leading_selection F n O.
Proof.
constructor=> p hp0.
have hsne := combined_support_sequence_nonempty hp0.
case hs: (combined_support_sequence p) hsne=> [|a s] //= _.
have [z [hz hmax]] := sequence_maximum_exists O a s.
exists z; split.
- apply/combined_support_sequenceP.
  by rewrite hs.
- move=> b hb hbz; split; last exact: hbz.
  apply: hmax.
  move/combined_support_sequenceP: hb.
  by rewrite hs.
Qed.

Definition leading_term_at
    (p : Ambient) (a : Monomial) : Ambient :=
  ambient_scale (OI.combined_coefficient p a)
    (OI.combined_monomial_polynomial F n a).

Definition reduction_term_at
    (p : Ambient) (a : Monomial) (k : 'I_n) : Ambient :=
  (ambient_scale (OI.combined_coefficient p a)
      (OI.combined_monomial_polynomial F n
        (combined_sub a (OI.displayed_leading_monomial n k)))) *
    OI.literal_displayed_family F n k.

Lemma leading_term_at_coefficient p a :
  OI.combined_coefficient (leading_term_at p a) a =
    OI.combined_coefficient p a.
Proof.
rewrite /leading_term_at combined_coefficient_scale
  combined_monomial_coefficient_same mulr1.
exact: erefl.
Qed.

Lemma leading_term_at_support_upper
    (O : OI.admissible_monomial_order n) p a b :
  OI.combined_support (leading_term_at p a) b ->
  OI.amo_le O b a.
Proof.
move/combined_support_scale.
move/combined_monomial_support_single=> ->.
exact: OI.amo_le_refl O _.
Qed.

Lemma leading_term_at_standard p a :
  (forall k : 'I_n,
    ~ OI.combined_divides
      (OI.displayed_leading_monomial n k) a) ->
  OI.literal_standard F n (leading_term_at p a).
Proof.
move=> hnone b hb k.
have -> : b = a.
  apply: combined_monomial_support_single.
  exact: combined_support_scale hb.
exact: hnone k.
Qed.

Lemma reduction_term_at_coefficient
    (O : OI.admissible_monomial_order n)
    (D : literal_order_support_data F O) p a k
    (hk : OI.combined_divides
      (OI.displayed_leading_monomial n k) a) :
  OI.combined_coefficient (reduction_term_at p a k) a =
    OI.combined_coefficient p a.
Proof.
rewrite /reduction_term_at ambient_scale_mul combined_coefficient_scale.
set d := combined_sub a (OI.displayed_leading_monomial n k).
have hd : OI.combined_add d (OI.displayed_leading_monomial n k) = a.
  rewrite /d.
  exact: combined_subK hk.
have hmono :
    OI.combined_coefficient
      ((OI.combined_monomial_polynomial F n d *
        OI.literal_displayed_family F n k)%R) a =
    OI.combined_coefficient (OI.literal_displayed_family F n k)
      (OI.displayed_leading_monomial n k).
  rewrite -hd.
  exact: combined_coefficient_monomial_mul.
rewrite hmono (losd_monic D) mulr1.
exact: erefl.
Qed.

Lemma reduction_term_at_support_upper
    (O : OI.admissible_monomial_order n)
    (D : literal_order_support_data F O) p a k
    (hk : OI.combined_divides
      (OI.displayed_leading_monomial n k) a) b :
  OI.combined_support (reduction_term_at p a k) b ->
  OI.amo_le O b a.
Proof.
rewrite /reduction_term_at ambient_scale_mul.
move/combined_support_scale.
move/combined_support_monomial_mul=> [c [hc ->]].
have hclead : OI.amo_le O c (OI.displayed_leading_monomial n k).
  exact: is_leading_monomial_upper (losd_leading D k) hc.
have hadd := @combined_add_le_compat O c
  (OI.displayed_leading_monomial n k)
  (combined_sub a (OI.displayed_leading_monomial n k)) hclead.
by rewrite (combined_subK hk) in hadd.
Qed.

Lemma reduction_term_at_in_displayed_ideal p a k :
  OI.literal_displayed_ideal F n (reduction_term_at p a k).
Proof.
rewrite /reduction_term_at.
exact: GI.generated_by_mul_left
  (GI.generated_by_generator (OI.literal_displayed_family F n) k).
Qed.

Lemma leading_cancellation_strict_at
    (O : OI.admissible_monomial_order n)
    (p t : Ambient) (a b : Monomial) :
  OI.is_leading_monomial O p a ->
  OI.is_leading_monomial O (p - t) b ->
  OI.combined_coefficient t a = OI.combined_coefficient p a ->
  (forall c, OI.combined_support t c -> OI.amo_le O c a) ->
  OI.amo_lt O b a.
Proof.
move=> hpa hqb hcoeff ht; split.
- exact: leading_cancellation_support_upper hpa ht b hqb.1.
- move=> hba; subst b.
  have hzero := leading_cancellation_coefficient_zero hcoeff.
  exact: hqb.1 hzero.
Qed.

Definition propositional_division_result
    (O : OI.admissible_monomial_order n)
    (p : Ambient) (a : Monomial) (r : Ambient) : Prop :=
  OI.literal_standard F n r /\
  OI.literal_displayed_ideal F n (p - r) /\
  (forall b, OI.combined_support r b -> OI.amo_le O b a) /\
  ((forall k : 'I_n,
      ~ OI.combined_divides
        (OI.displayed_leading_monomial n k) a) ->
    OI.combined_coefficient r a = OI.combined_coefficient p a).

(** Well-founded monic division in [Prop].  The recursion follows an
    existentially selected leading monomial, so it needs no order-decision
    procedure and produces no hidden certificate input. *)
Theorem exists_propositional_division_from_leading
    (O : OI.admissible_monomial_order n)
    (D : literal_order_support_data F O) :
  forall a : Monomial, forall p : Ambient,
    OI.is_leading_monomial O p a ->
    exists r : Ambient, propositional_division_result O p a r.
Proof.
apply: (well_founded_induction (OI.amo_lt_well_founded O)
  (fun a => forall p : Ambient,
    OI.is_leading_monomial O p a ->
    exists r : Ambient, propositional_division_result O p a r)).
move=> a ih p hpa.
case: (pickP [pred k : 'I_n |
    OI.combined_divides (OI.displayed_leading_monomial n k) a]) =>
    [k hk|hnone].
- pose t := reduction_term_at p a k.
  pose q := p - t.
  case hqzero: (q == 0).
  + have hq0 : q = 0 := eqP hqzero.
    exists 0; split; first exact: OI.literal_standard0.
    split.
    * rewrite subr0.
      have hpterm : p = t.
        apply/eqP; rewrite -subr_eq0.
        apply/eqP.
        exact: hq0.
      rewrite hpterm /t.
      exact: reduction_term_at_in_displayed_ideal.
    * split.
      -- move=> b hb.
         exact: False_rect _ (OI.combined_zero_not_support hb).
      -- move=> hnone'.
         exact: False_rect _ (hnone' k hk).
  + have hq0 : q <> 0.
      move=> hq.
      by move: hqzero; rewrite hq eqxx.
    have [b hqb] := @OI.cls_leading_exists F n O
      (combined_leading_selection_of_order O) q hq0.
    have hba : OI.amo_lt O b a.
      apply: (@leading_cancellation_strict_at O p t a b hpa hqb).
      - exact: (@reduction_term_at_coefficient O D p a k hk).
      - exact: (@reduction_term_at_support_upper O D p a k hk).
    have [r [hrstandard [hrcongruent [hrupper hrpreserve]]]] :=
      ih b hba q hqb.
    exists r; split; first exact: hrstandard.
    split.
    * have h := GI.generated_byD
        (reduction_term_at_in_displayed_ideal p a k) hrcongruent.
      have heq : (p - r)%R = (t + (q - r))%R.
        apply: (addIr r).
        rewrite subrK addrA subrK /q.
        by rewrite addrC subrK.
      rewrite heq.
      exact h.
    * split.
      -- move=> c hc.
         exact: OI.amo_le_trans O _ _ _ (hrupper c hc) hba.1.
      -- move=> hnone'.
         exact: False_rect _ (hnone' k hk).
- have hnone' k :
      ~ OI.combined_divides (OI.displayed_leading_monomial n k) a.
    move=> hk.
    have hfalse := hnone k.
    change (OI.combined_divides
      (OI.displayed_leading_monomial n k) a = false) in hfalse.
    by move: hfalse; rewrite hk.
  pose t := leading_term_at p a.
  pose q := p - t.
  case hqzero: (q == 0).
  + have hq0 : q = 0 := eqP hqzero.
    exists t; split.
    * exact: leading_term_at_standard hnone'.
    * split.
      -- change (OI.literal_displayed_ideal F n q).
         rewrite hq0; exact: GI.generated_by0.
      -- split.
         ++ exact: leading_term_at_support_upper.
         ++ move=> _; exact: leading_term_at_coefficient.
  + have hq0 : q <> 0.
      move=> hq.
      by move: hqzero; rewrite hq eqxx.
    have [b hqb] := @OI.cls_leading_exists F n O
      (combined_leading_selection_of_order O) q hq0.
    have hba : OI.amo_lt O b a.
      apply: (@leading_cancellation_strict_at O p t a b hpa hqb).
      - exact: (@leading_term_at_coefficient p a).
      - exact: (@leading_term_at_support_upper O p a).
    have [r [hrstandard [hrcongruent [hrupper hrpreserve]]]] :=
      ih b hba q hqb.
    exists (t + r); split.
    * exact: literal_standardD
        (leading_term_at_standard hnone') hrstandard.
    * split.
      -- have heq : (p - (t + r))%R = (q - r)%R.
           rewrite /q /t opprD.
           by rewrite addrA.
         rewrite heq.
         exact hrcongruent.
      -- split.
         ++ move=> c hc.
            case: (combined_supportD_cases hc)=> hs.
            ** exact: leading_term_at_support_upper hs.
            ** exact: OI.amo_le_trans O _ _ _ (hrupper c hs) hba.1.
         ++ move=> _.
            rewrite combined_coefficientD leading_term_at_coefficient.
            have hrzero : OI.combined_coefficient r a = 0.
              case hzero: (OI.combined_coefficient r a == 0).
              ** exact: eqP hzero.
              ** have hrsupport : OI.combined_support r a.
                   move=> hra0.
                   by rewrite hra0 eqxx in hzero.
                 have hab := hrupper a hrsupport.
                 have heq := OI.amo_le_antisym hba.1 hab.
                 exact: False_rect _ (hba.2 heq).
            by rewrite hrzero addr0.
Qed.

Theorem exists_propositional_division
    (O : OI.admissible_monomial_order n)
    (D : literal_order_support_data F O) (p : Ambient) :
  exists r : Ambient,
    OI.literal_standard F n r /\
    OI.literal_displayed_ideal F n (p - r) /\
    forall a, OI.is_leading_monomial O p a ->
      (forall k : 'I_n,
        ~ OI.combined_divides
          (OI.displayed_leading_monomial n k) a) ->
      OI.combined_coefficient r a = OI.combined_coefficient p a.
Proof.
case hpzero: (p == 0).
- move/eqP: hpzero=> ->.
  exists 0; split; first exact: OI.literal_standard0.
  split; first by rewrite subrr; exact: GI.generated_by0.
  move=> a ha.
  exact: False_rect _ (OI.combined_zero_not_support ha.1).
- have hp0 : p <> 0.
    move=> hp; subst p.
    by rewrite eqxx in hpzero.
  have [a hpa] := @OI.cls_leading_exists F n O
    (combined_leading_selection_of_order O) p hp0.
  have [r [hrstandard [hrcongruent [_ hrpreserve]]]] :=
    exists_propositional_division_from_leading D hpa.
  exists r; split; first exact: hrstandard.
  split; first exact: hrcongruent.
  move=> b hpb hnone.
  have hba : b = a := is_leading_monomial_unique hpb hpa.
  subst b.
  exact: hrpreserve hnone.
Qed.

Theorem exists_unique_literal_standard_remainder_of_arbitrary_paper_order
    (O : OI.admissible_monomial_order n)
    (H : OI.paper_order_hypotheses O) (p : Ambient) :
  exists r : Ambient,
    OI.literal_standard F n r /\
    OI.literal_displayed_ideal F n (p - r) /\
    forall s : Ambient,
      OI.literal_standard F n s ->
      OI.literal_displayed_ideal F n (p - s) -> s = r.
Proof.
pose D := @constructed_literal_order_support_data F n O H.
have [r [hrstandard [hrcongruent _]]] :=
  exists_propositional_division D p.
exists r; split; first exact: hrstandard.
split; first exact: hrcongruent.
move=> s hs hps.
have hsr : OI.literal_displayed_ideal F n (s - r).
  have h := GI.generated_byB hrcongruent hps.
  have heq : (((p - r) - (p - s))%R) = (s - r)%R.
    by rewrite opprB addrC subrKA.
  rewrite heq in h.
  exact h.
have hzero := literal_standard_displayed_ideal_zero
  (literal_standardB hs hrstandard) hsr.
apply/eqP; rewrite -subr_eq0.
apply/eqP.
exact: hzero.
Qed.

Theorem propositional_division_initial_divisibility
    (O : OI.admissible_monomial_order n)
    (D : literal_order_support_data F O)
    (p : Ambient) (a : Monomial) :
  OI.literal_displayed_ideal F n p ->
  p <> 0 ->
  OI.is_leading_monomial O p a ->
  exists k : 'I_n,
    OI.combined_divides (OI.displayed_leading_monomial n k) a.
Proof.
move=> hp hp0 hpa.
case hexists: [exists k : 'I_n,
    OI.combined_divides (OI.displayed_leading_monomial n k) a].
- have /existsP [k hk] := hexists.
  by exists k.
- have hnone k :
      ~ OI.combined_divides (OI.displayed_leading_monomial n k) a.
    move=> hk.
    have hsome : [exists j : 'I_n,
        OI.combined_divides (OI.displayed_leading_monomial n j) a].
      apply/existsP; by exists k.
    by move: hsome; rewrite hexists.
  have [r [hrstandard [hrcongruent hrpreserve]]] :=
    exists_propositional_division D p.
  have hrmem : OI.literal_displayed_ideal F n r.
    have h := GI.generated_byB hp hrcongruent.
    have heq : (p - (p - r))%R = r.
      by rewrite opprB addrC subrK.
    rewrite heq in h.
    exact h.
  have hrzero := literal_standard_displayed_ideal_zero hrstandard hrmem.
  have hcoeff := hrpreserve a hpa hnone.
  rewrite hrzero /OI.combined_coefficient !mcoeff0 in hcoeff.
  exact: False_rect _ (hpa.1 (esym hcoeff)).
Qed.

(** Literal Lemma 1 for every Prop-valued admissible paper order.  This is
    the noncomputable-in-the-programming-sense but fully constructive
    mathematical endpoint: no decision package and no classical axiom. *)
Theorem literal_reduced_groebner_of_arbitrary_paper_order
    (O : OI.admissible_monomial_order n)
    (H : OI.paper_order_hypotheses O) :
  @OI.literal_reduced_groebner_certificate F n O.
Proof.
pose D := @constructed_literal_order_support_data F n O H.
pose L := literal_order_data_of_support_data D.
constructor.
- exact: H.
- move=> p; exact: GC.conventional_printed_generated_ideal_eq_vieta.
- exact: losd_monic D.
- exact: losd_leading D.
- exact: displayed_leading_monomials_incomparable.
- exact: losd_reduced_tails D.
- exact: OI.cls_leading_exists (combined_leading_selection_of_order O).
- exact: propositional_division_initial_divisibility D.
Qed.

(** Strongest single Prop endpoint for literal Lemma 1.  In addition to the
    reduced-Groebner/initial-ideal certificate it records the exact
    elementary-symmetric specialization kernel and existence and uniqueness
    of the standard remainder for every polynomial. *)
Definition literal_lemma_one_complete
    (O : OI.admissible_monomial_order n) : Prop :=
  @OI.literal_reduced_groebner_certificate F n O /\
  (forall p : Ambient,
    formal_specialization p = 0 <->
      OI.literal_displayed_ideal F n p) /\
  (forall p : Ambient, exists r : Ambient,
    OI.literal_standard F n r /\
    OI.literal_displayed_ideal F n (p - r) /\
    forall s : Ambient,
      OI.literal_standard F n s ->
      OI.literal_displayed_ideal F n (p - s) -> s = r).

Theorem literal_lemma_one_complete_of_arbitrary_paper_order
    (O : OI.admissible_monomial_order n)
    (H : OI.paper_order_hypotheses O) :
  literal_lemma_one_complete O.
Proof.
split.
- exact: literal_reduced_groebner_of_arbitrary_paper_order H.
- split.
  + move=> p; exact: formal_specialization_kernel_displayed.
  + move=> p.
    exact: exists_unique_literal_standard_remainder_of_arbitrary_paper_order H p.
Qed.

End PaperArtinBasis.

End PolynomialFormulasLazardDisplayedGroebnerGeneralOrderPort.
