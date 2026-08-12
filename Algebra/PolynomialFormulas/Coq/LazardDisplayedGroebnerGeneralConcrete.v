From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import LazardDisplayedGroebnerGeneralIdeal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A concrete finite-coefficient realization of the all-degrees displayed
    family.

    No formal-power-series library is used.  Instead we construct, to a
    requested finite precision, the inverse of a polynomial whose constant
    coefficient is one.  For the [k]th displayed relation we multiply the
    inverse of the full signed elementary series by the signed elementary
    product in the final [k] roots.  The source below proves the full
    elementary-product factorization, exposes an independent conventional
    complete-homogeneous definition, and identifies it coefficientwise with
    the finite quotient through the required precision.

    Only coefficients through degree [k+1] are relevant.  The finite inverse
    is therefore both sufficient and more honest than postulating an
    infinite-series operation that MathComp multinomials do not provide. *)
Module PolynomialFormulasLazardDisplayedGroebnerGeneralConcrete.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope mpoly_scope.

Module Core := PolynomialFormulasLazardDisplayedGroebnerGeneralIdeal.

(** * A finite inverse for a polynomial with constant coefficient one *)

Section FiniteInverse.

Variable A : comRingType.

(** [finite_inverse p d] has [d] computed coefficients.  At the successor
    step the new coefficient is chosen to make coefficient [d] of the
    product with [p] equal to the corresponding coefficient of one. *)
Fixpoint finite_inverse (p : {poly A}) (d : nat) : {poly A} :=
  match d with
  | 0 => 0
  | r.+1 =>
      let q := finite_inverse p r in
      q + (((r == 0)%:R - (p * q)`_r) *: 'X^r)
  end.

(** The construction is an inverse in every coefficient below its finite
    precision. *)
Theorem finite_inverse_spec (p : {poly A})
    (p0 : p`_0 = 1) (d r : nat) :
  (r < d)%N ->
  (p * finite_inverse p d)`_r = (r == 0)%:R.
Proof.
elim: d r => [r|d ih r] //=.
rewrite ltnS leq_eqVlt => /orP [/eqP ->|hrd].
- rewrite mulrDr coefD -scalerAr coefZ coefMXn ltnn subnn p0 mulr1.
  exact: subrKC.
- rewrite mulrDr coefD -scalerAr coefZ coefMXn hrd mulr0 addr0.
  exact: ih hrd.
Qed.

(** The quotient coefficients are built low-to-high in a polynomial table.
    At stage [r+1], the correction in degree [r] is chosen to make coefficient
    [r] of [p * q] equal to [s_r].  Recursing on the precision (rather than on
    a course-of-values coefficient index) keeps this an ordinary structurally
    recursive Coq definition. *)
Fixpoint finite_quotient_poly
    (p s : {poly A}) (d : nat) : {poly A} :=
  match d with
  | 0 => 0
  | r.+1 =>
      let q := finite_quotient_poly p s r in
      q + ((s`_r - (p * q)`_r) *: 'X^r)
  end.

(** The coefficient exposed by the finite quotient recurrence at its first
    precision containing that coefficient. *)
Definition finite_quotient_recurrence
    (p s : {poly A}) (r : nat) : A :=
  (finite_quotient_poly p s r.+1)`_r.

Lemma finite_quotient_poly_size p s (d : nat) :
  (size (finite_quotient_poly p s d) <= d)%N.
Proof.
elim: d => [|d ih] /=; first by rewrite size_poly0.
apply: leq_trans (size_polyD _ _) _.
rewrite geq_max; apply/andP; split.
- exact: leq_trans ih (leqnSn d).
- have hs := size_scale_leq
    (s`_d - (p * finite_quotient_poly p s d)`_d)
    ('X^d : {poly A}).
  by rewrite size_polyXn in hs.
Qed.

(** Once a coefficient has been constructed, later precision steps leave it
    unchanged; the added monomial is always in the new top degree. *)
Lemma finite_quotient_poly_coeff p s (d r : nat) :
  (r < d)%N ->
  (finite_quotient_poly p s d)`_r =
    finite_quotient_recurrence p s r.
Proof.
elim: d r => [r|d ih r] //=.
rewrite ltnS leq_eqVlt => /orP [/eqP ->|hrd].
- exact: erefl.
- rewrite coefD coefZ coefXn (ltn_eqF hrd) mulr0 addr0.
  exact: ih _ hrd.
Qed.

Theorem finite_quotient_poly_spec (p s : {poly A})
    (p0 : p`_0 = 1) (d r : nat) :
  (r < d)%N ->
  (p * finite_quotient_poly p s d)`_r = s`_r.
Proof.
elim: d r => [r|d ih r] //=.
rewrite ltnS leq_eqVlt => /orP [/eqP ->|hrd].
- rewrite mulrDr coefD -scalerAr coefZ coefMXn ltnn subnn p0 mulr1.
  exact: subrKC.
- rewrite mulrDr coefD -scalerAr coefZ coefMXn hrd mulr0 addr0.
  exact: ih hrd.
Qed.

(** Two finite solutions of the same coefficient equation with constant
    coefficient one agree coefficientwise. *)
Theorem finite_product_solution_unique
    (p s q1 q2 : {poly A}) (p0 : p`_0 = 1) (d : nat)
    (hproduct1 : forall r : nat, (r < d)%N -> (p * q1)`_r = s`_r)
    (hproduct2 : forall r : nat, (r < d)%N -> (p * q2)`_r = s`_r) :
  forall r : nat, (r < d)%N -> q1`_r = q2`_r.
Proof.
move=> r; elim: r {-2} r (leqnn r) => [|j ih] r.
- rewrite leqn0 => /eqP -> hr.
  have h1 := hproduct1 0 hr.
  have h2 := hproduct2 0 hr.
  rewrite coef0M p0 mul1r in h1.
  rewrite coef0M p0 mul1r in h2.
  by rewrite h1 h2.
- rewrite leq_eqVlt ltnS => /orP [/eqP ->|hrj] hr; last first.
    exact: ih r hrj hr.
  have h1 := hproduct1 j.+1 hr.
  have h2 := hproduct2 j.+1 hr.
  rewrite coefM big_ord_recl /= p0 mul1r subn0 in h1.
  rewrite coefM big_ord_recl /= p0 mul1r subn0 in h2.
  have hlow (i : 'I_j.+1) : q1`_(j - i) = q2`_(j - i).
    apply: ih.
    + exact: leq_subr i j.
    + exact: ltn_trans
        (leq_ltn_trans (leq_subr i j) (ltnSn j)) hr.
  have hsum1 :
      (\sum_(i < j.+1)
        p`_(bump 0 i) * q1`_(j.+1 - bump 0 i)) =
      \sum_(i < j.+1) p`_i.+1 * q2`_(j - i).
    apply: eq_bigr => i _.
    by rewrite /bump /= subSS hlow.
  have hsum2 :
      (\sum_(i < j.+1)
        p`_(bump 0 i) * q2`_(j.+1 - bump 0 i)) =
      \sum_(i < j.+1) p`_i.+1 * q2`_(j - i).
    apply: eq_bigr => i _.
    by rewrite /bump /= subSS.
  rewrite hsum1 in h1.
  rewrite hsum2 in h2.
  apply: (addIr (\sum_(i < j.+1) p`_i.+1 * q2`_(j - i))).
  by rewrite h1 h2.
Qed.

(** Any finite coefficient solution of [p * q = s], with [p_0 = 1], has
    the coefficients computed by the structural low-to-high quotient above. *)
Theorem finite_quotient_recurrence_unique
    (p s q : {poly A}) (p0 : p`_0 = 1) (d : nat)
    (hproduct : forall r : nat, (r < d)%N -> (p * q)`_r = s`_r) :
  forall r : nat, (r < d)%N ->
    q`_r = finite_quotient_recurrence p s r.
Proof.
move=> r hr.
rewrite /finite_quotient_recurrence.
have hproduct1 : forall j : nat, (j < r.+1)%N -> (p * q)`_j = s`_j.
  move=> j hj.
  exact: hproduct j (leq_trans hj hr).
have hproduct2 : forall j : nat, (j < r.+1)%N ->
    (p * finite_quotient_poly p s r.+1)`_j = s`_j.
  move=> j hj.
  exact (@finite_quotient_poly_spec p s p0 r.+1 j hj).
exact (@finite_product_solution_unique p s q
  (finite_quotient_poly p s r.+1) p0 r.+1 hproduct1 hproduct2
  r (ltnSn r)).
Qed.

End FiniteInverse.

(** * Signed elementary series as an actual product *)

(** MathComp's library theorem [Viete] is stated for the reversed monic
    product over [int].  The following orientation is the one needed here and
    is proved directly over an arbitrary commutative ring. *)
Section SignedElementaryProduct.

Variable A : comRingType.

Definition signed_elementary_series (m : nat) :
    {poly {mpoly A[m]}} :=
  \poly_(r < m.+1)
    ((-1 : {mpoly A[m]}) ^+ r * mesym m A r).

Definition signed_elementary_product (m : nat) :
    {poly {mpoly A[m]}} :=
  \prod_(i < m)
    (1 - ('X_i : {mpoly A[m]}) *: 'X).

Lemma signed_elementary_series_coeff m r :
  (signed_elementary_series m)`_r =
    (-1 : {mpoly A[m]}) ^+ r * mesym m A r.
Proof.
rewrite /signed_elementary_series coef_poly.
case: ltnP => // hmr.
by rewrite mesym_geqnE ?mulr0.
Qed.

Lemma signed_elementary_series_succ m :
  signed_elementary_series m.+1 =
    mpwiden (signed_elementary_series m) *
      (1 - ('X_(ord_max) : {mpoly A[m.+1]}) *: 'X).
Proof.
apply/polyP => r.
rewrite signed_elementary_series_coeff mulrBr mulr1 coefB.
rewrite -scalerAr coefZ coefMX /mpwiden !coef_map.
rewrite !signed_elementary_series_coeff.
case: r => [|r] /=.
- by rewrite expr0 !mesym0E !mul1r mwiden1 mulr0 subr0.
- rewrite mesymSS mulrDr !mwidenM !rmorphXn.
  rewrite exprS mulN1r.
  have hmul :
      (-1 : {mpoly A[m.+1]}) ^+ r *
          (mwiden (mesym m A r) * 'X_(ord_max)) =
        'X_(ord_max) *
          ((-1 : {mpoly A[m.+1]}) ^+ r * mwiden (mesym m A r)).
    by rewrite mulrA mulrC.
  rewrite !rmorphN !rmorph1 exprS mulN1r.
  by rewrite !mulNr hmul.
Qed.

Lemma signed_elementary_product_succ m :
  signed_elementary_product m.+1 =
    mpwiden (signed_elementary_product m) *
      (1 - ('X_(ord_max) : {mpoly A[m.+1]}) *: 'X).
Proof.
rewrite /signed_elementary_product big_ord_recr /=.
congr (_ * _).
rewrite /mpwiden rmorph_prod /=.
apply: eq_bigr => i _.
rewrite raddfB /= map_polyC map_polyZ map_polyX /=.
by rewrite mwiden1 mwidenX mnmwiden1.
Qed.

Theorem signed_elementary_series_product m :
  signed_elementary_series m = signed_elementary_product m.
Proof.
elim: m => [|m ih].
- apply/polyP => r.
  rewrite signed_elementary_series_coeff /signed_elementary_product big_ord0
    coef1.
  case: r => [|r].
  + by rewrite expr0 mesym0E mul1r eqxx.
  + by rewrite mesym_geqnE ?mulr0.
- by rewrite signed_elementary_series_succ
    signed_elementary_product_succ ih.
Qed.

End SignedElementaryProduct.

(** * Concrete nested multinomials *)

Section ConcreteFamily.

Variables (R : comRingType) (n : nat).

Local Notation Coeff := {mpoly R[n]}.
Local Notation Ambient := {mpoly Coeff[n]}.
Local Notation Series := {poly Ambient}.

Definition root_x (i : 'I_n) : Ambient := 'X_i.

(** The elementary symmetric coefficient in all [n] root variables. *)
Definition concrete_sigma (r : nat) : Ambient := mesym n Coeff r.

(** Independent formal coefficients [e_1,...,e_n], together with [e_0=1]
    and zero extension above degree [n]. *)
Definition concrete_formal_e (r : nat) : Ambient :=
  if r is j.+1 then
    if insub j : option 'I_n is Some i then
      (('X_i : Coeff))%:MP
    else 0
  else 1.

Lemma concrete_sigma0 : concrete_sigma 0 = 1.
Proof. by rewrite /concrete_sigma mesym0E. Qed.

Lemma concrete_formal_e0 : concrete_formal_e 0 = 1.
Proof. exact: erefl. Qed.

Lemma concrete_formal_e_succ (i : 'I_n) :
  concrete_formal_e i.+1 = (('X_i : Coeff))%:MP.
Proof.
by rewrite /concrete_formal_e /= valK.
Qed.

(** The full signed elementary generating polynomial

    [sum_r (-1)^r sigma_r T^r]. *)
Definition full_elementary_series : Series :=
  \poly_(r < n.+1)
    ((-1 : Ambient) ^+ r * concrete_sigma r).

Lemma full_elementary_series_coeff r (hr : (r < n.+1)%N) :
  full_elementary_series`_r =
    (-1 : Ambient) ^+ r * concrete_sigma r.
Proof. by rewrite /full_elementary_series coef_poly hr. Qed.

Lemma full_elementary_series0 : full_elementary_series`_0 = 1.
Proof.
by rewrite full_elementary_series_coeff ?ltn0Sn //
  expr0 concrete_sigma0 mul1r.
Qed.

(** The final [k] roots are represented by the right summand in
    ['I_(n-k) + 'I_k]. *)
Definition suffix_total_eq (k : 'I_n) : ((n - k)%N) + k = n :=
  subnK (ltnW (ltn_ord k)).

Definition suffix_index (k : 'I_n) (j : 'I_k) : 'I_n :=
  cast_ord (suffix_total_eq k) (rshift ((n - k)%N) j).

(** The complementary first [n-k] roots are represented by the left summand
    in the same ordinal decomposition. *)
Definition prefix_index (k : 'I_n) (j : 'I_(n - k)) : 'I_n :=
  cast_ord (suffix_total_eq k) (lshift k j).

(** The conventional complete homogeneous polynomial of degree [r] in a
    finite sequence of variables.  The exponent [i] assigned to the head and
    the recursively chosen exponents on the tail range over all weak
    compositions of [r], so every monomial of total degree [r] occurs once. *)
Fixpoint complete_homogeneous_seq
    (xs : seq Ambient) (r : nat) : Ambient :=
  match xs with
  | [::] => (r == 0)%:R
  | x :: xs' =>
      \sum_(i < r.+1)
        x ^+ i * complete_homogeneous_seq xs' ((r - i)%N)
  end.

Lemma complete_homogeneous_seq0 xs :
  complete_homogeneous_seq xs 0 = 1.
Proof.
elim: xs => [|x xs ih] /=; first by [].
by rewrite big_ord1 expr0 subn0 ih !mul1r.
Qed.

Definition prefix_root_tuple (k : 'I_n) : (n - k).-tuple Ambient :=
  [tuple root_x (prefix_index (k := k) j) | j < n - k].

(** This definition is independent of the finite-series quotient below: it is
    the literal sum of all monomials of degree [r] in the prefix roots. *)
Definition conventional_prefix_h (k : 'I_n) (r : nat) : Ambient :=
  complete_homogeneous_seq (prefix_root_tuple k) r.

Lemma conventional_prefix_h0 (k : 'I_n) :
  conventional_prefix_h k 0 = 1.
Proof. exact: complete_homogeneous_seq0 _. Qed.

Lemma complete_homogeneous_seq_consS x xs r :
  complete_homogeneous_seq (x :: xs) r.+1 =
    complete_homogeneous_seq xs r.+1 +
      x * complete_homogeneous_seq (x :: xs) r.
Proof.
rewrite /= [LHS]big_ord_recl /= expr0 mul1r subn0.
congr (_ + _).
rewrite mulr_sumr.
apply: eq_bigr => i _.
by rewrite /bump /= exprS subSS mulrA.
Qed.

Definition complete_homogeneous_series
    (xs : seq Ambient) (d : nat) : Series :=
  \poly_(r < d) complete_homogeneous_seq xs r.

Lemma complete_homogeneous_series_coeff xs d r (hr : (r < d)%N) :
  (complete_homogeneous_series xs d)`_r =
    complete_homogeneous_seq xs r.
Proof. by rewrite /complete_homogeneous_series coef_poly hr. Qed.

(** Multiplication by the head linear factor removes that head from the
    complete-homogeneous series, coefficientwise below the truncation. *)
Lemma complete_homogeneous_linear_step x xs d r (hr : (r < d)%N) :
  ((1 - x *: 'X) * complete_homogeneous_series (x :: xs) d)`_r =
    (complete_homogeneous_series xs d)`_r.
Proof.
rewrite mulrBl mul1r coefB -scalerAl coefZ coefXM.
case: r hr => [|r] hr /=.
- by rewrite !complete_homogeneous_series_coeff //
    !complete_homogeneous_seq0 mulr0 subr0.
- have hrd : (r < d)%N := ltn_trans (ltnSn r) hr.
  rewrite !complete_homogeneous_series_coeff //.
  by rewrite complete_homogeneous_seq_consS addrK.
Qed.

Definition signed_elementary_seq_product (xs : seq Ambient) : Series :=
  \prod_(x <- xs) (1 - x *: 'X).

(** The weak-composition definition is the finite inverse of the literal
    signed elementary product. *)
Theorem complete_homogeneous_series_inverse xs d r (hr : (r < d)%N) :
  (signed_elementary_seq_product xs *
      complete_homogeneous_series xs d)`_r = (r == 0)%:R.
Proof.
elim: xs => [|x xs ih] in r hr *.
- by rewrite /signed_elementary_seq_product big_nil mul1r
    complete_homogeneous_series_coeff //=.
- rewrite /signed_elementary_seq_product big_cons -mulrA mulrCA coefM.
  have hsum :
      (\sum_(j < r.+1)
        (\prod_(y <- xs) (1 - y *: 'X))`_j *
        ((1 - x *: 'X) * complete_homogeneous_series (x :: xs) d)`_
          (r - j)) =
      \sum_(j < r.+1)
        (\prod_(y <- xs) (1 - y *: 'X))`_j *
        (complete_homogeneous_series xs d)`_(r - j).
    apply: eq_bigr => j _.
    rewrite (complete_homogeneous_linear_step x xs
      (d := d) (r := r - j)
      (leq_ltn_trans (leq_subr j r) hr)).
    exact: erefl.
  rewrite hsum.
  rewrite -coefM.
  exact: ih r hr.
Qed.

(** Actual signed elementary product in the first [n-k] roots. *)
Definition prefix_elementary_series (k : 'I_n) : Series :=
  \prod_(j < n - k)
    (1 - root_x (prefix_index (k := k) j) *: 'X).

Lemma prefix_elementary_seriesE (k : 'I_n) :
  prefix_elementary_series k =
    signed_elementary_seq_product (prefix_root_tuple k).
Proof.
rewrite /prefix_elementary_series /signed_elementary_seq_product
  /prefix_root_tuple big_tuple.
apply: eq_bigr => j _.
by rewrite tnth_mktuple.
Qed.

Lemma prefix_elementary_series0 (k : 'I_n) :
  (prefix_elementary_series k)`_0 = 1.
Proof.
rewrite /prefix_elementary_series coef0_prod.
apply: big1 => j _.
rewrite coefB coef1 coefZ coefX.
by rewrite eqxx /= mulr0 subr0.
Qed.

(** Actual signed elementary product in the final [k] roots. *)
Definition raw_suffix_elementary_series (k : 'I_n) : Series :=
  \prod_(j < k)
    (1 - root_x (suffix_index (k := k) j) *: 'X).

(** The product over all roots, indexed through the explicit
    ['I_(n-k) + 'I_k] decomposition. *)
Definition raw_full_elementary_series (k : 'I_n) : Series :=
  \prod_(i < (n - k) + k)
    (1 - root_x (cast_ord (suffix_total_eq k) i) *: 'X).

Lemma raw_full_elementary_series_split (k : 'I_n) :
  raw_full_elementary_series k =
    prefix_elementary_series k * raw_suffix_elementary_series k.
Proof.
by rewrite /raw_full_elementary_series /prefix_elementary_series
  /raw_suffix_elementary_series big_split_ord.
Qed.

(** The split indexing is only a transport of the ordinary product over
    ['I_n]. *)
Lemma raw_full_elementary_series_standard (k : 'I_n) :
  raw_full_elementary_series k =
    \prod_(i < n) (1 - root_x i *: 'X).
Proof.
rewrite /raw_full_elementary_series.
apply/esym.
apply: reindex.
exists (cast_ord (esym (suffix_total_eq k))) => [i _|i _].
- exact: cast_ordK (suffix_total_eq k) i.
- exact: cast_ordKV (suffix_total_eq k) i.
Qed.

(** The [mesym]-to-product bridge, kept as a named proposition so downstream
    statements can expose precisely which identity they use. *)
Definition full_elementary_product_bridge (k : 'I_n) : Prop :=
  full_elementary_series = raw_full_elementary_series k.

Theorem full_elementary_product_bridgeP (k : 'I_n) :
  full_elementary_product_bridge k.
Proof.
rewrite /full_elementary_product_bridge.
change ((@signed_elementary_series Coeff n) = raw_full_elementary_series k).
rewrite (@signed_elementary_series_product Coeff n).
exact: esym (raw_full_elementary_series_standard k).
Qed.

Lemma full_elementary_series_split (k : 'I_n) :
  full_elementary_series =
    prefix_elementary_series k * raw_suffix_elementary_series k.
Proof.
rewrite (full_elementary_product_bridgeP k).
exact: raw_full_elementary_series_split.
Qed.

Lemma signed_linear_factor_size (i : 'I_n) :
  (size (((1%R : Series) - root_x i *: 'X)%R) <= 2)%N.
Proof.
apply: (leq_trans (size_polyD (1 : Series) (-(root_x i *: 'X)))).
rewrite geq_max size_poly1 size_polyN.
apply/andP; split; first exact: leqnSn 1.
apply: (leq_trans (size_scale_leq _ _)).
by rewrite size_polyX.
Qed.

Lemma raw_suffix_elementary_series_size (k : 'I_n) :
  (size (raw_suffix_elementary_series k) <= k.+1)%N.
Proof.
have hbound :
    (size (raw_suffix_elementary_series k) <=
      (\sum_(j < k) 1).+1)%N.
  rewrite /raw_suffix_elementary_series.
  apply: (big_ind2 (fun (p : Series) (m : nat) =>
    (size p <= m.+1)%N)) =>
    [|p m q l hp hq|j _].
  - by rewrite size_poly1.
  - apply: leq_trans (size_polyMleq _ _) _.
    by rewrite -subn1 -addnS leq_subLR addnA leq_add.
  - exact: signed_linear_factor_size _.
move: hbound.
by rewrite sum1_card card_ord.
Qed.

(** Only degrees below [k+1] can contribute to the target coefficient.  The
    truncation is retained as an implementation detail, but the proved degree
    bound below shows that it is extensionally the genuine suffix product. *)
Definition suffix_elementary_series (k : 'I_n) : Series :=
  take_poly k.+1 (raw_suffix_elementary_series k).

Lemma suffix_elementary_seriesE (k : 'I_n) :
  suffix_elementary_series k = raw_suffix_elementary_series k.
Proof.
rewrite /suffix_elementary_series.
exact: take_poly_id (raw_suffix_elementary_series_size k).
Qed.

Lemma raw_suffix_elementary_series0 (k : 'I_n) :
  (raw_suffix_elementary_series k)`_0 = 1.
Proof.
rewrite /raw_suffix_elementary_series coef0_prod.
apply: big1 => j _.
rewrite coefB coef1 coefZ coefX.
by rewrite eqxx /= mulr0 subr0.
Qed.

Lemma suffix_elementary_series0 (k : 'I_n) :
  (suffix_elementary_series k)`_0 = 1.
Proof.
by rewrite suffix_elementary_seriesE raw_suffix_elementary_series0.
Qed.

Lemma suffix_elementary_series_top_coeff (k : 'I_n) :
  (suffix_elementary_series k)`_k.+1 = 0.
Proof.
rewrite suffix_elementary_seriesE nth_default //.
exact: raw_suffix_elementary_series_size k.
Qed.

(** We compute one coefficient beyond the displayed triangular tail. *)
Definition full_finite_inverse (k : 'I_n) : Series :=
  finite_inverse full_elementary_series k.+2.

Lemma full_finite_inverse0 (k : 'I_n) :
  (full_finite_inverse k)`_0 = 1.
Proof.
have h := finite_inverse_spec full_elementary_series0
  (r := 0) (d := k.+2) (ltn0Sn k.+1).
move: h.
by rewrite /full_finite_inverse coef0M full_elementary_series0
  mul1r eqxx.
Qed.

(** Finite quotient [E_suffix / E_full].  The theorem
    [concrete_prefix_h_finite_recurrence] below identifies its coefficients
    with the explicit quotient recurrence, and
    [concrete_prefix_h_eq_conventional] then identifies them with the
    independently defined weak-composition family [conventional_prefix_h]. *)
Definition prefix_complete_series (k : 'I_n) : Series :=
  full_finite_inverse k * suffix_elementary_series k.

Definition concrete_prefix_h (k : 'I_n) (r : nat) : Ambient :=
  (prefix_complete_series k)`_r.

Lemma concrete_prefix_h0 (k : 'I_n) : concrete_prefix_h k 0 = 1.
Proof.
by rewrite /concrete_prefix_h /prefix_complete_series coef0M
  full_finite_inverse0 suffix_elementary_series0 mul1r.
Qed.

(** The defining finite quotient identity in all degrees used by the [k]th
    displayed relation. *)
Lemma full_inverse_coeff (k : 'I_n) (j : 'I_k.+2) :
  (full_elementary_series * full_finite_inverse k)`_j =
    (j == 0)%:R.
Proof.
rewrite /full_finite_inverse.
exact (@finite_inverse_spec Ambient full_elementary_series
  full_elementary_series0 k.+2 j (ltn_ord j)).
Qed.

(** Up to the required finite precision, multiplication by the full
    elementary series sends the prefix-complete quotient back to the actual
    suffix elementary product.  This is the finite coefficient recursion
    replacing an infinite generating-series inverse. *)
Theorem prefix_complete_series_spec (k : 'I_n) (r : 'I_k.+2) :
  (full_elementary_series * prefix_complete_series k)`_r =
    (suffix_elementary_series k)`_r.
Proof.
have hinv (j : 'I_r.+1) :
    (full_elementary_series * full_finite_inverse k)`_j =
      (j == 0)%:R.
  rewrite /full_finite_inverse.
  exact (@finite_inverse_spec Ambient full_elementary_series
    full_elementary_series0 k.+2 j
    (leq_trans (ltn_ord j) (ltn_ord r))).
rewrite /prefix_complete_series mulrA coefM.
under eq_bigr => j _ do rewrite hinv.
rewrite (bigD1 ord0) //=.
rewrite mul1r subn0.
rewrite big1 ?addr0 // => j hj.
by rewrite (negbTE hj) mul0r.
Qed.

(** The quotient coefficients are not opaque consequences of
    [finite_inverse]: through every degree used by the displayed relation they
    are the unique coefficients obtained by the explicit low-to-high quotient
    recurrence. *)
Theorem concrete_prefix_h_finite_recurrence
    (k : 'I_n) r (hr : (r < k.+2)%N) :
  concrete_prefix_h k r =
    finite_quotient_recurrence
      full_elementary_series (suffix_elementary_series k) r.
Proof.
apply: (@finite_quotient_recurrence_unique Ambient
  full_elementary_series (suffix_elementary_series k)
  (prefix_complete_series k) full_elementary_series0 k.+2 _ r hr).
move=> j hj.
exact (@prefix_complete_series_spec k (Ordinal hj)).
Qed.

(** The constructed quotient is an inverse of the genuine prefix product in
    every required coefficient.  Cancellation of the suffix is performed by
    [finite_product_solution_unique], so no integral-domain hypothesis is
    hidden here. *)
Theorem prefix_complete_series_prefix_inverse
    (k : 'I_n) r (hr : (r < k.+2)%N) :
  (prefix_elementary_series k * prefix_complete_series k)`_r =
    (r == 0)%:R.
Proof.
have hconstructed j (hj : (j < k.+2)%N) :
    (suffix_elementary_series k *
      (prefix_elementary_series k * prefix_complete_series k))`_j =
    (suffix_elementary_series k)`_j.
  have h := @prefix_complete_series_spec k (Ordinal hj).
  rewrite (full_elementary_series_split k)
    -(suffix_elementary_seriesE k) -mulrA mulrCA in h.
  exact: h.
have hone j (hj : (j < k.+2)%N) :
    (suffix_elementary_series k * (1 : Series))`_j =
      (suffix_elementary_series k)`_j by rewrite mulr1.
have hunique := @finite_product_solution_unique Ambient
  (suffix_elementary_series k) (suffix_elementary_series k)
  (prefix_elementary_series k * prefix_complete_series k) 1
  (suffix_elementary_series0 k) k.+2 hconstructed hone.
move: (hunique r hr).
by rewrite coef1.
Qed.

Lemma conventional_prefix_series_inverse
    (k : 'I_n) d r (hr : (r < d)%N) :
  (prefix_elementary_series k *
      complete_homogeneous_series (prefix_root_tuple k) d)`_r =
    (r == 0)%:R.
Proof.
rewrite prefix_elementary_seriesE.
exact: complete_homogeneous_series_inverse hr.
Qed.

(** The independent weak-composition definition and the quotient construction
    agree through degree [k+1]. *)
Theorem concrete_prefix_h_eq_conventional
    (k : 'I_n) r (hr : (r < k.+2)%N) :
  concrete_prefix_h k r = conventional_prefix_h k r.
Proof.
have hquotient j (hj : (j < k.+2)%N) :
    (prefix_elementary_series k * prefix_complete_series k)`_j =
      (1 : Series)`_j.
  by rewrite prefix_complete_series_prefix_inverse // coef1.
have hconventional j (hj : (j < k.+2)%N) :
    (prefix_elementary_series k *
      complete_homogeneous_series (prefix_root_tuple k) k.+2)`_j =
      (1 : Series)`_j.
  by rewrite conventional_prefix_series_inverse // coef1.
have hunique := @finite_product_solution_unique Ambient
  (prefix_elementary_series k) 1
  (prefix_complete_series k)
  (complete_homogeneous_series (prefix_root_tuple k) k.+2)
  (prefix_elementary_series0 k) k.+2
  hquotient hconventional.
move: (hunique r hr).
by rewrite /concrete_prefix_h complete_homogeneous_series_coeff //
  /conventional_prefix_h.
Qed.

(** This discharges the sole abstract interface from the order-free core:
    the suffix has [k] variables and therefore contributes zero in degree
    [k+1]. *)
Theorem concrete_printed_cancellation (k : 'I_n) :
  Core.elementary_complete_convolution
      concrete_sigma (concrete_prefix_h k) k.+1 = 0.
Proof.
have hk2 : (k.+2 <= n.+1)%N by exact: ltn_ord k.
have hconv :
    Core.elementary_complete_convolution
        concrete_sigma (concrete_prefix_h k) k.+1 =
      (full_elementary_series * prefix_complete_series k)`_k.+1.
  rewrite /Core.elementary_complete_convolution coefM.
  apply: eq_bigr => j _.
  have hjn : (j < n.+1)%N := leq_trans (ltn_ord j) hk2.
  by rewrite /concrete_prefix_h (full_elementary_series_coeff hjn).
rewrite hconv (@prefix_complete_series_spec k ord_max).
exact: suffix_elementary_series_top_coeff k.
Qed.

(** The cancellation theorem for the literal conventional
    complete-homogeneous family. *)
Theorem conventional_printed_cancellation (k : 'I_n) :
  Core.elementary_complete_convolution
      concrete_sigma (conventional_prefix_h k) k.+1 = 0.
Proof.
rewrite /Core.elementary_complete_convolution.
under eq_bigr => j _ do
  rewrite -(concrete_prefix_h_eq_conventional (k := k) (r := k.+1 - j)
    (leq_ltn_trans (leq_subr j k.+1) (ltnSn k.+1))).
exact: concrete_printed_cancellation.
Qed.

(** * Unconditional instantiation of the generic ideal theorem *)

Definition concrete_vieta_relation : 'I_n -> Ambient :=
  @Core.vieta_relation Ambient n concrete_sigma concrete_formal_e.

Definition concrete_printed_displayed_J : 'I_n -> Ambient :=
  @Core.printed_displayed_J Ambient n
    concrete_formal_e concrete_prefix_h.

(** The literal printed family, now using the independently defined
    weak-composition complete homogeneous polynomials. *)
Definition conventional_printed_displayed_J : 'I_n -> Ambient :=
  @Core.printed_displayed_J Ambient n
    concrete_formal_e conventional_prefix_h.

Theorem concrete_printed_generated_ideal_eq_vieta (p : Ambient) :
  @Core.generated_by Ambient n concrete_printed_displayed_J p <->
  @Core.generated_by Ambient n concrete_vieta_relation p.
Proof.
exact: (@Core.printed_displayed_generated_ideal_eq_vieta
  Ambient n concrete_sigma concrete_formal_e concrete_prefix_h
  concrete_sigma0 concrete_formal_e0 concrete_prefix_h0
  concrete_printed_cancellation p).
Qed.

Theorem conventional_printed_generated_ideal_eq_vieta (p : Ambient) :
  @Core.generated_by Ambient n conventional_printed_displayed_J p <->
  @Core.generated_by Ambient n concrete_vieta_relation p.
Proof.
exact: (@Core.printed_displayed_generated_ideal_eq_vieta
  Ambient n concrete_sigma concrete_formal_e conventional_prefix_h
  concrete_sigma0 concrete_formal_e0 conventional_prefix_h0
  conventional_printed_cancellation p).
Qed.

End ConcreteFamily.

End PolynomialFormulasLazardDisplayedGroebnerGeneralConcrete.
