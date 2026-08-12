From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  SexticSparsePolynomials
  LazardQuinticRootFourierNumeratorP2Sparse
  LazardQuinticRootFourierNumeratorP3Common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Sparse semantics for the root-specialized P3 numerator.
    All canonical polynomial operations, root atoms, cyclic operations, and
    their semantic lemmas are reused from the P2 sparse checker. *)
Module PolynomialFormulasLazardQuinticRootFourierNumeratorP3Sparse.

Import GRing.Theory.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticFourierNumerators.
Module S := PolynomialFormulasLazardQuinticRootFourierNumeratorP2Sparse.
Module P3C := PolynomialFormulasLazardQuinticRootFourierNumeratorP3Common.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module C := PolynomialFormulasLazardQuinticRootFourierNumeratorCommon.
Module SP := PolynomialFormulasSexticSparsePolynomials.
Module SN := PolynomialFormulasSexticNewtonPowerSums.
Local Open Scope ring_scope.

(** The four P3 coefficients.  Each summand is closed before it is inserted
    into the fold-right sum, matching the bounded P2 proof pattern. *)
Definition sp31 : SP.sparse_polynomial :=
  S.sparse_canonical_scale (- 25%:Z) S.sq.

Definition sp32 : SP.sparse_polynomial :=
  S.sparse_canonical_scale 25%:Z (S.ssum [::
    S.sparse_canonical_scale (- 10%:Z) S.si8;
    S.sparse_canonical_scale 2%:Z
      (S.sparse_canonical_mul S.sp S.si6);
    S.sparse_canonical_scale (- 22%:Z)
      (S.sparse_canonical_mul S.sq S.si5);
    S.sparse_canonical_scale 2%:Z
      (S.sparse_canonical_mul (S.sparse_canonical_pow S.sp 2) S.si4);
    S.sparse_canonical_scale 20%:Z
      (S.sparse_canonical_mul (S.sparse_canonical_pow S.sp 2) S.sr);
    S.sparse_canonical_scale 2%:Z
      (S.sparse_canonical_mul S.sp (S.sparse_canonical_pow S.sq 2));
    S.sparse_canonical_scale (- 35%:Z)
      (S.sparse_canonical_mul S.sq S.ss);
    S.sparse_canonical_scale (- 40%:Z)
      (S.sparse_canonical_pow S.sr 2)]).

Definition sp33 : SP.sparse_polynomial :=
  S.sparse_canonical_scale 5%:Z (S.ssum [::
    S.sparse_canonical_scale 35%:Z S.si8;
    S.sparse_canonical_scale (- 4%:Z)
      (S.sparse_canonical_mul S.sp S.si6);
    S.sparse_canonical_scale 23%:Z
      (S.sparse_canonical_mul S.sq S.si5);
    S.sparse_canonical_mul
      (S.sparse_canonical_add
        (S.sparse_canonical_scale (- 6%:Z)
          (S.sparse_canonical_pow S.sp 2))
        (S.sparse_canonical_scale 12%:Z S.sr)) S.si4;
    S.sparse_canonical_scale (- 58%:Z)
      (S.sparse_canonical_mul (S.sparse_canonical_pow S.sp 2) S.sr);
    S.sparse_canonical_scale 14%:Z
      (S.sparse_canonical_mul S.sp (S.sparse_canonical_pow S.sq 2));
    S.sparse_canonical_scale (- 105%:Z)
      (S.sparse_canonical_mul S.sq S.ss);
    S.sparse_canonical_scale 76%:Z
      (S.sparse_canonical_pow S.sr 2)]).

Definition sp34 : SP.sparse_polynomial :=
  S.sparse_canonical_scale 5%:Z (S.ssum [::
    S.sparse_canonical_scale 5%:Z S.si8;
    S.sparse_canonical_scale (- 22%:Z)
      (S.sparse_canonical_mul S.sp S.si6);
    S.sparse_canonical_scale 14%:Z
      (S.sparse_canonical_mul S.sq S.si5);
    S.sparse_canonical_mul
      (S.sparse_canonical_add
        (S.sparse_canonical_scale (- 18%:Z)
          (S.sparse_canonical_pow S.sp 2))
        (S.sparse_canonical_scale 16%:Z S.sr)) S.si4;
    S.sparse_canonical_scale (- 34%:Z)
      (S.sparse_canonical_mul (S.sparse_canonical_pow S.sp 2) S.sr);
    S.sparse_canonical_scale 22%:Z
      (S.sparse_canonical_mul S.sp (S.sparse_canonical_pow S.sq 2));
    S.sparse_canonical_scale (- 140%:Z)
      (S.sparse_canonical_mul S.sq S.ss);
    S.sparse_canonical_scale 68%:Z
      (S.sparse_canonical_pow S.sr 2)]).

(** P3 uses Fourier exponents [0, 3, 1, 4, 2], hence the cyclic row
    [x0, x2, x4, x1, x3]. *)
Definition sparse_cyclic_fourier_P3 : S.SparseCyclicFive :=
  {| S.sparse_cyclic0 := S.sx0;
     S.sparse_cyclic1 := S.sx2;
     S.sparse_cyclic2 := S.sx4;
     S.sparse_cyclic3 := S.sx1;
     S.sparse_cyclic4 := S.sx3 |}.

(** These definitions mirror the parenthesization of P3Common exactly. *)
Definition sparse_p3_numerator_left : S.SparseCyclicFive :=
  S.sparse_cyclic_add
    (S.sparse_cyclic_scale
      (S.sparse_canonical_mul
        (S.sparse_canonical_mul
          (S.sparse_canonical_const 5) S.sroot_E) sp31)
      S.sparse_cyclic_epsilon)
    (S.sparse_cyclic_add
      (S.sparse_cyclic_constant
        (S.sparse_canonical_mul
          (S.sparse_canonical_mul
            (S.sparse_canonical_const 5) S.sroot_E) sp32))
      (S.sparse_cyclic_scale (S.sparse_canonical_const 2)
        (S.sparse_cyclic_mul S.sparse_cyclic_epsilon
          (S.sparse_cyclic_add
            (S.sparse_cyclic_scale sp33 S.sparse_cyclic_T)
            (S.sparse_cyclic_scale sp34 S.sparse_cyclic_formula_U))))).

Definition sparse_p3_numerator_right : S.SparseCyclicFive :=
  S.sparse_cyclic_scale
    (S.sparse_canonical_scale 20%:Z S.sroot_E)
    (S.sparse_cyclic_mul S.sparse_cyclic_epsilon
      (S.sparse_cyclic_mul
        (S.sparse_cyclic_mul S.sparse_cyclic_fourier_P1
          S.sparse_cyclic_fourier_P1)
        sparse_cyclic_fourier_P3)).

Definition sparse_p3_numerator_difference : S.SparseCyclicFive :=
  S.sparse_cyclic_sub sparse_p3_numerator_left
    sparse_p3_numerator_right.

(** Semantic bridge to the public field-valued P3 definitions. *)
Section SemanticBridge.
Variable F : fieldType.
Variable roots : 5.-tuple F.
Let values := S.sparse_root_values roots.

(** Avoid expanding the already certified P2 root atoms while proving the
    small P3 coefficient semantics.  They are restored to transparency
    below so the generated [vm_compute] leaves can reduce them. *)
Opaque S.sp S.sq S.sr S.ss S.si4 S.si5 S.si6 S.si7 S.si8.

Lemma add8_right_assoc (a b c d e f g h : F) :
  (((((((a + b) + c) + d) + e) + f) + g) + h) =
    a + (b + (c + (d + (e + (f + (g + h)))))).
Proof. by rewrite !addrA. Qed.

(** Closed atom composites shared by P32--P34. *)
Lemma eval_sp_si6_mul_atom :
  SN.sparse_eval_ring values (S.sparse_canonical_mul S.sp S.si6) =
    SN.sparse_eval_ring values S.sp *
      SN.sparse_eval_ring values S.si6.
Proof. exact: S.sparse_canonical_mul_eval. Qed.

Lemma eval_sq_si5_mul_atom :
  SN.sparse_eval_ring values (S.sparse_canonical_mul S.sq S.si5) =
    SN.sparse_eval_ring values S.sq *
      SN.sparse_eval_ring values S.si5.
Proof. exact: S.sparse_canonical_mul_eval. Qed.

Lemma eval_sp_square_si4_mul_atom :
  SN.sparse_eval_ring values
      (S.sparse_canonical_mul (S.sparse_canonical_pow S.sp 2) S.si4) =
    SN.sparse_eval_ring values S.sp ^+ 2 *
      SN.sparse_eval_ring values S.si4.
Proof.
rewrite [LHS]S.sparse_canonical_mul_eval.
by rewrite S.sparse_canonical_pow_eval.
Qed.

Lemma eval_sp_square_sr_mul_atom :
  SN.sparse_eval_ring values
      (S.sparse_canonical_mul (S.sparse_canonical_pow S.sp 2) S.sr) =
    SN.sparse_eval_ring values S.sp ^+ 2 *
      SN.sparse_eval_ring values S.sr.
Proof.
rewrite [LHS]S.sparse_canonical_mul_eval.
by rewrite S.sparse_canonical_pow_eval.
Qed.

Lemma eval_sq_square_atom :
  SN.sparse_eval_ring values (S.sparse_canonical_pow S.sq 2) =
    SN.sparse_eval_ring values S.sq ^+ 2.
Proof. exact: S.sparse_canonical_pow_eval. Qed.

Lemma eval_sp_sq_square_mul_atom :
  SN.sparse_eval_ring values
      (S.sparse_canonical_mul S.sp (S.sparse_canonical_pow S.sq 2)) =
    SN.sparse_eval_ring values S.sp *
      SN.sparse_eval_ring values S.sq ^+ 2.
Proof.
rewrite [LHS]S.sparse_canonical_mul_eval.
by rewrite eval_sq_square_atom.
Qed.

Lemma eval_sq_ss_mul_atom :
  SN.sparse_eval_ring values (S.sparse_canonical_mul S.sq S.ss) =
    SN.sparse_eval_ring values S.sq *
      SN.sparse_eval_ring values S.ss.
Proof. exact: S.sparse_canonical_mul_eval. Qed.

Lemma eval_sr_square_atom :
  SN.sparse_eval_ring values (S.sparse_canonical_pow S.sr 2) =
    SN.sparse_eval_ring values S.sr ^+ 2.
Proof. exact: S.sparse_canonical_pow_eval. Qed.

(** P31 is one closed summand. *)
Lemma eval_sp31_structure :
  SN.sparse_eval_ring values sp31 =
    - (25%:R * SN.sparse_eval_ring values S.sq).
Proof.
rewrite /sp31 [LHS]S.sparse_canonical_scale_neg_nat_eval.
reflexivity.
Qed.

(** The eight closed P32 summands. *)
Lemma eval_sp32_i8_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale (- 10%:Z) S.si8) =
    - (10%:R * SN.sparse_eval_ring values S.si8).
Proof. by rewrite [LHS]S.sparse_canonical_scale_neg_nat_eval. Qed.

Lemma eval_sp32_p_i6_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale 2%:Z
        (S.sparse_canonical_mul S.sp S.si6)) =
    2%:R * (SN.sparse_eval_ring values S.sp *
      SN.sparse_eval_ring values S.si6).
Proof.
rewrite [LHS]S.sparse_canonical_scale_nat_eval.
by rewrite eval_sp_si6_mul_atom.
Qed.

Lemma eval_sp32_q_i5_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale (- 22%:Z)
        (S.sparse_canonical_mul S.sq S.si5)) =
    - (22%:R * (SN.sparse_eval_ring values S.sq *
      SN.sparse_eval_ring values S.si5)).
Proof.
rewrite [LHS]S.sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sq_si5_mul_atom.
Qed.

Lemma eval_sp32_p_square_i4_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale 2%:Z
        (S.sparse_canonical_mul
          (S.sparse_canonical_pow S.sp 2) S.si4)) =
    2%:R * (SN.sparse_eval_ring values S.sp ^+ 2 *
      SN.sparse_eval_ring values S.si4).
Proof.
rewrite [LHS]S.sparse_canonical_scale_nat_eval.
by rewrite eval_sp_square_si4_mul_atom.
Qed.

Lemma eval_sp32_p_square_r_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale 20%:Z
        (S.sparse_canonical_mul
          (S.sparse_canonical_pow S.sp 2) S.sr)) =
    20%:R * (SN.sparse_eval_ring values S.sp ^+ 2 *
      SN.sparse_eval_ring values S.sr).
Proof.
rewrite [LHS]S.sparse_canonical_scale_nat_eval.
by rewrite eval_sp_square_sr_mul_atom.
Qed.

Lemma eval_sp32_p_q_square_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale 2%:Z
        (S.sparse_canonical_mul S.sp
          (S.sparse_canonical_pow S.sq 2))) =
    2%:R * (SN.sparse_eval_ring values S.sp *
      SN.sparse_eval_ring values S.sq ^+ 2).
Proof.
rewrite [LHS]S.sparse_canonical_scale_nat_eval.
by rewrite eval_sp_sq_square_mul_atom.
Qed.

Lemma eval_sp32_q_s_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale (- 35%:Z)
        (S.sparse_canonical_mul S.sq S.ss)) =
    - (35%:R * (SN.sparse_eval_ring values S.sq *
      SN.sparse_eval_ring values S.ss)).
Proof.
rewrite [LHS]S.sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sq_ss_mul_atom.
Qed.

Lemma eval_sp32_r_square_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale (- 40%:Z)
        (S.sparse_canonical_pow S.sr 2)) =
    - (40%:R * SN.sparse_eval_ring values S.sr ^+ 2).
Proof.
rewrite [LHS]S.sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sr_square_atom.
Qed.

(** The eight closed P33 summands. *)
Lemma eval_sp33_i8_term :
  SN.sparse_eval_ring values (S.sparse_canonical_scale 35%:Z S.si8) =
    35%:R * SN.sparse_eval_ring values S.si8.
Proof. by rewrite [LHS]S.sparse_canonical_scale_nat_eval. Qed.

Lemma eval_sp33_p_i6_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale (- 4%:Z)
        (S.sparse_canonical_mul S.sp S.si6)) =
    - (4%:R * (SN.sparse_eval_ring values S.sp *
      SN.sparse_eval_ring values S.si6)).
Proof.
rewrite [LHS]S.sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sp_si6_mul_atom.
Qed.

Lemma eval_sp33_q_i5_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale 23%:Z
        (S.sparse_canonical_mul S.sq S.si5)) =
    23%:R * (SN.sparse_eval_ring values S.sq *
      SN.sparse_eval_ring values S.si5).
Proof.
rewrite [LHS]S.sparse_canonical_scale_nat_eval.
by rewrite eval_sq_si5_mul_atom.
Qed.

Lemma eval_sp33_i4_left_atom :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale (- 6%:Z)
        (S.sparse_canonical_pow S.sp 2)) =
    - (6%:R * SN.sparse_eval_ring values S.sp ^+ 2).
Proof.
rewrite [LHS]S.sparse_canonical_scale_neg_nat_eval.
by rewrite S.sparse_canonical_pow_eval.
Qed.

Lemma eval_sp33_i4_right_atom :
  SN.sparse_eval_ring values (S.sparse_canonical_scale 12%:Z S.sr) =
    12%:R * SN.sparse_eval_ring values S.sr.
Proof. by rewrite [LHS]S.sparse_canonical_scale_nat_eval. Qed.

Lemma eval_sp33_i4_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_mul
        (S.sparse_canonical_add
          (S.sparse_canonical_scale (- 6%:Z)
            (S.sparse_canonical_pow S.sp 2))
          (S.sparse_canonical_scale 12%:Z S.sr)) S.si4) =
    (- (6%:R * SN.sparse_eval_ring values S.sp ^+ 2) +
      12%:R * SN.sparse_eval_ring values S.sr) *
      SN.sparse_eval_ring values S.si4.
Proof.
rewrite [LHS]S.sparse_canonical_mul_eval
  S.sparse_canonical_add_eval
  eval_sp33_i4_left_atom eval_sp33_i4_right_atom.
reflexivity.
Qed.

Lemma eval_sp33_p_square_r_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale (- 58%:Z)
        (S.sparse_canonical_mul
          (S.sparse_canonical_pow S.sp 2) S.sr)) =
    - (58%:R * (SN.sparse_eval_ring values S.sp ^+ 2 *
      SN.sparse_eval_ring values S.sr)).
Proof.
rewrite [LHS]S.sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sp_square_sr_mul_atom.
Qed.

Lemma eval_sp33_p_q_square_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale 14%:Z
        (S.sparse_canonical_mul S.sp
          (S.sparse_canonical_pow S.sq 2))) =
    14%:R * (SN.sparse_eval_ring values S.sp *
      SN.sparse_eval_ring values S.sq ^+ 2).
Proof.
rewrite [LHS]S.sparse_canonical_scale_nat_eval.
by rewrite eval_sp_sq_square_mul_atom.
Qed.

Lemma eval_sp33_q_s_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale (- 105%:Z)
        (S.sparse_canonical_mul S.sq S.ss)) =
    - (105%:R * (SN.sparse_eval_ring values S.sq *
      SN.sparse_eval_ring values S.ss)).
Proof.
rewrite [LHS]S.sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sq_ss_mul_atom.
Qed.

Lemma eval_sp33_r_square_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale 76%:Z
        (S.sparse_canonical_pow S.sr 2)) =
    76%:R * SN.sparse_eval_ring values S.sr ^+ 2.
Proof.
rewrite [LHS]S.sparse_canonical_scale_nat_eval.
by rewrite eval_sr_square_atom.
Qed.

(** The eight closed P34 summands. *)
Lemma eval_sp34_i8_term :
  SN.sparse_eval_ring values (S.sparse_canonical_scale 5%:Z S.si8) =
    5%:R * SN.sparse_eval_ring values S.si8.
Proof. by rewrite [LHS]S.sparse_canonical_scale_nat_eval. Qed.

Lemma eval_sp34_p_i6_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale (- 22%:Z)
        (S.sparse_canonical_mul S.sp S.si6)) =
    - (22%:R * (SN.sparse_eval_ring values S.sp *
      SN.sparse_eval_ring values S.si6)).
Proof.
rewrite [LHS]S.sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sp_si6_mul_atom.
Qed.

Lemma eval_sp34_q_i5_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale 14%:Z
        (S.sparse_canonical_mul S.sq S.si5)) =
    14%:R * (SN.sparse_eval_ring values S.sq *
      SN.sparse_eval_ring values S.si5).
Proof.
rewrite [LHS]S.sparse_canonical_scale_nat_eval.
by rewrite eval_sq_si5_mul_atom.
Qed.

Lemma eval_sp34_i4_left_atom :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale (- 18%:Z)
        (S.sparse_canonical_pow S.sp 2)) =
    - (18%:R * SN.sparse_eval_ring values S.sp ^+ 2).
Proof.
rewrite [LHS]S.sparse_canonical_scale_neg_nat_eval.
by rewrite S.sparse_canonical_pow_eval.
Qed.

Lemma eval_sp34_i4_right_atom :
  SN.sparse_eval_ring values (S.sparse_canonical_scale 16%:Z S.sr) =
    16%:R * SN.sparse_eval_ring values S.sr.
Proof. by rewrite [LHS]S.sparse_canonical_scale_nat_eval. Qed.

Lemma eval_sp34_i4_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_mul
        (S.sparse_canonical_add
          (S.sparse_canonical_scale (- 18%:Z)
            (S.sparse_canonical_pow S.sp 2))
          (S.sparse_canonical_scale 16%:Z S.sr)) S.si4) =
    (- (18%:R * SN.sparse_eval_ring values S.sp ^+ 2) +
      16%:R * SN.sparse_eval_ring values S.sr) *
      SN.sparse_eval_ring values S.si4.
Proof.
rewrite [LHS]S.sparse_canonical_mul_eval
  S.sparse_canonical_add_eval
  eval_sp34_i4_left_atom eval_sp34_i4_right_atom.
reflexivity.
Qed.

Lemma eval_sp34_p_square_r_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale (- 34%:Z)
        (S.sparse_canonical_mul
          (S.sparse_canonical_pow S.sp 2) S.sr)) =
    - (34%:R * (SN.sparse_eval_ring values S.sp ^+ 2 *
      SN.sparse_eval_ring values S.sr)).
Proof.
rewrite [LHS]S.sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sp_square_sr_mul_atom.
Qed.

Lemma eval_sp34_p_q_square_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale 22%:Z
        (S.sparse_canonical_mul S.sp
          (S.sparse_canonical_pow S.sq 2))) =
    22%:R * (SN.sparse_eval_ring values S.sp *
      SN.sparse_eval_ring values S.sq ^+ 2).
Proof.
rewrite [LHS]S.sparse_canonical_scale_nat_eval.
by rewrite eval_sp_sq_square_mul_atom.
Qed.

Lemma eval_sp34_q_s_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale (- 140%:Z)
        (S.sparse_canonical_mul S.sq S.ss)) =
    - (140%:R * (SN.sparse_eval_ring values S.sq *
      SN.sparse_eval_ring values S.ss)).
Proof.
rewrite [LHS]S.sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sq_ss_mul_atom.
Qed.

Lemma eval_sp34_r_square_term :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale 68%:Z
        (S.sparse_canonical_pow S.sr 2)) =
    68%:R * SN.sparse_eval_ring values S.sr ^+ 2.
Proof.
rewrite [LHS]S.sparse_canonical_scale_nat_eval.
by rewrite eval_sr_square_atom.
Qed.

(** Fold-right structures of the three eight-summand coefficients. *)
Lemma eval_sp32_structure :
  SN.sparse_eval_ring values sp32 =
    25%:R *
      (- (10%:R * SN.sparse_eval_ring values S.si8) +
      (2%:R * (SN.sparse_eval_ring values S.sp *
          SN.sparse_eval_ring values S.si6) +
      (- (22%:R * (SN.sparse_eval_ring values S.sq *
          SN.sparse_eval_ring values S.si5)) +
      (2%:R * (SN.sparse_eval_ring values S.sp ^+ 2 *
          SN.sparse_eval_ring values S.si4) +
      (20%:R * (SN.sparse_eval_ring values S.sp ^+ 2 *
          SN.sparse_eval_ring values S.sr) +
      (2%:R * (SN.sparse_eval_ring values S.sp *
          SN.sparse_eval_ring values S.sq ^+ 2) +
      (- (35%:R * (SN.sparse_eval_ring values S.sq *
          SN.sparse_eval_ring values S.ss)) +
      - (40%:R * SN.sparse_eval_ring values S.sr ^+ 2)))))))).
Proof.
rewrite /sp32 [LHS]S.sparse_canonical_scale_nat_eval.
congr (_ * _).
rewrite S.eval_ssum !big_cons !big_nil.
rewrite eval_sp32_i8_term eval_sp32_p_i6_term eval_sp32_q_i5_term
  eval_sp32_p_square_i4_term eval_sp32_p_square_r_term
  eval_sp32_p_q_square_term eval_sp32_q_s_term eval_sp32_r_square_term.
by rewrite addr0.
Qed.

Lemma eval_sp33_structure :
  SN.sparse_eval_ring values sp33 =
    5%:R *
      (35%:R * SN.sparse_eval_ring values S.si8 +
      (- (4%:R * (SN.sparse_eval_ring values S.sp *
          SN.sparse_eval_ring values S.si6)) +
      (23%:R * (SN.sparse_eval_ring values S.sq *
          SN.sparse_eval_ring values S.si5) +
      ((- (6%:R * SN.sparse_eval_ring values S.sp ^+ 2) +
          12%:R * SN.sparse_eval_ring values S.sr) *
          SN.sparse_eval_ring values S.si4 +
      (- (58%:R * (SN.sparse_eval_ring values S.sp ^+ 2 *
          SN.sparse_eval_ring values S.sr)) +
      (14%:R * (SN.sparse_eval_ring values S.sp *
          SN.sparse_eval_ring values S.sq ^+ 2) +
      (- (105%:R * (SN.sparse_eval_ring values S.sq *
          SN.sparse_eval_ring values S.ss)) +
      76%:R * SN.sparse_eval_ring values S.sr ^+ 2))))))).
Proof.
rewrite /sp33 [LHS]S.sparse_canonical_scale_nat_eval.
congr (_ * _).
rewrite S.eval_ssum !big_cons !big_nil.
rewrite eval_sp33_i8_term eval_sp33_p_i6_term eval_sp33_q_i5_term
  eval_sp33_i4_term eval_sp33_p_square_r_term
  eval_sp33_p_q_square_term eval_sp33_q_s_term eval_sp33_r_square_term.
by rewrite addr0.
Qed.

Lemma eval_sp34_structure :
  SN.sparse_eval_ring values sp34 =
    5%:R *
      (5%:R * SN.sparse_eval_ring values S.si8 +
      (- (22%:R * (SN.sparse_eval_ring values S.sp *
          SN.sparse_eval_ring values S.si6)) +
      (14%:R * (SN.sparse_eval_ring values S.sq *
          SN.sparse_eval_ring values S.si5) +
      ((- (18%:R * SN.sparse_eval_ring values S.sp ^+ 2) +
          16%:R * SN.sparse_eval_ring values S.sr) *
          SN.sparse_eval_ring values S.si4 +
      (- (34%:R * (SN.sparse_eval_ring values S.sp ^+ 2 *
          SN.sparse_eval_ring values S.sr)) +
      (22%:R * (SN.sparse_eval_ring values S.sp *
          SN.sparse_eval_ring values S.sq ^+ 2) +
      (- (140%:R * (SN.sparse_eval_ring values S.sq *
          SN.sparse_eval_ring values S.ss)) +
      68%:R * SN.sparse_eval_ring values S.sr ^+ 2))))))).
Proof.
rewrite /sp34 [LHS]S.sparse_canonical_scale_nat_eval.
congr (_ * _).
rewrite S.eval_ssum !big_cons !big_nil.
rewrite eval_sp34_i8_term eval_sp34_p_i6_term eval_sp34_q_i5_term
  eval_sp34_i4_term eval_sp34_p_square_r_term
  eval_sp34_p_q_square_term eval_sp34_q_s_term eval_sp34_r_square_term.
by rewrite addr0.
Qed.

(** Bridges from closed sparse structures to the public P3 coefficients. *)
Lemma eval_p31_from_atoms
    (c : LazardDepressedRootCoefficients F)
    (hq : SN.sparse_eval_ring values S.sq = lazard_root_q c) :
  SN.sparse_eval_ring values sp31 = lazard_p31 c.
Proof.
rewrite eval_sp31_structure hq /lazard_p31.
by rewrite mulNr.
Qed.

Lemma eval_p32_from_atoms
    (c : LazardDepressedRootCoefficients F) (i : LazardRootInvariants F)
    (hp : SN.sparse_eval_ring values S.sp = lazard_root_p c)
    (hq : SN.sparse_eval_ring values S.sq = lazard_root_q c)
    (hr : SN.sparse_eval_ring values S.sr = lazard_root_r c)
    (hs : SN.sparse_eval_ring values S.ss = lazard_root_s c)
    (hi4 : SN.sparse_eval_ring values S.si4 = lazard_root_i4 i)
    (hi5 : SN.sparse_eval_ring values S.si5 = lazard_root_i5 i)
    (hi6 : SN.sparse_eval_ring values S.si6 = lazard_root_i6 i)
    (hi8 : SN.sparse_eval_ring values S.si8 = lazard_root_i8 i) :
  SN.sparse_eval_ring values sp32 = lazard_p32 c i.
Proof.
rewrite eval_sp32_structure hp hq hr hs hi4 hi5 hi6 hi8 /lazard_p32.
by rewrite !mulNr !mulrA add8_right_assoc.
Qed.

Lemma eval_p33_from_atoms
    (c : LazardDepressedRootCoefficients F) (i : LazardRootInvariants F)
    (hp : SN.sparse_eval_ring values S.sp = lazard_root_p c)
    (hq : SN.sparse_eval_ring values S.sq = lazard_root_q c)
    (hr : SN.sparse_eval_ring values S.sr = lazard_root_r c)
    (hs : SN.sparse_eval_ring values S.ss = lazard_root_s c)
    (hi4 : SN.sparse_eval_ring values S.si4 = lazard_root_i4 i)
    (hi5 : SN.sparse_eval_ring values S.si5 = lazard_root_i5 i)
    (hi6 : SN.sparse_eval_ring values S.si6 = lazard_root_i6 i)
    (hi8 : SN.sparse_eval_ring values S.si8 = lazard_root_i8 i) :
  SN.sparse_eval_ring values sp33 = lazard_p33 c i.
Proof.
rewrite eval_sp33_structure hp hq hr hs hi4 hi5 hi6 hi8 /lazard_p33.
by rewrite !mulNr !mulrA add8_right_assoc.
Qed.

Lemma eval_p34_from_atoms
    (c : LazardDepressedRootCoefficients F) (i : LazardRootInvariants F)
    (hp : SN.sparse_eval_ring values S.sp = lazard_root_p c)
    (hq : SN.sparse_eval_ring values S.sq = lazard_root_q c)
    (hr : SN.sparse_eval_ring values S.sr = lazard_root_r c)
    (hs : SN.sparse_eval_ring values S.ss = lazard_root_s c)
    (hi4 : SN.sparse_eval_ring values S.si4 = lazard_root_i4 i)
    (hi5 : SN.sparse_eval_ring values S.si5 = lazard_root_i5 i)
    (hi6 : SN.sparse_eval_ring values S.si6 = lazard_root_i6 i)
    (hi8 : SN.sparse_eval_ring values S.si8 = lazard_root_i8 i) :
  SN.sparse_eval_ring values sp34 = lazard_p34 c i.
Proof.
rewrite eval_sp34_structure hp hq hr hs hi4 hi5 hi6 hi8 /lazard_p34.
by rewrite !mulNr !mulrA add8_right_assoc.
Qed.

Lemma eval_p31 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sp31 =
    lazard_p31 (lazard_depressed_of_roots roots).
Proof.
have [_ [hq _]] := S.eval_root_atoms hsum.
exact: eval_p31_from_atoms hq.
Qed.

Lemma eval_p32 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sp32 =
    lazard_p32 (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots).
Proof.
have [hp [hq [hr hs]]] := S.eval_root_atoms hsum.
have [hi4 [hi5 [hi6 [_ hi8]]]] := S.eval_invariant_atoms hsum.
exact: eval_p32_from_atoms hp hq hr hs hi4 hi5 hi6 hi8.
Qed.

Lemma eval_p33 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sp33 =
    lazard_p33 (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots).
Proof.
have [hp [hq [hr hs]]] := S.eval_root_atoms hsum.
have [hi4 [hi5 [hi6 [_ hi8]]]] := S.eval_invariant_atoms hsum.
exact: eval_p33_from_atoms hp hq hr hs hi4 hi5 hi6 hi8.
Qed.

Lemma eval_p34 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sp34 =
    lazard_p34 (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots).
Proof.
have [hp [hq [hr hs]]] := S.eval_root_atoms hsum.
have [hi4 [hi5 [hi6 [_ hi8]]]] := S.eval_invariant_atoms hsum.
exact: eval_p34_from_atoms hp hq hr hs hi4 hi5 hi6 hi8.
Qed.

Lemma eval_p3_atoms (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sp31 =
      lazard_p31 (lazard_depressed_of_roots roots) /\
  SN.sparse_eval_ring values sp32 =
      lazard_p32 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots) /\
  SN.sparse_eval_ring values sp33 =
      lazard_p33 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots) /\
  SN.sparse_eval_ring values sp34 =
      lazard_p34 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots).
Proof.
repeat split.
- exact: eval_p31 hsum.
- exact: eval_p32 hsum.
- exact: eval_p33 hsum.
- exact: eval_p34 hsum.
Qed.

Lemma eval_sparse_cyclic_fourier_P3
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic sparse_cyclic_fourier_P3 =
    lazard_cyclic_fourier_P3 roots.
Proof.
have hx0 := S.sx0_eval roots.
have hx1 := S.sx1_eval roots.
have hx2 := S.sx2_eval roots.
have hx3 := S.sx3_eval roots.
have hx4 := S.sx4_eval hsum.
by rewrite /sparse_cyclic_fourier_P3 /S.eval_sparse_cyclic
  /lazard_cyclic_fourier_P3 /= hx0 hx1 hx2 hx3 hx4.
Qed.

(** Closed scalar subtrees used by the numerator. *)
Lemma eval_sparse_p3_five_E (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values
      (S.sparse_canonical_mul
        (S.sparse_canonical_const 5) S.sroot_E) =
    5%:R * Q.lazard_root_E roots.
Proof.
have [_ [_ [_ hE]]] := S.eval_tu_epsilon_E hsum.
rewrite [LHS]S.sparse_canonical_mul_eval.
by rewrite S.sparse_canonical_const_eval hE.
Qed.

Lemma eval_sparse_p3_five_E_p31
    (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values
      (S.sparse_canonical_mul
        (S.sparse_canonical_mul
          (S.sparse_canonical_const 5) S.sroot_E) sp31) =
    5%:R * Q.lazard_root_E roots *
      lazard_p31 (lazard_depressed_of_roots roots).
Proof.
have hp31 := eval_p31 hsum.
rewrite [LHS]S.sparse_canonical_mul_eval.
by rewrite (eval_sparse_p3_five_E hsum) hp31.
Qed.

Lemma eval_sparse_p3_five_E_p32
    (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values
      (S.sparse_canonical_mul
        (S.sparse_canonical_mul
          (S.sparse_canonical_const 5) S.sroot_E) sp32) =
    5%:R * Q.lazard_root_E roots *
      lazard_p32 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots).
Proof.
have hp32 := eval_p32 hsum.
rewrite [LHS]S.sparse_canonical_mul_eval.
by rewrite (eval_sparse_p3_five_E hsum) hp32.
Qed.

Lemma eval_sparse_p3_two :
  SN.sparse_eval_ring values (S.sparse_canonical_const 2) = 2%:R.
Proof. exact: S.sparse_canonical_const_eval. Qed.

Lemma eval_sparse_p3_twenty_E
    (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values
      (S.sparse_canonical_scale 20%:Z S.sroot_E) =
    20%:R * Q.lazard_root_E roots.
Proof.
have [_ [_ [_ hE]]] := S.eval_tu_epsilon_E hsum.
rewrite [LHS]S.sparse_canonical_scale_nat_eval.
by rewrite hE.
Qed.

(** Closed semantic helpers for every local subtree of the P3 left side. *)
Lemma eval_sparse_p3_p31_epsilon_term
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic
      (S.sparse_cyclic_scale
        (S.sparse_canonical_mul
          (S.sparse_canonical_mul
            (S.sparse_canonical_const 5) S.sroot_E) sp31)
        S.sparse_cyclic_epsilon) =
    lazard_cyclic_scale
      (5%:R * Q.lazard_root_E roots *
        lazard_p31 (lazard_depressed_of_roots roots))
      (C.lazard_cyclic_root_epsilon roots).
Proof.
have [hepsilon _] := S.eval_sparse_structural_atoms hsum.
rewrite [LHS]S.eval_sparse_cyclic_scale.
by rewrite (eval_sparse_p3_five_E_p31 hsum) hepsilon.
Qed.

Lemma eval_sparse_p3_p32_constant_term
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic
      (S.sparse_cyclic_constant
        (S.sparse_canonical_mul
          (S.sparse_canonical_mul
            (S.sparse_canonical_const 5) S.sroot_E) sp32)) =
    C.lazard_cyclic_constant
      (5%:R * Q.lazard_root_E roots *
        lazard_p32 (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots)).
Proof.
rewrite [LHS]S.eval_sparse_cyclic_constant.
by rewrite (eval_sparse_p3_five_E_p32 hsum).
Qed.

Lemma eval_sparse_p3_p33_T_term
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic
      (S.sparse_cyclic_scale sp33 S.sparse_cyclic_T) =
    lazard_cyclic_scale
      (lazard_p33 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
      (C.lazard_cyclic_root_T roots).
Proof.
have [_ [hT _]] := S.eval_sparse_structural_atoms hsum.
have hp33 := eval_p33 hsum.
rewrite [LHS]S.eval_sparse_cyclic_scale.
by rewrite hp33 hT.
Qed.

Lemma eval_sparse_p3_p34_U_term
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic
      (S.sparse_cyclic_scale sp34 S.sparse_cyclic_formula_U) =
    lazard_cyclic_scale
      (lazard_p34 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
      (C.lazard_cyclic_root_formula_U roots).
Proof.
have [_ [_ [hU _]]] := S.eval_sparse_structural_atoms hsum.
have hp34 := eval_p34 hsum.
rewrite [LHS]S.eval_sparse_cyclic_scale.
by rewrite hp34 hU.
Qed.

Lemma eval_sparse_p3_p33_T_add_p34_U
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic
      (S.sparse_cyclic_add
        (S.sparse_cyclic_scale sp33 S.sparse_cyclic_T)
        (S.sparse_cyclic_scale sp34 S.sparse_cyclic_formula_U)) =
    lazard_cyclic_add
      (lazard_cyclic_scale
        (lazard_p33 (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots))
        (C.lazard_cyclic_root_T roots))
      (lazard_cyclic_scale
        (lazard_p34 (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots))
        (C.lazard_cyclic_root_formula_U roots)).
Proof.
rewrite [LHS]S.eval_sparse_cyclic_add.
by rewrite (eval_sparse_p3_p33_T_term hsum)
  (eval_sparse_p3_p34_U_term hsum).
Qed.

Lemma eval_sparse_p3_epsilon_times_TU
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic
      (S.sparse_cyclic_mul S.sparse_cyclic_epsilon
        (S.sparse_cyclic_add
          (S.sparse_cyclic_scale sp33 S.sparse_cyclic_T)
          (S.sparse_cyclic_scale sp34 S.sparse_cyclic_formula_U))) =
    lazard_cyclic_mul
      (C.lazard_cyclic_root_epsilon roots)
      (lazard_cyclic_add
        (lazard_cyclic_scale
          (lazard_p33 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots))
          (C.lazard_cyclic_root_T roots))
        (lazard_cyclic_scale
          (lazard_p34 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots))
          (C.lazard_cyclic_root_formula_U roots))).
Proof.
have [hepsilon _] := S.eval_sparse_structural_atoms hsum.
rewrite [LHS]S.eval_sparse_cyclic_mul.
by rewrite hepsilon (eval_sparse_p3_p33_T_add_p34_U hsum).
Qed.

Lemma eval_sparse_p3_twice_epsilon_TU
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic
      (S.sparse_cyclic_scale (S.sparse_canonical_const 2)
        (S.sparse_cyclic_mul S.sparse_cyclic_epsilon
          (S.sparse_cyclic_add
            (S.sparse_cyclic_scale sp33 S.sparse_cyclic_T)
            (S.sparse_cyclic_scale sp34 S.sparse_cyclic_formula_U)))) =
    lazard_cyclic_scale 2%:R
      (lazard_cyclic_mul
        (C.lazard_cyclic_root_epsilon roots)
        (lazard_cyclic_add
          (lazard_cyclic_scale
            (lazard_p33 (lazard_depressed_of_roots roots)
              (lazard_root_invariants roots))
            (C.lazard_cyclic_root_T roots))
          (lazard_cyclic_scale
            (lazard_p34 (lazard_depressed_of_roots roots)
              (lazard_root_invariants roots))
            (C.lazard_cyclic_root_formula_U roots)))).
Proof.
rewrite [LHS]S.eval_sparse_cyclic_scale.
by rewrite eval_sparse_p3_two (eval_sparse_p3_epsilon_times_TU hsum).
Qed.

Lemma eval_sparse_p3_constant_add_twice
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic
      (S.sparse_cyclic_add
        (S.sparse_cyclic_constant
          (S.sparse_canonical_mul
            (S.sparse_canonical_mul
              (S.sparse_canonical_const 5) S.sroot_E) sp32))
        (S.sparse_cyclic_scale (S.sparse_canonical_const 2)
          (S.sparse_cyclic_mul S.sparse_cyclic_epsilon
            (S.sparse_cyclic_add
              (S.sparse_cyclic_scale sp33 S.sparse_cyclic_T)
              (S.sparse_cyclic_scale sp34 S.sparse_cyclic_formula_U))))) =
    lazard_cyclic_add
      (C.lazard_cyclic_constant
        (5%:R * Q.lazard_root_E roots *
          lazard_p32 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots)))
      (lazard_cyclic_scale 2%:R
        (lazard_cyclic_mul
          (C.lazard_cyclic_root_epsilon roots)
          (lazard_cyclic_add
            (lazard_cyclic_scale
              (lazard_p33 (lazard_depressed_of_roots roots)
                (lazard_root_invariants roots))
              (C.lazard_cyclic_root_T roots))
            (lazard_cyclic_scale
              (lazard_p34 (lazard_depressed_of_roots roots)
                (lazard_root_invariants roots))
              (C.lazard_cyclic_root_formula_U roots))))).
Proof.
rewrite [LHS]S.eval_sparse_cyclic_add.
by rewrite (eval_sparse_p3_p32_constant_term hsum)
  (eval_sparse_p3_twice_epsilon_TU hsum).
Qed.

Lemma eval_sparse_p3_numerator_left
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic sparse_p3_numerator_left =
    P3C.lazard_cyclic_p3_numerator_left roots.
Proof.
rewrite /sparse_p3_numerator_left
  /P3C.lazard_cyclic_p3_numerator_left.
rewrite [LHS]S.eval_sparse_cyclic_add.
by rewrite (eval_sparse_p3_p31_epsilon_term hsum)
  (eval_sparse_p3_constant_add_twice hsum).
Qed.

(** Closed semantic helpers for every local subtree of the P3 right side. *)
Lemma eval_sparse_p3_P1_square
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic
      (S.sparse_cyclic_mul S.sparse_cyclic_fourier_P1
        S.sparse_cyclic_fourier_P1) =
    lazard_cyclic_mul (lazard_cyclic_fourier_P1 roots)
      (lazard_cyclic_fourier_P1 roots).
Proof.
have [_ [_ [_ [hP1 _]]]] := S.eval_sparse_structural_atoms hsum.
rewrite [LHS]S.eval_sparse_cyclic_mul.
by rewrite hP1.
Qed.

Lemma eval_sparse_p3_P1_square_times_P3
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic
      (S.sparse_cyclic_mul
        (S.sparse_cyclic_mul S.sparse_cyclic_fourier_P1
          S.sparse_cyclic_fourier_P1)
        sparse_cyclic_fourier_P3) =
    lazard_cyclic_mul
      (lazard_cyclic_mul (lazard_cyclic_fourier_P1 roots)
        (lazard_cyclic_fourier_P1 roots))
      (lazard_cyclic_fourier_P3 roots).
Proof.
have hP3 := eval_sparse_cyclic_fourier_P3 hsum.
rewrite [LHS]S.eval_sparse_cyclic_mul.
by rewrite (eval_sparse_p3_P1_square hsum) hP3.
Qed.

Lemma eval_sparse_p3_epsilon_times_fourier
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic
      (S.sparse_cyclic_mul S.sparse_cyclic_epsilon
        (S.sparse_cyclic_mul
          (S.sparse_cyclic_mul S.sparse_cyclic_fourier_P1
            S.sparse_cyclic_fourier_P1)
          sparse_cyclic_fourier_P3)) =
    lazard_cyclic_mul
      (C.lazard_cyclic_root_epsilon roots)
      (lazard_cyclic_mul
        (lazard_cyclic_mul (lazard_cyclic_fourier_P1 roots)
          (lazard_cyclic_fourier_P1 roots))
        (lazard_cyclic_fourier_P3 roots)).
Proof.
have [hepsilon _] := S.eval_sparse_structural_atoms hsum.
rewrite [LHS]S.eval_sparse_cyclic_mul.
by rewrite hepsilon (eval_sparse_p3_P1_square_times_P3 hsum).
Qed.

Lemma eval_sparse_p3_numerator_right
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic sparse_p3_numerator_right =
    P3C.lazard_cyclic_p3_numerator_right roots.
Proof.
rewrite /sparse_p3_numerator_right
  /P3C.lazard_cyclic_p3_numerator_right.
rewrite [LHS]S.eval_sparse_cyclic_scale.
by rewrite (eval_sparse_p3_twenty_E hsum)
  (eval_sparse_p3_epsilon_times_fourier hsum).
Qed.

(** Public semantic interface consumed by the generated coefficient
    certificate aggregate. *)
Theorem eval_sparse_p3_numerator_difference
    (hsum : lazard_root_esymm1 roots = 0) :
  S.eval_sparse_cyclic sparse_p3_numerator_difference =
    P3C.lazard_cyclic_p3_numerator_difference roots.
Proof.
rewrite /sparse_p3_numerator_difference
  /P3C.lazard_cyclic_p3_numerator_difference.
rewrite [LHS]S.eval_sparse_cyclic_sub.
by rewrite (eval_sparse_p3_numerator_left hsum)
  (eval_sparse_p3_numerator_right hsum).
Qed.

(** Restore computational transparency for the generated [vm_compute]
    normalization leaves. *)
Transparent S.sp S.sq S.sr S.ss S.si4 S.si5 S.si6 S.si7 S.si8.

End SemanticBridge.

End PolynomialFormulasLazardQuinticRootFourierNumeratorP3Sparse.
