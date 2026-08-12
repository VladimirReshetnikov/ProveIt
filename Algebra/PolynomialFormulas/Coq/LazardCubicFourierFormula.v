From PolynomialFormulas Require Import CubicField.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Lazard's literal Section 4.2 cubic display.

    If [u] is a cube root of the first Cardano radicand, Lazard writes
    [s1 = 3 u] and displays the roots of [X^3 + p X + q] as

      [s1 / 3 - p / s1],
      [omega^2 s1 / 3 - omega p / s1],
      [omega s1 / 3 - omega^2 p / s1].

    The second Cardano radical [-p/(3u)], its compatibility equation, and its
    cube equation are derived below from the square radical and the first
    cube radical.  The exact factorization and exhaustive root statement then
    reuse [CubicField].  The paper's order is Cardano order [0,2,1].

    The hypotheses [2 != 0] and [3 != 0] are explicit: the paper's global
    exclusions of characteristics two and five do not justify this display
    in characteristic three. *)
Module PolynomialFormulasLazardCubicFourierFormula.

Import GRing.Theory.
Local Open Scope ring_scope.

Module CF := PolynomialFormulasCubicField.

Section LazardCubicFourierFormula.

Variable F : fieldType.

Definition lazard_cubic_s1 (u : F) : F := 3%:R * u.

Definition lazard_cubic_second (p u : F) : F :=
  CF.cardano_derived_second p u.

Definition lazard_cubic_root0 (p u : F) : F :=
  lazard_cubic_s1 u / 3%:R - p / lazard_cubic_s1 u.

Definition lazard_cubic_root1 (p u omega : F) : F :=
  omega ^+ 2 * lazard_cubic_s1 u / 3%:R -
    omega * p / lazard_cubic_s1 u.

Definition lazard_cubic_root2 (p u omega : F) : F :=
  omega * lazard_cubic_s1 u / 3%:R -
    omega ^+ 2 * p / lazard_cubic_s1 u.

Lemma lazard_cubic_s1_neq0 u
    (three_neq0 : (3%:R : F) != 0) (u_neq0 : u != 0) :
  lazard_cubic_s1 u != 0.
Proof.
rewrite /lazard_cubic_s1.
exact: mulf_neq0 three_neq0 u_neq0.
Qed.

Lemma lazard_cubic_s1_div_three u
    (three_neq0 : (3%:R : F) != 0) :
  lazard_cubic_s1 u / 3%:R = u.
Proof.
rewrite /lazard_cubic_s1 [3%:R * u]mulrC.
exact: mulfK three_neq0 u.
Qed.

Lemma lazard_cubic_scaled_s1_div_three a u
    (three_neq0 : (3%:R : F) != 0) :
  a * lazard_cubic_s1 u / 3%:R = a * u.
Proof.
apply: (mulfI three_neq0).
rewrite [3%:R * (_ / 3%:R)]mulrC divfK //.
rewrite /lazard_cubic_s1 !mulrA.
by rewrite [a * 3%:R]mulrC.
Qed.

Lemma lazard_cubic_scaled_second a p u :
  - (a * p / lazard_cubic_s1 u) =
    a * lazard_cubic_second p u.
Proof.
rewrite /lazard_cubic_second /CF.cardano_derived_second mulNr mulrN.
by rewrite mulrA.
Qed.

(** The quotient appearing in Lazard's display has Cardano's required
    product; no additional compatibility certificate is needed. *)
Lemma lazard_cubic_second_compatible p u
    (three_neq0 : (3%:R : F) != 0) (u_neq0 : u != 0) :
  u * lazard_cubic_second p u = - p / 3%:R.
Proof.
have hden : lazard_cubic_s1 u != 0 :=
  lazard_cubic_s1_neq0 three_neq0 u_neq0.
apply: (mulfI three_neq0).
rewrite /lazard_cubic_second /CF.cardano_derived_second.
rewrite mulrA -/lazard_cubic_s1.
rewrite [lazard_cubic_s1 u * _]mulrC divfK //.
by rewrite [3%:R * (- p / 3%:R)]mulrC divfK.
Qed.

Lemma lazard_cubic_cube_neg (x : F) :
  (- x) ^+ 3 = - (x ^+ 3).
Proof.
by rewrite !CF.cubic_expr3 mulrNN mulrN.
Qed.

(** The quotient [-p/(3u)] is automatically a cube root of the opposite
    Cardano radicand. *)
Lemma lazard_cubic_second_cubed p q s u
    (three_neq0 : (3%:R : F) != 0)
    (hs : s ^+ 2 = CF.cardano_delta p q)
    (hu : u ^+ 3 = CF.cardano_first_radicand q s)
    (u_neq0 : u != 0) :
  lazard_cubic_second p u ^+ 3 =
    CF.cardano_second_radicand q s.
Proof.
have hfirst : CF.cardano_first_radicand q s != 0.
  rewrite -hu.
  exact: expf_neq0 3 u_neq0.
have hcompat := lazard_cubic_second_compatible
  p (u := u) three_neq0 u_neq0.
have hproduct := CF.cardano_radicands_product
  (p := p) (q := q) (s := s) hs.
apply: (mulfI hfirst).
transitivity (- (p / 3%:R) ^+ 3).
- rewrite -hu -exprMn hcompat.
  by rewrite mulNr lazard_cubic_cube_neg.
- exact: esym hproduct.
Qed.

(** If [p] is nonzero, the radicand-product identity makes the first raw
    radicand nonzero before any cube root is supplied. *)
Lemma lazard_cubic_first_radicand_neq0_of_p_neq0 (p q s : F)
    (three_neq0 : (3%:R : F) != 0)
    (p_neq0 : p != 0)
    (hs : s ^+ 2 = CF.cardano_delta p q) :
  CF.cardano_first_radicand q s != 0.
Proof.
apply/negP=> /eqP hfirst0.
have hproduct := CF.cardano_radicands_product
  (p := p) (q := q) (s := s) hs.
rewrite hfirst0 mul0r in hproduct.
have hnegcube0 : - (p / 3%:R) ^+ 3 = 0 := esym hproduct.
have hpdivcube0 : (p / 3%:R) ^+ 3 = 0.
  apply: oppr_inj.
  by rewrite oppr0 hnegcube0.
have hpdivcube0b : (p / 3%:R) ^+ 3 == 0.
  apply/eqP.
  exact: hpdivcube0.
have hpdiv0b : p / 3%:R == 0.
  move: hpdivcube0b.
  by rewrite expf_eq0.
have hpdiv0 : p / 3%:R = 0 := eqP hpdiv0b.
have hp0 : p = 0.
  have hscaled := congr1 (fun z : F => 3%:R * z) hpdiv0.
  move: hscaled.
  by rewrite mulr0 [3%:R * (p / 3%:R)]mulrC divfK.
by move: p_neq0; rewrite hp0 eqxx.
Qed.

(** Consequently every cube root of that first radicand is automatically
    nonzero.  Thus the denominator condition is derived rather than supplied
    in the ordinary branch. *)
Lemma lazard_cubic_first_cube_root_neq0_of_p_neq0 (p q s u : F)
    (three_neq0 : (3%:R : F) != 0)
    (p_neq0 : p != 0)
    (hs : s ^+ 2 = CF.cardano_delta p q)
    (hu : u ^+ 3 = CF.cardano_first_radicand q s) :
  u != 0.
Proof.
have hfirst := lazard_cubic_first_radicand_neq0_of_p_neq0
  three_neq0 p_neq0 hs.
apply/negP=> /eqP hu0.
move: hfirst.
rewrite -hu hu0 CF.cubic_expr3 !mul0r eqxx.
by [].
Qed.

(** The first literal value is Cardano's untwisted value. *)
Lemma lazard_cubic_root0E p u
    (three_neq0 : (3%:R : F) != 0) :
  lazard_cubic_root0 p u =
    CF.cardano_root0 u (lazard_cubic_second p u).
Proof.
rewrite /lazard_cubic_root0 /CF.cardano_root0.
rewrite lazard_cubic_s1_div_three //.
by rewrite /lazard_cubic_second /CF.cardano_derived_second mulNr.
Qed.

(** The paper's second value is Cardano branch [2]. *)
Lemma lazard_cubic_root1E p u omega
    (three_neq0 : (3%:R : F) != 0) :
  lazard_cubic_root1 p u omega =
    CF.cardano_root2 u (lazard_cubic_second p u) omega.
Proof.
rewrite /lazard_cubic_root1 /CF.cardano_root2.
rewrite lazard_cubic_scaled_s1_div_three //.
by rewrite lazard_cubic_scaled_second.
Qed.

(** The paper's third value is Cardano branch [1]. *)
Lemma lazard_cubic_root2E p u omega
    (three_neq0 : (3%:R : F) != 0) :
  lazard_cubic_root2 p u omega =
    CF.cardano_root1 u (lazard_cubic_second p u) omega.
Proof.
rewrite /lazard_cubic_root2 /CF.cardano_root1.
rewrite lazard_cubic_scaled_s1_div_three //.
by rewrite lazard_cubic_scaled_second.
Qed.

(** Exact factorization through the three literal displayed values. *)
Theorem lazard_cubic_fourier_factorization p q s u omega y
    (two_neq0 : (2%:R : F) != 0)
    (three_neq0 : (3%:R : F) != 0)
    (homega : omega ^+ 2 + omega + 1 = 0)
    (hs : s ^+ 2 = CF.cardano_delta p q)
    (hu : u ^+ 3 = CF.cardano_first_radicand q s)
    (u_neq0 : u != 0) :
  CF.depressed_cubic_value p q y =
    (y - lazard_cubic_root0 p u) *
      (y - lazard_cubic_root1 p u omega) *
      (y - lazard_cubic_root2 p u omega).
Proof.
have hv := lazard_cubic_second_cubed three_neq0 hs hu u_neq0.
have huv := lazard_cubic_second_compatible
  p (u := u) three_neq0 u_neq0.
rewrite (CF.cardano_depressed_factorization
  (p := p) (q := q) (s := s) (u := u)
  (v := lazard_cubic_second p u) (omega := omega) y
  two_neq0 three_neq0 homega hs hu hv huv).
rewrite (lazard_cubic_root0E p u three_neq0).
rewrite (lazard_cubic_root1E p u omega three_neq0).
rewrite (lazard_cubic_root2E p u omega three_neq0).
exact: mulrAC _ _ _.
Qed.

(** All three literal displayed values are roots. *)
Theorem lazard_cubic_fourier_roots p q s u omega
    (two_neq0 : (2%:R : F) != 0)
    (three_neq0 : (3%:R : F) != 0)
    (homega : omega ^+ 2 + omega + 1 = 0)
    (hs : s ^+ 2 = CF.cardano_delta p q)
    (hu : u ^+ 3 = CF.cardano_first_radicand q s)
    (u_neq0 : u != 0) :
  CF.depressed_cubic_value p q (lazard_cubic_root0 p u) = 0 /\
  CF.depressed_cubic_value p q (lazard_cubic_root1 p u omega) = 0 /\
  CF.depressed_cubic_value p q (lazard_cubic_root2 p u omega) = 0.
Proof.
have hv := lazard_cubic_second_cubed three_neq0 hs hu u_neq0.
have huv := lazard_cubic_second_compatible
  p (u := u) three_neq0 u_neq0.
have hroots := CF.cardano_depressed_roots
  two_neq0 three_neq0 homega hs hu hv huv.
split.
- rewrite (lazard_cubic_root0E p u three_neq0).
  exact: hroots.1.
split.
- rewrite (lazard_cubic_root1E p u omega three_neq0).
  exact: hroots.2.2.
- rewrite (lazard_cubic_root2E p u omega three_neq0).
  exact: hroots.2.1.
Qed.

(** Every field-valued root is one of the three literal values. *)
Theorem lazard_cubic_fourier_exhaustive p q s u omega x
    (two_neq0 : (2%:R : F) != 0)
    (three_neq0 : (3%:R : F) != 0)
    (homega : omega ^+ 2 + omega + 1 = 0)
    (hs : s ^+ 2 = CF.cardano_delta p q)
    (hu : u ^+ 3 = CF.cardano_first_radicand q s)
    (u_neq0 : u != 0)
    (hx : CF.depressed_cubic_value p q x = 0) :
  x = lazard_cubic_root0 p u \/
  x = lazard_cubic_root1 p u omega \/
  x = lazard_cubic_root2 p u omega.
Proof.
have hv := lazard_cubic_second_cubed three_neq0 hs hu u_neq0.
have huv := lazard_cubic_second_compatible
  p (u := u) three_neq0 u_neq0.
have hcardano := CF.cardano_depressed_exhaustive
  two_neq0 three_neq0 homega hs hu hv huv hx.
move: hcardano=> [h0 | [h1 | h2]].
- left.
  rewrite (lazard_cubic_root0E p u three_neq0).
  exact: h0.
- right; right.
  rewrite (lazard_cubic_root2E p u omega three_neq0).
  exact: h1.
- right; left.
  rewrite (lazard_cubic_root1E p u omega three_neq0).
  exact: h2.
Qed.

(** Root iff for the exact three-value display. *)
Theorem lazard_cubic_fourier_eq_zero_iff p q s u omega x
    (two_neq0 : (2%:R : F) != 0)
    (three_neq0 : (3%:R : F) != 0)
    (homega : omega ^+ 2 + omega + 1 = 0)
    (hs : s ^+ 2 = CF.cardano_delta p q)
    (hu : u ^+ 3 = CF.cardano_first_radicand q s)
    (u_neq0 : u != 0) :
  CF.depressed_cubic_value p q x = 0 <->
    x = lazard_cubic_root0 p u \/
    x = lazard_cubic_root1 p u omega \/
    x = lazard_cubic_root2 p u omega.
Proof.
split.
- exact: lazard_cubic_fourier_exhaustive
    two_neq0 three_neq0 homega hs hu u_neq0.
- move=> [-> | [-> | ->]].
  + exact: (lazard_cubic_fourier_roots
      two_neq0 three_neq0 homega hs hu u_neq0).1.
  + exact: (lazard_cubic_fourier_roots
      two_neq0 three_neq0 homega hs hu u_neq0).2.1.
  + exact: (lazard_cubic_fourier_roots
      two_neq0 three_neq0 homega hs hu u_neq0).2.2.
Qed.

(** The paper's exceptional [p = 0] sign branch, ending in the literal
    displayed roots.  The returned [CardanoPZeroBranchCertificate] includes
    the selected sign, nonzero first radicand, nonzero [u], and nonzero
    displayed denominator [3u]. *)
Theorem lazard_cubic_irreducible_p_zero_literal_roots p q s u omega
    (two_neq0 : (2%:R : F) != 0)
    (three_neq0 : (3%:R : F) != 0)
    (homega : omega ^+ 2 + omega + 1 = 0)
    (hirr : irreducible_poly (CF.depressed_cubic_polynomial p q))
    (hp : p = 0)
    (hs : s ^+ 2 = CF.cardano_delta p q)
    (hu : u ^+ 3 =
      CF.cardano_first_radicand q (CF.cardano_selected_sqrt q s)) :
  CF.CardanoPZeroBranchCertificate p q s u /\
  lazard_cubic_s1 u != 0 /\
  CF.depressed_cubic_value p q (lazard_cubic_root0 p u) = 0 /\
  CF.depressed_cubic_value p q (lazard_cubic_root1 p u omega) = 0 /\
  CF.depressed_cubic_value p q (lazard_cubic_root2 p u omega) = 0 /\
  forall x : F, CF.depressed_cubic_value p q x = 0 <->
    x = lazard_cubic_root0 p u \/
    x = lazard_cubic_root1 p u omega \/
    x = lazard_cubic_root2 p u omega.
Proof.
have hcert := CF.cardano_irreducible_p_zero_branch
  two_neq0 three_neq0 hirr hp hs hu.
have hu0 := CF.pzero_s1_neq0 hcert.
have hs_selected := CF.pzero_selected_square hcert.
have hroots := lazard_cubic_fourier_roots
  two_neq0 three_neq0 homega hs_selected hu hu0.
have hiff (x : F) := (lazard_cubic_fourier_eq_zero_iff
  (p := p) (q := q) (s := CF.cardano_selected_sqrt q s)
  (u := u) (omega := omega) x
  two_neq0 three_neq0 homega hs_selected hu hu0).
split; first exact: hcert.
split.
- exact: lazard_cubic_s1_neq0 three_neq0 hu0.
split; first exact: hroots.1.
split; first exact: hroots.2.1.
split; first exact: hroots.2.2.
exact: hiff.
Qed.

(** Complete paper-facing branch selection for an irreducible depressed
    cubic.  In the ordinary [p != 0] case the original square-root sign is
    safe.  In the exceptional [p = 0] case [CubicField] selects the opposite
    sign exactly when needed.  No independent nonzero-denominator or
    compatible-second-radical certificate is accepted from the caller. *)
Theorem lazard_cubic_irreducible_literal_branch p q s omega
    (two_neq0 : (2%:R : F) != 0)
    (three_neq0 : (3%:R : F) != 0)
    (homega : omega ^+ 2 + omega + 1 = 0)
    (hirr : irreducible_poly (CF.depressed_cubic_polynomial p q))
    (hs : s ^+ 2 = CF.cardano_delta p q) :
  exists t : F,
    (t = s \/ t = - s) /\
    t ^+ 2 = CF.cardano_delta p q /\
    CF.cardano_first_radicand q t != 0 /\
    forall u : F,
      u ^+ 3 = CF.cardano_first_radicand q t ->
      lazard_cubic_s1 u != 0 /\
      (forall y : F,
        CF.depressed_cubic_value p q y =
          (y - lazard_cubic_root0 p u) *
            (y - lazard_cubic_root1 p u omega) *
              (y - lazard_cubic_root2 p u omega)) /\
      CF.depressed_cubic_value p q (lazard_cubic_root0 p u) = 0 /\
      CF.depressed_cubic_value p q (lazard_cubic_root1 p u omega) = 0 /\
      CF.depressed_cubic_value p q (lazard_cubic_root2 p u omega) = 0 /\
      (forall x : F, CF.depressed_cubic_value p q x = 0 <->
        x = lazard_cubic_root0 p u \/
        x = lazard_cubic_root1 p u omega \/
        x = lazard_cubic_root2 p u omega).
Proof.
case hp0 : (p == 0).
- have hp : p = 0 := eqP hp0.
  exists (CF.cardano_selected_sqrt q s).
  split; first exact: CF.cardano_selected_sqrt_is_sign.
  split.
  + rewrite CF.cardano_selected_sqrt_square.
    exact: hs.
  + split.
    * exact: (CF.cardano_selected_first_radicand_neq0
        (q := q) s two_neq0
        (CF.irreducible_depressed_p_zero_q_neq0 hirr hp)).
    * move=> u hu.
      have hliteral := lazard_cubic_irreducible_p_zero_literal_roots
        two_neq0 three_neq0 homega hirr hp hs hu.
      case: hliteral => hbranch [hden [hroot0 [hroot1 [hroot2 hiff]]]].
      have hu0 := CF.pzero_s1_neq0 hbranch.
      split; first exact: hden.
      split.
      { move=> y.
        exact: (lazard_cubic_fourier_factorization
          (p := p) (q := q) (s := CF.cardano_selected_sqrt q s)
          (u := u) (omega := omega) y
          two_neq0 three_neq0 homega
          (CF.pzero_selected_square hbranch) hu hu0). }
      { split; first exact: hroot0.
        split; first exact: hroot1.
        split; first exact: hroot2.
        exact: hiff. }
- have hp : p != 0 by rewrite hp0.
  exists s.
  split; first by left.
  split; first exact: hs.
  have hfirst := lazard_cubic_first_radicand_neq0_of_p_neq0
    three_neq0 hp hs.
  split; first exact: hfirst.
  move=> u hu.
  have hu0 := lazard_cubic_first_cube_root_neq0_of_p_neq0
    three_neq0 hp hs hu.
  have hden := lazard_cubic_s1_neq0 three_neq0 hu0.
  have hroots := lazard_cubic_fourier_roots
    two_neq0 three_neq0 homega hs hu hu0.
  have hiff (x : F) := (lazard_cubic_fourier_eq_zero_iff
    (p := p) (q := q) (s := s) (u := u) (omega := omega) x
    two_neq0 three_neq0 homega hs hu hu0).
  split; first exact: hden.
  split.
  + move=> y.
    exact: (lazard_cubic_fourier_factorization
      (p := p) (q := q) (s := s) (u := u) (omega := omega) y
      two_neq0 three_neq0 homega hs hu hu0).
  + split; first exact: hroots.1.
    split; first exact: hroots.2.1.
    split; first exact: hroots.2.2.
    exact: hiff.
Qed.

Print Assumptions lazard_cubic_fourier_factorization.
Print Assumptions lazard_cubic_fourier_roots.
Print Assumptions lazard_cubic_fourier_eq_zero_iff.
Print Assumptions lazard_cubic_irreducible_p_zero_literal_roots.
Print Assumptions lazard_cubic_first_radicand_neq0_of_p_neq0.
Print Assumptions lazard_cubic_irreducible_literal_branch.

End LazardCubicFourierFormula.

End PolynomialFormulasLazardCubicFourierFormula.
