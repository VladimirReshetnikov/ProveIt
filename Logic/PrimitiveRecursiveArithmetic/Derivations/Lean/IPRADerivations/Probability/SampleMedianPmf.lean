import IPRADerivations.Probability.SampleMedian
import IPRADerivations.Probability.JointLotus

/-!
# The trinomial count law and the exact odd-sample median mass

Packet: `probability/median_ipra_constructive_proofs`, Theorem `thm:sample-pmf`.

For two disjoint indicators `Y = [X < v]`, `Z = [X > v]` (`Y + Z ≤ 1`) on a finite law `w` over `M ≥ 1`
outcomes, put `A = ∑ w Y`, `B = ∑ w (1 − Y − Z)`, `C = ∑ w Z` and let `P_r`, `S^Y_r`, `S^Z_r` be the
product weight and the two sample counts on `M^r` outcome codes (`ProductPower`).

* `G2`: the closed form `G₂(r, i, k) = [i + k ≤ r] C(r, i) C(r − i, k) Aⁱ Cᵏ B^{r−i−k}`, i.e. the
  multinomial weight `r! / (i! k! (r − i − k)!) Aⁱ Cᵏ B^{r−i−k}`; on the edges it is the binomial form
  of `SampleMedian` (`G2_edge_i`, `G2_edge_k`), and it satisfies the trinomial Pascal recurrence
  `G₂(r+1, i+1, k+1) = B G₂(r, i+1, k+1) + A G₂(r, i, k+1) + C G₂(r, i+1, k)` with its three edge
  forms (`G2_succ_00`, `G2_succ_s0`, `G2_succ_0s`, `G2_succ_ss`);
* `F2_succ`: peeling the last observation splits `[S^Y + y = i][S^Z + z = k]` three ways
  (`eqb_split2`), so `F₂_{r+1}(i, k) = F₂_r(i, k) B + F₂_r(i−1, k) A + F₂_r(i, k−1) C`;
* `count_law2`: the trinomial count law `∑_{t<M^r} P_r(t) [S^Y_r(t) = i] [S^Z_r(t) = k] = G₂(r, i, k)`,
  by quantifier-free induction on the nested violation count
  `∑_{i<B} ∑_{k<B} [F₂_r(i, k) ≠ G₂(r, i, k)]` with `B = i + k + 1` (four cases on `i, k` zero/successor);
* `sample_pmf` (`thm:sample-pmf`): the joint LOTUS (`JointLotus.multi_lotus`) for the two counts and
  the median event `[S^Y ≤ ⌊N/2⌋] [S^Z ≤ ⌊N/2⌋]` gives
  `∑_{t<M^N} P_N(t) [S^Y ≤ ⌊N/2⌋] [S^Z ≤ ⌊N/2⌋] = ∑_{i≤N} ∑_{k≤N} [i ≤ ⌊N/2⌋] [k ≤ ⌊N/2⌋] G₂(N, i, k)`,
  the numerator of `Pr(M_N = v)` over the denominator `W^N` for `N = 2n + 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.SampleMedianPmf

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero' binom_self' pascal_at)
open LeanProofs.IPRA.Probability.SampleMedian (ind_le ind_gt G G_congr G_zero G_succ_zero G_succ_succ)
open LeanProofs.IPRA.Probability.ProductPower (TB SB Pr Sr TB_at SB_at pr_peel sr_peel peel_sum lin3 shift_mul'' shift_zero'
  shift_inst2' one_bound tb_zero)
open LeanProofs.IPRA.Probability.Expectation (inst2_mul')
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (eqb_succ_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `G₂(r, i, k) = [i + k ≤ r] C(r, i) C(r − i, k) aⁱ cᵏ b^{r−i−k}`. -/
abbrev G2 (a b c r i k : PTm n) : PTm n :=
  SampleMedian.ind (i + k) r * ((binom r i * binom (monus r i) k) * (pw a i * (pw c k * pw b (monus r (i + k)))))

theorem G2_edge_i (a b c r i : PTm n) : Γ ⊢[PRAAx] G2 a b c r i zero ≐ G a b r i := by
  have e0 : Γ ⊢[PRAAx] i + zero ≐ i := add_zero _
  refine (congrMul (congrMonus (.eqRefl _) (congrMonus e0 (.eqRefl _)))
    (congrMul (congrMul (.eqRefl _) (binom_zero' _)) (congrMul (.eqRefl _) (congrMul (pw_zero _)
      (congrAp2 powF (congrMonus (.eqRefl _) e0) (.eqRefl _)))))).eqTrans ?_
  ipra_ring

theorem G2_edge_k (a b c r k : PTm n) : Γ ⊢[PRAAx] G2 a b c r zero k ≐ G c b r k := by
  have e0 : Γ ⊢[PRAAx] zero + k ≐ k := zero_add _
  refine (congrMul (congrMonus (.eqRefl _) (congrMonus e0 (.eqRefl _)))
    (congrMul (congrMul (binom_zero' _) (Combinatorics.BinomialTheorem.congrBinom (monus_zero _) (.eqRefl _)))
      (congrMul (pw_zero _) (congrMul (.eqRefl _)
      (congrAp2 powF (congrMonus (.eqRefl _) e0) (.eqRefl _)))))).eqTrans ?_
  ipra_ring

/-- `x = y + d` gives `x ∸ y = d`. -/
alias monus_of_eq := Common.monus_of_eq

theorem G2_succ_00 (a b c r : PTm n) : Γ ⊢[PRAAx] G2 a b c (succ r) zero zero ≐ b * G2 a b c r zero zero :=
  (G2_edge_i a b c _ _).eqTrans ((G_succ_zero a b r).eqTrans (congrMul (.eqRefl _) (G2_edge_i a b c _ _).eqSymm))

theorem G2_succ_s0 (a b c r i : PTm n) :
    Γ ⊢[PRAAx] G2 a b c (succ r) (succ i) zero ≐ b * G2 a b c r (succ i) zero + a * G2 a b c r i zero :=
  (G2_edge_i a b c _ _).eqTrans ((G_succ_succ a b r i).eqTrans
    (congrAdd (congrMul (.eqRefl _) (G2_edge_i a b c _ _).eqSymm) (congrMul (.eqRefl _) (G2_edge_i a b c _ _).eqSymm)))

theorem G2_succ_0s (a b c r k : PTm n) :
    Γ ⊢[PRAAx] G2 a b c (succ r) zero (succ k) ≐ b * G2 a b c r zero (succ k) + c * G2 a b c r zero k :=
  (G2_edge_k a b c _ _).eqTrans ((G_succ_succ c b r k).eqTrans
    (congrAdd (congrMul (.eqRefl _) (G2_edge_k a b c _ _).eqSymm) (congrMul (.eqRefl _) (G2_edge_k a b c _ _).eqSymm)))

/-- The interior recurrence `G₂(r+1, i+1, k+1) = b G₂(r, i+1, k+1) + a G₂(r, i, k+1) + c G₂(r, i+1, k)`. -/
theorem G2_succ_ss (a b c r i k : PTm n) :
    Γ ⊢[PRAAx] G2 a b c (succ r) (succ i) (succ k) ≐
      b * G2 a b c r (succ i) (succ k) + (a * G2 a b c r i (succ k) + c * G2 a b c r (succ i) k) := by
  have pa : Γ ⊢[PRAAx] pw a (succ i) ≐ pw a i * a := pw_succ _ _
  have pc : Γ ⊢[PRAAx] pw c (succ k) ≐ pw c k * c := pw_succ _ _
  have mr : Γ ⊢[PRAAx] monus (succ r) (succ i) ≐ monus r i := succ_monus_succ _ _
  refine .orE (lt_or_le (succ (i + k)) r) ?_ ?_
  · -- `i + k + 2 ≤ r`: Pascal twice, all guards `1`.
    let C := lt (succ (i + k)) r :: Γ
    have h : C ⊢[PRAAx] lt (succ (i + k)) r := Prf.hyp0
    have R0 := eq_add_of_le h
    let e := monus r (succ (succ (i + k)))
    have m1 : C ⊢[PRAAx] monus (succ r) (succ i + succ k) ≐ succ e :=
      monus_of_eq (by have x := natEq R0; apply deriveNat; ipra_simps; linear_combination x)
    have m2 : C ⊢[PRAAx] monus r (succ i + succ k) ≐ e :=
      monus_of_eq (by have x := natEq R0; apply deriveNat; ipra_simps; linear_combination x)
    have m3 : C ⊢[PRAAx] monus r (i + succ k) ≐ succ e :=
      monus_of_eq (by have x := natEq R0; apply deriveNat; ipra_simps; linear_combination x)
    have m4 : C ⊢[PRAAx] monus r (succ i + k) ≐ succ e :=
      monus_of_eq (by have x := natEq R0; apply deriveNat; ipra_simps; linear_combination x)
    have mu : C ⊢[PRAAx] monus r (succ i) ≐ succ k + e :=
      monus_of_eq (by have x := natEq R0; apply deriveNat; ipra_simps; linear_combination x)
    have mi : C ⊢[PRAAx] monus r i ≐ succ (succ k + e) :=
      monus_of_eq (by have x := natEq R0; apply deriveNat; ipra_simps; linear_combination x)
    have g1 := ind_le (Γ := C) (le_of_eq_add (d := succ e) (by have x := natEq R0; apply deriveNat; ipra_simps; linear_combination x) :
      C ⊢[PRAAx] le (succ i + succ k) (succ r))
    have g2 := ind_le (Γ := C) (le_of_eq_add (d := e) (by have x := natEq R0; apply deriveNat; ipra_simps; linear_combination x) :
      C ⊢[PRAAx] le (succ i + succ k) r)
    have g3 := ind_le (Γ := C) (le_of_eq_add (d := succ e) (by have x := natEq R0; apply deriveNat; ipra_simps; linear_combination x) :
      C ⊢[PRAAx] le (i + succ k) r)
    have g4 := ind_le (Γ := C) (le_of_eq_add (d := succ e) (by have x := natEq R0; apply deriveNat; ipra_simps; linear_combination x) :
      C ⊢[PRAAx] le (succ i + k) r)
    have hir : C ⊢[PRAAx] lt i r := le_of_eq_add (d := succ k + e) (by have x := natEq R0; apply deriveNat; ipra_simps; linear_combination x)
    have hku : C ⊢[PRAAx] lt k (succ k + e) := le_of_eq_add (d := e) (by apply deriveNat; ipra_simps)
    have B1 := pascal_at hir
    have B2 := pascal_at hku
    have bt : C ⊢[PRAAx] binom (monus (succ r) (succ i)) (succ k) ≐ binom (succ k + e) k + binom (succ k + e) (succ k) :=
      (Combinatorics.BinomialTheorem.congrBinom (mr.wk.eqTrans mi) (.eqRefl _)).eqTrans B2
    have b2t : C ⊢[PRAAx] binom (monus r i) (succ k) ≐ binom (succ k + e) k + binom (succ k + e) (succ k) :=
      (Combinatorics.BinomialTheorem.congrBinom mi (.eqRefl _)).eqTrans B2
    have b1t : C ⊢[PRAAx] binom (monus r (succ i)) (succ k) ≐ binom (succ k + e) (succ k) :=
      Combinatorics.BinomialTheorem.congrBinom mu (.eqRefl _)
    have b3t : C ⊢[PRAAx] binom (monus r (succ i)) k ≐ binom (succ k + e) k :=
      Combinatorics.BinomialTheorem.congrBinom mu (.eqRefl _)
    have q1 : C ⊢[PRAAx] pw b (monus (succ r) (succ i + succ k)) ≐ pw b e * b := (congrAp2 powF m1 (.eqRefl _)).eqTrans (pw_succ _ _)
    have q2 : C ⊢[PRAAx] pw b (monus r (succ i + succ k)) ≐ pw b e := congrAp2 powF m2 (.eqRefl _)
    have q3 : C ⊢[PRAAx] pw b (monus r (i + succ k)) ≐ pw b e * b := (congrAp2 powF m3 (.eqRefl _)).eqTrans (pw_succ _ _)
    have q4 : C ⊢[PRAAx] pw b (monus r (succ i + k)) ≐ pw b e * b := (congrAp2 powF m4 (.eqRefl _)).eqTrans (pw_succ _ _)
    have L := congrMul g1 (congrMul (congrMul B1 bt) (congrMul pa.wk (congrMul pc.wk q1)))
    have T1 := congrMul (.eqRefl b) (congrMul g2 (congrMul (congrMul (.eqRefl (binom r (succ i))) b1t) (congrMul pa.wk (congrMul pc.wk q2))))
    have T2 := congrMul (.eqRefl a) (congrMul g3 (congrMul (congrMul (.eqRefl (binom r i)) b2t) (congrMul (.eqRefl (pw a i)) (congrMul pc.wk q3))))
    have T3 := congrMul (.eqRefl c) (congrMul g4 (congrMul (congrMul (.eqRefl (binom r (succ i))) b3t) (congrMul pa.wk (congrMul (.eqRefl (pw c k)) q4))))
    refine L.eqTrans (.eqTrans ?_ (congrAdd T1 (congrAdd T2 T3)).eqSymm)
    ipra_ring
  · let C := le r (succ (i + k)) :: Γ
    refine .orE (lt_or_eq_of_le (Prf.hyp0 : C ⊢[PRAAx] le r (succ (i + k)))) ?_ ?_
    · -- `r ≤ i + k`: every term vanishes.
      let C' := lt r (succ (i + k)) :: C
      have h : C' ⊢[PRAAx] le r (i + k) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
      have lt1 : C' ⊢[PRAAx] lt (succ r) (succ i + succ k) :=
        le_of_eq_add (d := monus (i + k) r) (by have x := natEq (eq_add_of_le h); apply deriveNat; ipra_simps; linear_combination x)
      have lt2 : C' ⊢[PRAAx] lt r (succ i + succ k) :=
        le_of_eq_add (d := succ (monus (i + k) r)) (by have x := natEq (eq_add_of_le h); apply deriveNat; ipra_simps; linear_combination x)
      have lt3 : C' ⊢[PRAAx] lt r (i + succ k) :=
        le_of_eq_add (d := monus (i + k) r) (by have x := natEq (eq_add_of_le h); apply deriveNat; ipra_simps; linear_combination x)
      have lt4 : C' ⊢[PRAAx] lt r (succ i + k) :=
        le_of_eq_add (d := monus (i + k) r) (by have x := natEq (eq_add_of_le h); apply deriveNat; ipra_simps; linear_combination x)
      refine (congrMul (ind_gt lt1) (.eqRefl _)).eqTrans ((zero_mul _).eqTrans (.eqTrans ?_
        (congrAdd (congrMul (.eqRefl _) (congrMul (ind_gt lt2) (.eqRefl _)))
          (congrAdd (congrMul (.eqRefl _) (congrMul (ind_gt lt3) (.eqRefl _)))
            (congrMul (.eqRefl _) (congrMul (ind_gt lt4) (.eqRefl _))))).eqSymm))
      ipra_ring
    · -- `r = i + k + 1`: Pascal once, the first term vanishes.
      let C' := (r ≐ succ (i + k)) :: C
      have h : C' ⊢[PRAAx] r ≐ succ (i + k) := Prf.hyp0
      have x := natEq h
      have m1 : C' ⊢[PRAAx] monus (succ r) (succ i + succ k) ≐ zero :=
        monus_of_eq (by apply deriveNat; ipra_simps; linear_combination x)
      have m3 : C' ⊢[PRAAx] monus r (i + succ k) ≐ zero := monus_of_eq (by apply deriveNat; ipra_simps; linear_combination x)
      have m4 : C' ⊢[PRAAx] monus r (succ i + k) ≐ zero := monus_of_eq (by apply deriveNat; ipra_simps; linear_combination x)
      have mi : C' ⊢[PRAAx] monus r i ≐ succ k := monus_of_eq (by apply deriveNat; ipra_simps; linear_combination x)
      have mu : C' ⊢[PRAAx] monus r (succ i) ≐ k := monus_of_eq (by apply deriveNat; ipra_simps; linear_combination x)
      have g1 := ind_le (Γ := C') (le_of_eq_add (d := zero) (by apply deriveNat; ipra_simps; linear_combination x) :
        C' ⊢[PRAAx] le (succ i + succ k) (succ r))
      have z2 := ind_gt (Γ := C') (le_of_eq_add (d := zero) (by apply deriveNat; ipra_simps; linear_combination -x) :
        C' ⊢[PRAAx] lt r (succ i + succ k))
      have g3 := ind_le (Γ := C') (le_of_eq_add (d := zero) (by apply deriveNat; ipra_simps; linear_combination x) :
        C' ⊢[PRAAx] le (i + succ k) r)
      have g4 := ind_le (Γ := C') (le_of_eq_add (d := zero) (by apply deriveNat; ipra_simps; linear_combination x) :
        C' ⊢[PRAAx] le (succ i + k) r)
      have hir : C' ⊢[PRAAx] lt i r := le_of_eq_add (d := k) (by apply deriveNat; ipra_simps; linear_combination x)
      have B1 := pascal_at hir
      have bt : C' ⊢[PRAAx] binom (monus (succ r) (succ i)) (succ k) ≐ one :=
        (Combinatorics.BinomialTheorem.congrBinom (mr.wk.wk.eqTrans mi) (.eqRefl _)).eqTrans (binom_self' _)
      have b2t : C' ⊢[PRAAx] binom (monus r i) (succ k) ≐ one :=
        (Combinatorics.BinomialTheorem.congrBinom mi (.eqRefl _)).eqTrans (binom_self' _)
      have b3t : C' ⊢[PRAAx] binom (monus r (succ i)) k ≐ one :=
        (Combinatorics.BinomialTheorem.congrBinom mu (.eqRefl _)).eqTrans (binom_self' _)
      have q1 : C' ⊢[PRAAx] pw b (monus (succ r) (succ i + succ k)) ≐ one := (congrAp2 powF m1 (.eqRefl _)).eqTrans (pw_zero _)
      have q3 : C' ⊢[PRAAx] pw b (monus r (i + succ k)) ≐ one := (congrAp2 powF m3 (.eqRefl _)).eqTrans (pw_zero _)
      have q4 : C' ⊢[PRAAx] pw b (monus r (succ i + k)) ≐ one := (congrAp2 powF m4 (.eqRefl _)).eqTrans (pw_zero _)
      have L := congrMul g1 (congrMul (congrMul B1 bt) (congrMul pa.wk.wk (congrMul pc.wk.wk q1)))
      have T1 := congrMul (.eqRefl b) (congrMul z2 (.eqRefl ((binom r (succ i) * binom (monus r (succ i)) (succ k)) *
        (pw a (succ i) * (pw c (succ k) * pw b (monus r (succ i + succ k)))))))
      have T2 := congrMul (.eqRefl a) (congrMul g3 (congrMul (congrMul (.eqRefl (binom r i)) b2t) (congrMul (.eqRefl (pw a i)) (congrMul pc.wk.wk q3))))
      have T3 := congrMul (.eqRefl c) (congrMul g4 (congrMul (congrMul (.eqRefl (binom r (succ i))) b3t) (congrMul pa.wk.wk (congrMul (.eqRefl (pw c k)) q4))))
      refine L.eqTrans (.eqTrans ?_ (congrAdd T1 (congrAdd T2 T3)).eqSymm)
      ipra_ring

theorem G2_zero (a b c i k : PTm n) : Γ ⊢[PRAAx] G2 a b c zero i k ≐ eqb zero i * eqb zero k := by
  refine .orE (zero_or_succ i) ?_ ?_
  · let C := (i ≐ zero) :: Γ
    have hi : C ⊢[PRAAx] i ≐ zero := Prf.hyp0
    have e : C ⊢[PRAAx] G2 a b c zero i k ≐ G2 a b c zero zero k :=
      congrMul (congrMonus (.eqRefl _) (congrMonus (congrAdd hi (.eqRefl _)) (.eqRefl _)))
        (congrMul (congrMul (Combinatorics.BinomialTheorem.congrBinom (.eqRefl _) hi)
          (Combinatorics.BinomialTheorem.congrBinom (congrMonus (.eqRefl _) hi) (.eqRefl _)))
          (congrMul (congrAp2 powF hi (.eqRefl _)) (congrMul (.eqRefl _) (congrAp2 powF (congrMonus (.eqRefl _) (congrAdd hi (.eqRefl _))) (.eqRefl _)))))
    refine e.eqTrans ((G2_edge_k a b c _ _).eqTrans ((G_zero c b k).eqTrans ?_))
    refine .eqTrans ?_ (congrMul (eqb_of_eq hi.eqSymm) (.eqRefl _)).eqSymm
    ipra_ring
  · let C := (i ≐ succ (pred i)) :: Γ
    have hlt : C ⊢[PRAAx] lt zero (i + k) := le_of_eq_add (d := pred i + k)
      (by have x := natEq (Prf.hyp0 : C ⊢[PRAAx] i ≐ succ (pred i)); apply deriveNat; ipra_simps; linear_combination x)
    have hi0 : C ⊢[PRAAx] lt zero i := le_of_eq_add (d := pred i)
      (by have x := natEq (Prf.hyp0 : C ⊢[PRAAx] i ≐ succ (pred i)); apply deriveNat; ipra_simps; linear_combination x)
    refine (congrMul (ind_gt hlt) (.eqRefl _)).eqTrans ((zero_mul _).eqTrans ?_)
    exact ((congrMul (eqb_zero_of_lt hi0) (.eqRefl _)).eqTrans (zero_mul _)).eqSymm

/-! ## The trinomial count law on the product space -/

/-- Two disjoint indicators split `[s₁ + y = i][s₂ + z = k]` for `y + z ≤ 1`. -/
theorem eqb_split2 {s₁ s₂ y z i k : PTm n} (h : Γ ⊢[PRAAx] le (y + z) one) :
    Γ ⊢[PRAAx] eqb (s₁ + y) i * eqb (s₂ + z) k ≐ monus one (y + z) * (eqb s₁ i * eqb s₂ k) +
      (y * (eqb (succ s₁) i * eqb s₂ k) + z * (eqb s₁ i * eqb (succ s₂) k)) := by
  refine .orE (zero_or_succ y) ?_ ?_
  · let C := (y ≐ zero) :: Γ
    have hy : C ⊢[PRAAx] y ≐ zero := Prf.hyp0
    have hz : C ⊢[PRAAx] le z one := le_congr ((congrAdd hy (.eqRefl _)).eqTrans (zero_add _)) (.eqRefl _) h.wk
    have e1 : C ⊢[PRAAx] eqb (s₁ + y) i ≐ eqb s₁ i := congrEqb ((congrAdd (.eqRefl _) hy).eqTrans (add_zero _)) (.eqRefl _)
    have e2 := SampleMedian.eqb_split (s := s₂) (k := k) hz
    have m : C ⊢[PRAAx] monus one (y + z) ≐ monus one z := congrMonus (.eqRefl _) ((congrAdd hy (.eqRefl _)).eqTrans (zero_add _))
    have x1 := natEq e1; have x2 := natEq e2; have x3 := natEq m; have x4 := natEq hy
    apply deriveNat; ipra_simps
    linear_combination 𝔞 (eqb (s₂ + z) k) * x1 + 𝔞 (eqb s₁ i) * x2 - 𝔞 (eqb s₁ i) * 𝔞 (eqb s₂ k) * x3 -
      𝔞 (eqb (succ s₁) i) * 𝔞 (eqb s₂ k) * x4
  · let C := (y ≐ succ (pred y)) :: Γ
    have hy : C ⊢[PRAAx] y ≐ succ (pred y) := Prf.hyp0
    have l0 : C ⊢[PRAAx] le (pred y + z) zero :=
      (succ_monus_succ _ _).eqSymm.eqTrans ((congrMonus (by have x := natEq hy; apply deriveNat; ipra_simps; linear_combination -x) (.eqRefl _)).eqTrans h.wk)
    have s0 : C ⊢[PRAAx] pred y + z ≐ zero := le_antisymm l0 (zero_le _)
    have p0 : C ⊢[PRAAx] pred y ≐ zero := le_antisymm (le_trans (le_add_right _ _) (le_congr (.eqRefl _) s0 (le_refl _))) (zero_le _)
    have z0 : C ⊢[PRAAx] z ≐ zero := le_antisymm (le_trans (le_add_left _ _) (le_congr (.eqRefl _) s0 (le_refl _))) (zero_le _)
    have y1 : C ⊢[PRAAx] y ≐ one := hy.eqTrans (congrSucc p0)
    have e1 : C ⊢[PRAAx] eqb (s₁ + y) i ≐ eqb (succ s₁) i :=
      congrEqb ((congrAdd (.eqRefl _) y1).eqTrans (succ_eq_add_one _).eqSymm) (.eqRefl _)
    have e2 : C ⊢[PRAAx] eqb (s₂ + z) k ≐ eqb s₂ k := congrEqb ((congrAdd (.eqRefl _) z0).eqTrans (add_zero _)) (.eqRefl _)
    have m : C ⊢[PRAAx] monus one (y + z) ≐ zero :=
      congrMonus (.eqRefl _) ((congrAdd y1 z0).eqTrans (add_zero _)) |>.eqTrans (monus_self _)
    have x1 := natEq e1; have x2 := natEq e2; have x3 := natEq m; have x4 := natEq y1; have x5 := natEq z0
    apply deriveNat; ipra_simps
    linear_combination 𝔞 (eqb (s₂ + z) k) * x1 + 𝔞 (eqb (succ s₁) i) * x2 - 𝔞 (eqb s₁ i) * 𝔞 (eqb s₂ k) * x3 -
      𝔞 (eqb (succ s₁) i) * 𝔞 (eqb s₂ k) * x4 - 𝔞 (eqb s₁ i) * 𝔞 (eqb (succ s₂) k) * x5

section Count2

variable (w Y Z : PTm 2)

/-- `P_r(t) [S^Y_r(t) + e₁ = i] [S^Z_r(t) + e₂ = k]`, over `0 = t`, `1 = ⟨⟨i, k⟩, ⟨r, ⟨M, x⟩⟩⟩`. -/
abbrev f2B : PTm 2 := Syn.subst ![var 0, sndT (var 1)] (TB w) *
  (eqb (Syn.subst ![var 0, sndT (var 1)] (SB Y)) (fstT (fstT (var 1))) *
    eqb (Syn.subst ![var 0, sndT (var 1)] (SB Z)) (sndT (fstT (var 1))))
abbrev f2B1 : PTm 2 := Syn.subst ![var 0, sndT (var 1)] (TB w) *
  (eqb (succ (Syn.subst ![var 0, sndT (var 1)] (SB Y))) (fstT (fstT (var 1))) *
    eqb (Syn.subst ![var 0, sndT (var 1)] (SB Z)) (sndT (fstT (var 1))))
abbrev f2B2 : PTm 2 := Syn.subst ![var 0, sndT (var 1)] (TB w) *
  (eqb (Syn.subst ![var 0, sndT (var 1)] (SB Y)) (fstT (fstT (var 1))) *
    eqb (succ (Syn.subst ![var 0, sndT (var 1)] (SB Z))) (sndT (fstT (var 1))))

abbrev F2 (i k r M x : PTm n) : PTm n := ap2 (sumF (f2B w Y Z)) (pw M r) (pairT (pairT i k) (pairT r (pairT M x)))
abbrev F21 (i k r M x : PTm n) : PTm n := ap2 (sumF (f2B1 w Y Z)) (pw M r) (pairT (pairT i k) (pairT r (pairT M x)))
abbrev F22 (i k r M x : PTm n) : PTm n := ap2 (sumF (f2B2 w Y Z)) (pw M r) (pairT (pairT i k) (pairT r (pairT M x)))

theorem sub_at (f : PTm 2) (t z : PTm n) : inst2 (Syn.subst ![var 0, sndT (var 1)] f) t z = inst2 f t (sndT z) := by
  simp only [inst2, Syn.subst_subst]; congr 1; funext j; fin_cases j <;> simp

/-- The common evaluation of the three bodies. -/
theorem f2_parts (t i k r M x : PTm n) :
    Γ ⊢[PRAAx] (inst2 (TB w) t (sndT (pairT (pairT i k) (pairT r (pairT M x)))) ≐ Pr w r t M x) ⋏
      ((inst2 (SB Y) t (sndT (pairT (pairT i k) (pairT r (pairT M x)))) ≐ Sr Y r t M x) ⋏
      ((inst2 (SB Z) t (sndT (pairT (pairT i k) (pairT r (pairT M x)))) ≐ Sr Z r t M x) ⋏
      ((fstT (fstT (pairT (pairT i k) (pairT r (pairT M x)))) ≐ i) ⋏
       (sndT (fstT (pairT (pairT i k) (pairT r (pairT M x)))) ≐ k)))) := by
  have s : Γ ⊢[PRAAx] sndT (pairT (pairT i k) (pairT r (pairT M x))) ≐ pairT r (pairT M x) := snd_pair _ _
  have f : Γ ⊢[PRAAx] fstT (pairT (pairT i k) (pairT r (pairT M x))) ≐ pairT i k := fst_pair _ _
  exact .andI ((congrInst2 _ (.eqRefl _) s).eqTrans (TB_at w _ _ _ _)) (.andI ((congrInst2 _ (.eqRefl _) s).eqTrans (SB_at Y _ _ _ _))
    (.andI ((congrInst2 _ (.eqRefl _) s).eqTrans (SB_at Z _ _ _ _)) (.andI f.fstE
      f.sndE)))

theorem f2B_at (t i k r M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (f2B w Y Z) t (pairT (pairT i k) (pairT r (pairT M x))) ≐
      Pr w r t M x * (eqb (Sr Y r t M x) i * eqb (Sr Z r t M x) k) := by
  have e : inst2 (f2B w Y Z) t (pairT (pairT i k) (pairT r (pairT M x))) =
      inst2 (TB w) t (sndT (pairT (pairT i k) (pairT r (pairT M x)))) *
        (eqb (inst2 (SB Y) t (sndT (pairT (pairT i k) (pairT r (pairT M x))))) (fstT (fstT (pairT (pairT i k) (pairT r (pairT M x))))) *
         eqb (inst2 (SB Z) t (sndT (pairT (pairT i k) (pairT r (pairT M x))))) (sndT (fstT (pairT (pairT i k) (pairT r (pairT M x)))))) := by
    rw [inst2_mul', inst2_mul']; simp only [sub_at]; simp [inst2]
  rw [e]
  have p := f2_parts (Γ := Γ) w Y Z t i k r M x
  exact congrMul (Prf.andE₁ p) (congrMul (congrEqb (Prf.andE₁ (Prf.andE₂ p)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ p)))))
    (congrEqb (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ p))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ p))))))

theorem f2B1_at (t i k r M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (f2B1 w Y Z) t (pairT (pairT i k) (pairT r (pairT M x))) ≐
      Pr w r t M x * (eqb (succ (Sr Y r t M x)) i * eqb (Sr Z r t M x) k) := by
  have e : inst2 (f2B1 w Y Z) t (pairT (pairT i k) (pairT r (pairT M x))) =
      inst2 (TB w) t (sndT (pairT (pairT i k) (pairT r (pairT M x)))) *
        (eqb (succ (inst2 (SB Y) t (sndT (pairT (pairT i k) (pairT r (pairT M x)))))) (fstT (fstT (pairT (pairT i k) (pairT r (pairT M x))))) *
         eqb (inst2 (SB Z) t (sndT (pairT (pairT i k) (pairT r (pairT M x))))) (sndT (fstT (pairT (pairT i k) (pairT r (pairT M x)))))) := by
    rw [inst2_mul', inst2_mul']; simp only [sub_at]; simp [inst2]
  rw [e]
  have p := f2_parts (Γ := Γ) w Y Z t i k r M x
  exact congrMul (Prf.andE₁ p) (congrMul (congrEqb (congrSucc (Prf.andE₁ (Prf.andE₂ p))) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ p)))))
    (congrEqb (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ p))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ p))))))

theorem f2B2_at (t i k r M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (f2B2 w Y Z) t (pairT (pairT i k) (pairT r (pairT M x))) ≐
      Pr w r t M x * (eqb (Sr Y r t M x) i * eqb (succ (Sr Z r t M x)) k) := by
  have e : inst2 (f2B2 w Y Z) t (pairT (pairT i k) (pairT r (pairT M x))) =
      inst2 (TB w) t (sndT (pairT (pairT i k) (pairT r (pairT M x)))) *
        (eqb (inst2 (SB Y) t (sndT (pairT (pairT i k) (pairT r (pairT M x))))) (fstT (fstT (pairT (pairT i k) (pairT r (pairT M x))))) *
         eqb (succ (inst2 (SB Z) t (sndT (pairT (pairT i k) (pairT r (pairT M x)))))) (sndT (fstT (pairT (pairT i k) (pairT r (pairT M x)))))) := by
    rw [inst2_mul', inst2_mul']; simp only [sub_at]; simp [inst2]
  rw [e]
  have p := f2_parts (Γ := Γ) w Y Z t i k r M x
  exact congrMul (Prf.andE₁ p) (congrMul (congrEqb (Prf.andE₁ (Prf.andE₂ p)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ p)))))
    (congrEqb (congrSucc (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ p)))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ p))))))

end Count2

section Count2b

variable (w Y Z : PTm 2)

/-- One block of `F₂_{r+1}(i, k)`. -/
theorem block_F2 {a i k r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (ha : Γ ⊢[PRAAx] lt a M)
    (hYZ : Γ ⊢[PRAAx] le (inst2 Y a x + inst2 Z a x) one) :
    Γ ⊢[PRAAx] inst2 (BlockSum.blkB (f2B w Y Z)) a (pairT (pw M r) (pairT (pairT i k) (pairT (succ r) (pairT M x)))) ≐
      (inst2 w a x * monus one (inst2 Y a x + inst2 Z a x)) * F2 w Y Z i k r M x +
        ((inst2 w a x * inst2 Y a x) * F21 w Y Z i k r M x + (inst2 w a x * inst2 Z a x) * F22 w Y Z i k r M x) := by
  refine (BlockSum.blk_at _ _ _ _).eqTrans (lin3 (f2B w Y Z) (f2B1 w Y Z) (f2B2 w Y Z) (offB (f2B w Y Z)) (.allI (.impI ?_)))
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have ha' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift M) := by
    have e := ha.shift; simp only [Fm.shift, subst_lt, subst_le, ConciseIPRA.PTm.subst_succ] at e; simpa [Syn.shift] using e
  have hYZ' : Γ.map Fm.shift ⊢[PRAAx] le (inst2 Y (Syn.shift a) (Syn.shift x) + inst2 Z (Syn.shift a) (Syn.shift x)) one := by
    have e := hYZ.shift; simp only [Fm.shift, subst_le] at e; simpa [Syn.shift, shift_inst2'] using e
  simp only [shift_pairT, shift_mul'', shift_inst2']
  have hp : Syn.shift (pw M r) = pw (Syn.shift M) (Syn.shift r) := by simp [Syn.shift]
  have hs : Syn.shift (succ r) = succ (Syn.shift r) := by simp [Syn.shift]
  have hm1 : Syn.shift (monus one (inst2 Y a x + inst2 Z a x)) =
      monus one (inst2 Y (Syn.shift a) (Syn.shift x) + inst2 Z (Syn.shift a) (Syn.shift x)) := by
    simp [Syn.shift, shift_inst2']
  rw [hp, hs, hm1]
  let C : List (Fm PTm (n + 1)) := lt (var 0) (pw (Syn.shift M) (Syn.shift r)) :: Γ.map Fm.shift
  have hu : C ⊢[PRAAx] lt (var 0) (pw (Syn.shift M) (Syn.shift r)) := Prf.hyp0
  rw [inst2_offB]
  have s : C ⊢[PRAAx] sndT (pairT (Syn.shift a * pw (Syn.shift M) (Syn.shift r))
      (pairT (pairT (Syn.shift i) (Syn.shift k)) (pairT (succ (Syn.shift r)) (pairT (Syn.shift M) (Syn.shift x))))) ≐
      pairT (pairT (Syn.shift i) (Syn.shift k)) (pairT (succ (Syn.shift r)) (pairT (Syn.shift M) (Syn.shift x))) := snd_pair _ _
  refine (congrInst2 _ (congrAdd (fst_pair _ _) (.eqRefl _)) s).eqTrans ?_
  refine (f2B_at w Y Z _ _ _ _ _ _).eqTrans ?_
  have p1 := pr_peel w (x := Syn.shift x) hM'.wk ha'.wk hu
  have sY := sr_peel Y (x := Syn.shift x) hM'.wk ha'.wk hu
  have sZ := sr_peel Z (x := Syn.shift x) hM'.wk ha'.wk hu
  refine (congrMul p1 ((congrMul (congrEqb sY (.eqRefl _)) (congrEqb sZ (.eqRefl _))).eqTrans (eqb_split2 hYZ'.wk))).eqTrans ?_
  refine .eqTrans ?_ (congrAdd (congrMul (.eqRefl _) (f2B_at w Y Z _ _ _ _ _ _)) (congrAdd (congrMul (.eqRefl _) (f2B1_at w Y Z _ _ _ _ _ _))
    (congrMul (.eqRefl _) (f2B2_at w Y Z _ _ _ _ _ _)))).eqSymm
  ipra_ring

/-- `F₂_{r+1}(i, k) = F₂_r(i, k) b + F₂¹_r(i, k) a + F₂²_r(i, k) c`. -/
theorem F2_succ {i k r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hYZ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (inst2 Y (var 0) (Syn.shift x) + inst2 Z (var 0) (Syn.shift x)) one)) :
    Γ ⊢[PRAAx] F2 w Y Z i k (succ r) M x ≐ F2 w Y Z i k r M x * ap2 (sumF (w * monus one (Y + Z))) M x +
      (F21 w Y Z i k r M x * ap2 (sumF (w * Y)) M x + F22 w Y Z i k r M x * ap2 (sumF (w * Z)) M x) := by
  refine (peel_sum (f2B w Y Z) r M _).eqTrans (lin3 (w * monus one (Y + Z)) (w * Y) (w * Z) _ (.allI (.impI ?_)))
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hYZ' := Prf.impE hYZ.allOpen.wk (Prf.hyp0 : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] _)
  simp only [shift_pairT]
  have hp : Syn.shift (pw M r) = pw (Syn.shift M) (Syn.shift r) := by simp [Syn.shift]
  have hs : Syn.shift (succ r) = succ (Syn.shift r) := by simp [Syn.shift]
  have hF : Syn.shift (F2 w Y Z i k r M x) = F2 w Y Z (Syn.shift i) (Syn.shift k) (Syn.shift r) (Syn.shift M) (Syn.shift x) := by
    simp [Syn.shift]
  have hF1 : Syn.shift (F21 w Y Z i k r M x) = F21 w Y Z (Syn.shift i) (Syn.shift k) (Syn.shift r) (Syn.shift M) (Syn.shift x) := by
    simp [Syn.shift]
  have hF2 : Syn.shift (F22 w Y Z i k r M x) = F22 w Y Z (Syn.shift i) (Syn.shift k) (Syn.shift r) (Syn.shift M) (Syn.shift x) := by
    simp [Syn.shift]
  rw [hp, hs, hF, hF1, hF2, inst2_mul', inst2_mul', inst2_mul']
  have hm : inst2 (monus one (Y + Z)) (var 0) (Syn.shift x) =
      monus one (inst2 Y (var 0) (Syn.shift x) + inst2 Z (var 0) (Syn.shift x)) := by simp [inst2]
  rw [hm]
  refine (block_F2 w Y Z hM'.wk Prf.hyp0 hYZ').eqTrans ?_
  ipra_ring

theorem F21_zero (k r M x : PTm n) : Γ ⊢[PRAAx] F21 w Y Z zero k r M x ≐ zero := by
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  refine (f2B1_at w Y Z _ _ _ _ _ _).eqTrans ?_
  have z : (lt (var 0) (Syn.shift (pw M r)) :: Γ.map Fm.shift) ⊢[PRAAx]
      eqb (succ (Sr Y (Syn.shift r) (var 0) (Syn.shift M) (Syn.shift x))) (Syn.shift zero) ≐ zero := by
    rw [ConciseIPRA.PTm.shift_zero]
    exact eqb_zero_of_gt (le_of_eq_add (d := Sr Y (Syn.shift r) (var 0) (Syn.shift M) (Syn.shift x))
      (by ipra_ring))
  exact (congrMul (.eqRefl _) ((congrMul z (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)

theorem F22_zero (i r M x : PTm n) : Γ ⊢[PRAAx] F22 w Y Z i zero r M x ≐ zero := by
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  refine (f2B2_at w Y Z _ _ _ _ _ _).eqTrans ?_
  have z : (lt (var 0) (Syn.shift (pw M r)) :: Γ.map Fm.shift) ⊢[PRAAx]
      eqb (succ (Sr Z (Syn.shift r) (var 0) (Syn.shift M) (Syn.shift x))) (Syn.shift zero) ≐ zero := by
    rw [ConciseIPRA.PTm.shift_zero]
    exact eqb_zero_of_gt (le_of_eq_add (d := Sr Z (Syn.shift r) (var 0) (Syn.shift M) (Syn.shift x))
      (by ipra_ring))
  exact (congrMul (.eqRefl _) ((congrMul (.eqRefl _) z).eqTrans (mul_zero _))).eqTrans (mul_zero _)

theorem F21_succ (i k r M x : PTm n) : Γ ⊢[PRAAx] F21 w Y Z (succ i) k r M x ≐ F2 w Y Z i k r M x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  refine (f2B1_at w Y Z _ _ _ _ _ _).eqTrans (.eqTrans ?_ (f2B_at w Y Z _ _ _ _ _ _).eqSymm)
  have hs : Syn.shift (succ i) = succ (Syn.shift i) := by simp [Syn.shift]
  rw [hs]
  exact congrMul (.eqRefl _) (congrMul (eqb_succ_succ _ _) (.eqRefl _))

theorem F22_succ (i k r M x : PTm n) : Γ ⊢[PRAAx] F22 w Y Z i (succ k) r M x ≐ F2 w Y Z i k r M x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  refine (f2B2_at w Y Z _ _ _ _ _ _).eqTrans (.eqTrans ?_ (f2B_at w Y Z _ _ _ _ _ _).eqSymm)
  have hs : Syn.shift (succ k) = succ (Syn.shift k) := by simp [Syn.shift]
  rw [hs]
  exact congrMul (.eqRefl _) (congrMul (.eqRefl _) (eqb_succ_succ _ _))

theorem F2_zero (i k M x : PTm n) : Γ ⊢[PRAAx] F2 w Y Z i k zero M x ≐ eqb zero i * eqb zero k := by
  refine (one_bound _ _ _).eqTrans ((f2B_at w Y Z _ _ _ _ _ _).eqTrans ?_)
  have p : Γ ⊢[PRAAx] Pr w zero zero M x ≐ one := (TB_at w _ _ _ _).eqSymm.eqTrans (tb_zero w M x)
  have sy : Γ ⊢[PRAAx] Sr Y zero zero M x ≐ zero := sum_zero _ _
  have sz : Γ ⊢[PRAAx] Sr Z zero zero M x ≐ zero := sum_zero _ _
  exact (congrMul p (congrMul (congrEqb sy (.eqRefl _)) (congrEqb sz (.eqRefl _)))).eqTrans (one_mul _)

end Count2b

/-! ## The trinomial count law by a nested violation count -/

theorem G2_congr {a a' b b' c c' r r' i i' k k' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b')
    (hc : Γ ⊢[PRAAx] c ≐ c') (hr : Γ ⊢[PRAAx] r ≐ r') (hi : Γ ⊢[PRAAx] i ≐ i') (hk : Γ ⊢[PRAAx] k ≐ k') :
    Γ ⊢[PRAAx] G2 a b c r i k ≐ G2 a' b' c' r' i' k' :=
  congrMul (congrMonus (.eqRefl _) (congrMonus (congrAdd hi hk) hr))
    (congrMul (congrMul (Combinatorics.BinomialTheorem.congrBinom hr hi)
        (Combinatorics.BinomialTheorem.congrBinom (congrMonus hr hi) hk))
      (congrMul (congrAp2 powF hi ha) (congrMul (congrAp2 powF hk hc) (congrAp2 powF (congrMonus hr (congrAdd hi hk)) hb))))

/-- The parameter `⟨⟨B, ⟨a, ⟨b, c⟩⟩⟩, ⟨r, ⟨M, x⟩⟩⟩` of the nested count. -/
abbrev Qt (B a b c r M x : PTm n) : PTm n := pairT (pairT B (pairT a (pairT b c))) (pairT r (pairT M x))

theorem lt_pred' {k B : PTm n} (z : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hk : Γ ⊢[PRAAx] lt k B) : Γ ⊢[PRAAx] lt (pred k) B :=
  lt_of_lt_of_le (le_congr (.eqRefl _) z.eqSymm (le_refl _)) (le_of_lt hk)

theorem step_combine {F F1 F11 F12 X1 X2 X3 a b c Gs : PTm n} (fs : Γ ⊢[PRAAx] F ≐ F1 * b + (F11 * a + F12 * c))
    (e1 : Γ ⊢[PRAAx] F1 ≐ X1) (e2 : Γ ⊢[PRAAx] F11 ≐ X2) (e3 : Γ ⊢[PRAAx] F12 ≐ X3)
    (g : Γ ⊢[PRAAx] Gs ≐ b * X1 + (a * X2 + c * X3)) : Γ ⊢[PRAAx] F ≐ Gs := by
  refine fs.eqTrans ((congrAdd (congrMul e1 (.eqRefl _)) (congrAdd (congrMul e2 (.eqRefl _)) (congrMul e3 (.eqRefl _)))).eqTrans
    (.eqTrans ?_ g.eqSymm))
  ipra_ring

section Count2c

variable (w Y Z : PTm 2)

/-- The inner violation body `1 ∸ [F₂_r(i, k) = G₂(r, i, k)]`, over `0 = k`, `1 = ⟨i, Q⟩`. -/
abbrev vI : PTm 2 :=
  monus one (eqb (ap2 (sumF (f2B w Y Z)) (pw (fstT (sndT (sndT (sndT (var 1))))) (fstT (sndT (sndT (var 1)))))
      (pairT (pairT (fstT (var 1)) (var 0)) (sndT (sndT (var 1)))))
    (G2 (fstT (sndT (fstT (sndT (var 1))))) (fstT (sndT (sndT (fstT (sndT (var 1))))))
      (sndT (sndT (sndT (fstT (sndT (var 1)))))) (fstT (sndT (sndT (var 1)))) (fstT (var 1)) (var 0)))

/-- The outer body `∑_{k<B} [F₂_r(i, k) ≠ G₂(r, i, k)]`, over `0 = i`, `1 = Q`. -/
abbrev vO : PTm 2 := ap2 (sumF (vI w Y Z)) (fstT (fstT (var 1))) (pairT (var 0) (var 1))

/-- `V₂ = ∑_{i<B} ∑_{k<B} [F₂_r(i, k) ≠ G₂(r, i, k)]`. -/
abbrev V2 (B a b c r M x : PTm n) : PTm n := ap2 (sumF (vO w Y Z)) B (Qt B a b c r M x)

theorem vI_eq (k P : PTm n) : inst2 (vI w Y Z) k P =
    monus one (eqb (ap2 (sumF (f2B w Y Z)) (pw (fstT (sndT (sndT (sndT P)))) (fstT (sndT (sndT P))))
      (pairT (pairT (fstT P) k) (sndT (sndT P))))
    (G2 (fstT (sndT (fstT (sndT P)))) (fstT (sndT (sndT (fstT (sndT P)))))
      (sndT (sndT (sndT (fstT (sndT P))))) (fstT (sndT (sndT P))) (fstT P) k)) := by
  simp [inst2]

theorem vI_at (i k B a b c r M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (vI w Y Z) k (pairT i (Qt B a b c r M x)) ≐
      monus one (eqb (F2 w Y Z i k r M x) (G2 a b c r i k)) := by
  rw [vI_eq]
  have hP : Γ ⊢[PRAAx] fstT (pairT i (Qt B a b c r M x)) ≐ i := fst_pair _ _
  have hQ : Γ ⊢[PRAAx] sndT (pairT i (Qt B a b c r M x)) ≐ Qt B a b c r M x := snd_pair _ _
  have hT : Γ ⊢[PRAAx] sndT (sndT (pairT i (Qt B a b c r M x))) ≐ pairT r (pairT M x) := hQ.sndE
  have hr : Γ ⊢[PRAAx] fstT (sndT (sndT (pairT i (Qt B a b c r M x)))) ≐ r := hT.fstE
  have hM : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (pairT i (Qt B a b c r M x))))) ≐ M :=
    hT.sndE.fstE
  have hK : Γ ⊢[PRAAx] sndT (fstT (sndT (pairT i (Qt B a b c r M x)))) ≐ pairT a (pairT b c) :=
    hQ.fstE.sndE
  have ha : Γ ⊢[PRAAx] fstT (sndT (fstT (sndT (pairT i (Qt B a b c r M x))))) ≐ a := hK.fstE
  have hbc : Γ ⊢[PRAAx] sndT (sndT (fstT (sndT (pairT i (Qt B a b c r M x))))) ≐ pairT b c :=
    hK.sndE
  have hb : Γ ⊢[PRAAx] fstT (sndT (sndT (fstT (sndT (pairT i (Qt B a b c r M x)))))) ≐ b := hbc.fstE
  have hc : Γ ⊢[PRAAx] sndT (sndT (sndT (fstT (sndT (pairT i (Qt B a b c r M x)))))) ≐ c := hbc.sndE
  exact congrMonus (.eqRefl _) (congrEqb (congrAp2 _ (congrAp2 powF hr hM) (congrPairT (congrPairT hP (.eqRefl _)) hT))
    (G2_congr ha hb hc hr hP (.eqRefl _)))

theorem vO_at (i B a b c r M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (vO w Y Z) i (Qt B a b c r M x) ≐ ap2 (sumF (vI w Y Z)) B (pairT i (Qt B a b c r M x)) := by
  have e : inst2 (vO w Y Z) i (Qt B a b c r M x) =
      ap2 (sumF (vI w Y Z)) (fstT (fstT (Qt B a b c r M x))) (pairT i (Qt B a b c r M x)) := by simp [inst2]
  rw [e]
  exact congrAp2 _ (fst_pair _ _).fstE (.eqRefl _)

theorem V2_elim {B a b c i k r M x : PTm n} (hV : Γ ⊢[PRAAx] V2 w Y Z B a b c r M x ≐ zero)
    (hi : Γ ⊢[PRAAx] lt i B) (hk : Γ ⊢[PRAAx] lt k B) : Γ ⊢[PRAAx] F2 w Y Z i k r M x ≐ G2 a b c r i k :=
  AnalyticNumberTheory.EulerProduct.eq_of_viol ((vI_at w Y Z i k B a b c r M x).eqSymm.eqTrans
    (sum_zero_elim _ ((vO_at w Y Z i B a b c r M x).eqSymm.eqTrans (sum_zero_elim _ hV hi)) hk))

theorem F2_congr {i i' k k' r M x : PTm n} (hi : Γ ⊢[PRAAx] i ≐ i') (hk : Γ ⊢[PRAAx] k ≐ k') :
    Γ ⊢[PRAAx] F2 w Y Z i k r M x ≐ F2 w Y Z i' k' r M x :=
  congrAp2 _ (.eqRefl _) (congrPairT (congrPairT hi hk) (.eqRefl _))

theorem F21_congr {i i' k k' r M x : PTm n} (hi : Γ ⊢[PRAAx] i ≐ i') (hk : Γ ⊢[PRAAx] k ≐ k') :
    Γ ⊢[PRAAx] F21 w Y Z i k r M x ≐ F21 w Y Z i' k' r M x :=
  congrAp2 _ (.eqRefl _) (congrPairT (congrPairT hi hk) (.eqRefl _))

theorem F22_congr {i i' k k' r M x : PTm n} (hi : Γ ⊢[PRAAx] i ≐ i') (hk : Γ ⊢[PRAAx] k ≐ k') :
    Γ ⊢[PRAAx] F22 w Y Z i k r M x ≐ F22 w Y Z i' k' r M x :=
  congrAp2 _ (.eqRefl _) (congrPairT (congrPairT hi hk) (.eqRefl _))

section Cases

variable {w Y Z} {B a b c i k r M x : PTm n}
  (fs : Γ ⊢[PRAAx] F2 w Y Z i k (succ r) M x ≐
    F2 w Y Z i k r M x * b + (F21 w Y Z i k r M x * a + F22 w Y Z i k r M x * c))
  (hV : Γ ⊢[PRAAx] V2 w Y Z B a b c r M x ≐ zero) (hi : Γ ⊢[PRAAx] lt i B) (hk : Γ ⊢[PRAAx] lt k B)
include fs hV hi hk

theorem case00 (zi : Γ ⊢[PRAAx] i ≐ zero) (zk : Γ ⊢[PRAAx] k ≐ zero) :
    Γ ⊢[PRAAx] F2 w Y Z i k (succ r) M x ≐ G2 a b c (succ r) i k := by
  refine step_combine fs ((V2_elim w Y Z hV hi hk).eqTrans (G2_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) zi zk))
    ((F21_congr w Y Z zi (.eqRefl _)).eqTrans (F21_zero w Y Z _ _ _ _))
    ((F22_congr w Y Z (.eqRefl _) zk).eqTrans (F22_zero w Y Z _ _ _ _)) ?_
  refine (G2_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) zi zk).eqTrans ((G2_succ_00 a b c r).eqTrans ?_)
  ipra_ring

theorem case0s (zi : Γ ⊢[PRAAx] i ≐ zero) (zk : Γ ⊢[PRAAx] k ≐ succ (pred k)) :
    Γ ⊢[PRAAx] F2 w Y Z i k (succ r) M x ≐ G2 a b c (succ r) i k := by
  refine step_combine fs ((V2_elim w Y Z hV hi hk).eqTrans (G2_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) zi zk))
    ((F21_congr w Y Z zi (.eqRefl _)).eqTrans (F21_zero w Y Z _ _ _ _))
    ((F22_congr w Y Z (.eqRefl _) zk).eqTrans ((F22_succ w Y Z _ _ _ _ _).eqTrans ((V2_elim w Y Z hV hi (lt_pred' zk hk)).eqTrans
      (G2_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) zi (.eqRefl _))))) ?_
  refine (G2_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) zi zk).eqTrans ((G2_succ_0s a b c r (pred k)).eqTrans ?_)
  ipra_ring

theorem cases0 (zi : Γ ⊢[PRAAx] i ≐ succ (pred i)) (zk : Γ ⊢[PRAAx] k ≐ zero) :
    Γ ⊢[PRAAx] F2 w Y Z i k (succ r) M x ≐ G2 a b c (succ r) i k := by
  refine step_combine fs ((V2_elim w Y Z hV hi hk).eqTrans (G2_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) zi zk))
    ((F21_congr w Y Z zi (.eqRefl _)).eqTrans ((F21_succ w Y Z _ _ _ _ _).eqTrans ((V2_elim w Y Z hV (lt_pred' zi hi) hk).eqTrans
      (G2_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) zk))))
    ((F22_congr w Y Z (.eqRefl _) zk).eqTrans (F22_zero w Y Z _ _ _ _)) ?_
  refine (G2_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) zi zk).eqTrans ((G2_succ_s0 a b c r (pred i)).eqTrans ?_)
  ipra_ring

theorem casess (zi : Γ ⊢[PRAAx] i ≐ succ (pred i)) (zk : Γ ⊢[PRAAx] k ≐ succ (pred k)) :
    Γ ⊢[PRAAx] F2 w Y Z i k (succ r) M x ≐ G2 a b c (succ r) i k :=
  step_combine fs ((V2_elim w Y Z hV hi hk).eqTrans (G2_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) zi zk))
    ((F21_congr w Y Z zi (.eqRefl _)).eqTrans ((F21_succ w Y Z _ _ _ _ _).eqTrans ((V2_elim w Y Z hV (lt_pred' zi hi) hk).eqTrans
      (G2_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) zk))))
    ((F22_congr w Y Z (.eqRefl _) zk).eqTrans ((F22_succ w Y Z _ _ _ _ _).eqTrans ((V2_elim w Y Z hV hi (lt_pred' zk hk)).eqTrans
      (G2_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) zi (.eqRefl _)))))
    ((G2_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) zi zk).eqTrans (G2_succ_ss a b c r (pred i) (pred k)))

theorem F2_step : Γ ⊢[PRAAx] F2 w Y Z i k (succ r) M x ≐ G2 a b c (succ r) i k := by
  refine .orE (zero_or_succ i) ?_ ?_
  · let C := (i ≐ zero) :: Γ
    have zi : C ⊢[PRAAx] i ≐ zero := Prf.hyp0
    refine .orE (zero_or_succ k) ?_ ?_
    · let D := (k ≐ zero) :: C
      have zk : D ⊢[PRAAx] k ≐ zero := Prf.hyp0
      exact case00 fs.wk.wk hV.wk.wk hi.wk.wk hk.wk.wk zi.wk zk
    · let D := (k ≐ succ (pred k)) :: C
      have zk : D ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
      exact case0s fs.wk.wk hV.wk.wk hi.wk.wk hk.wk.wk zi.wk zk
  · let C := (i ≐ succ (pred i)) :: Γ
    have zi : C ⊢[PRAAx] i ≐ succ (pred i) := Prf.hyp0
    refine .orE (zero_or_succ k) ?_ ?_
    · let D := (k ≐ zero) :: C
      have zk : D ⊢[PRAAx] k ≐ zero := Prf.hyp0
      exact cases0 fs.wk.wk hV.wk.wk hi.wk.wk hk.wk.wk zi.wk zk
    · let D := (k ≐ succ (pred k)) :: C
      have zk : D ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
      exact casess fs.wk.wk hV.wk.wk hi.wk.wk hk.wk.wk zi.wk zk

end Cases

theorem V2_shift (B a b c r M x : PTm n) : Syn.shift (V2 w Y Z B a b c r M x) =
    V2 w Y Z (Syn.shift B) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift r) (Syn.shift M) (Syn.shift x) := by
  simp [Syn.shift]

theorem V2_body_zero (i B a b c M x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (vI w Y Z)) B (pairT i (Qt B a b c zero M x)) ≐ zero := by
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  simp only [Qt, shift_pairT]
  refine (vI_at w Y Z _ _ _ _ _ _ _ _ _).eqTrans (AnalyticNumberTheory.EulerProduct.viol_of_eq ?_)
  rw [show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]]
  exact (F2_zero w Y Z _ _ _ _).eqTrans (G2_zero _ _ _ _ _).eqSymm

theorem V2_zero (B a b c M x : PTm n) : Γ ⊢[PRAAx] V2 w Y Z B a b c zero M x ≐ zero := by
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  simp only [Qt, shift_pairT]
  refine (vO_at w Y Z _ _ _ _ _ _ _ _).eqTrans ?_
  rw [show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]]
  exact V2_body_zero w Y Z _ _ _ _ _ _ _

theorem V2_body_succ {i B r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hYZ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (inst2 Y (var 0) (Syn.shift x) + inst2 Z (var 0) (Syn.shift x)) one))
    (hV : Γ ⊢[PRAAx] V2 w Y Z B (ap2 (sumF (w * Y)) M x) (ap2 (sumF (w * monus one (Y + Z))) M x) (ap2 (sumF (w * Z)) M x)
      r M x ≐ zero) (hi : Γ ⊢[PRAAx] lt i B) :
    Γ ⊢[PRAAx] ap2 (sumF (vI w Y Z)) B (pairT i (Qt B (ap2 (sumF (w * Y)) M x) (ap2 (sumF (w * monus one (Y + Z))) M x)
      (ap2 (sumF (w * Z)) M x) (succ r) M x)) ≐ zero := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hYZ' : Γ.map Fm.shift ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
      le (inst2 Y (var 0) (Syn.shift (Syn.shift x)) + inst2 Z (var 0) (Syn.shift (Syn.shift x))) one) := by
    simpa [Fm.shift, Syn.shift, Syn.subst_subst] using hYZ.shift
  have ea : Syn.shift (ap2 (sumF (w * Y)) M x) = ap2 (sumF (w * Y)) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have eb : Syn.shift (ap2 (sumF (w * monus one (Y + Z))) M x) =
      ap2 (sumF (w * monus one (Y + Z))) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have ec : Syn.shift (ap2 (sumF (w * Z)) M x) = ap2 (sumF (w * Z)) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have hV' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift (V2 w Y Z B (ap2 (sumF (w * Y)) M x) (ap2 (sumF (w * monus one (Y + Z))) M x)
      (ap2 (sumF (w * Z)) M x) r M x) ≐ Syn.shift zero := hV.shift
  rw [V2_shift, ea, eb, ec, show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]] at hV'
  have hi' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (Syn.shift B) := by
    have e := hi.shift; simp only [Fm.shift, subst_lt, subst_le, ConciseIPRA.PTm.subst_succ] at e; simpa [Syn.shift] using e
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  simp only [Qt, shift_pairT]
  have hsr : Syn.shift (succ r) = succ (Syn.shift r) := by simp [Syn.shift]
  rw [hsr, ea, eb, ec]
  refine (vI_at w Y Z _ _ _ _ _ _ _ _ _).eqTrans (AnalyticNumberTheory.EulerProduct.viol_of_eq ?_)
  let Δ := lt (var 0) (Syn.shift B) :: Γ.map Fm.shift
  have fs := F2_succ (Γ := Δ) w Y Z (i := Syn.shift i) (k := var 0) (r := Syn.shift r) hM'.wk hYZ'.wk
  exact F2_step fs hV'.wk hi'.wk Prf.hyp0

theorem V2_succ {B r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hYZ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (inst2 Y (var 0) (Syn.shift x) + inst2 Z (var 0) (Syn.shift x)) one))
    (hV : Γ ⊢[PRAAx] V2 w Y Z B (ap2 (sumF (w * Y)) M x) (ap2 (sumF (w * monus one (Y + Z))) M x) (ap2 (sumF (w * Z)) M x)
      r M x ≐ zero) :
    Γ ⊢[PRAAx] V2 w Y Z B (ap2 (sumF (w * Y)) M x) (ap2 (sumF (w * monus one (Y + Z))) M x) (ap2 (sumF (w * Z)) M x)
      (succ r) M x ≐ zero := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hYZ' : Γ.map Fm.shift ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
      le (inst2 Y (var 0) (Syn.shift (Syn.shift x)) + inst2 Z (var 0) (Syn.shift (Syn.shift x))) one) := by
    simpa [Fm.shift, Syn.shift, Syn.subst_subst] using hYZ.shift
  have ea : Syn.shift (ap2 (sumF (w * Y)) M x) = ap2 (sumF (w * Y)) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have eb : Syn.shift (ap2 (sumF (w * monus one (Y + Z))) M x) =
      ap2 (sumF (w * monus one (Y + Z))) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have ec : Syn.shift (ap2 (sumF (w * Z)) M x) = ap2 (sumF (w * Z)) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have hV' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift (V2 w Y Z B (ap2 (sumF (w * Y)) M x) (ap2 (sumF (w * monus one (Y + Z))) M x)
      (ap2 (sumF (w * Z)) M x) r M x) ≐ Syn.shift zero := hV.shift
  rw [V2_shift, ea, eb, ec, show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]] at hV'
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  simp only [Qt, shift_pairT]
  have hsr : Syn.shift (succ r) = succ (Syn.shift r) := by simp [Syn.shift]
  rw [hsr, ea, eb, ec]
  refine (vO_at w Y Z _ _ _ _ _ _ _ _).eqTrans ?_
  exact V2_body_succ w Y Z hM'.wk hYZ'.wk hV'.wk Prf.hyp0

/-- The trinomial count law: `F₂_r(i, k) = ∑_{t<M^r} P_r(t) [S^Y_r(t) = i] [S^Z_r(t) = k] = G₂(r, i, k)` with
`a = ∑ w Y`, `b = ∑ w (1 − Y − Z)`, `c = ∑ w Z`, for disjoint indicators `Y + Z ≤ 1`. -/
theorem count_law2 {i k r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hYZ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (inst2 Y (var 0) (Syn.shift x) + inst2 Z (var 0) (Syn.shift x)) one)) :
    Γ ⊢[PRAAx] F2 w Y Z i k r M x ≐
      G2 (ap2 (sumF (w * Y)) M x) (ap2 (sumF (w * monus one (Y + Z))) M x) (ap2 (sumF (w * Z)) M x) r i k := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hYZ' : Γ.map Fm.shift ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
      le (inst2 Y (var 0) (Syn.shift (Syn.shift x)) + inst2 Z (var 0) (Syn.shift (Syn.shift x))) one) := by
    simpa [Fm.shift, Syn.shift, Syn.subst_subst] using hYZ.shift
  have hall : Γ ⊢[PRAAx] Fm.all (V2 w Y Z (Syn.shift (succ (i + k))) (ap2 (sumF (w * Y)) (Syn.shift M) (Syn.shift x))
      (ap2 (sumF (w * monus one (Y + Z))) (Syn.shift M) (Syn.shift x)) (ap2 (sumF (w * Z)) (Syn.shift M) (Syn.shift x))
      (var 0) (Syn.shift M) (Syn.shift x) ≐ zero) := by
    ipra_qfind [V2, Qt, subst_ap2, subst_pairT]
    · exact V2_zero w Y Z _ _ _ _ _ _
    · exact V2_succ w Y Z hM'.wk hYZ'.wk Prf.hyp0
  have h := Prf.allE r hall
  simp only [V2, Qt, Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  have hi : Γ ⊢[PRAAx] lt i (succ (i + k)) := le_of_eq_add (d := k) (by ipra_ring)
  have hk : Γ ⊢[PRAAx] lt k (succ (i + k)) := le_of_eq_add (d := i) (by ipra_ring)
  exact V2_elim w Y Z h hi hk

end Count2c

/-! ## The exact odd-sample median mass -/

/-- The median event `[a ≤ ⌊N/2⌋] [b ≤ ⌊N/2⌋]`, over `0 = a`, `1 = b`, `2 = ⟨N, ⟨M, x⟩⟩`. -/
abbrev gP : PTm 3 := SampleMedian.ind (var 0) (half (fstT (var 2))) * SampleMedian.ind (var 1) (half (fstT (var 2)))

/-- The summand `[i ≤ ⌊N/2⌋] [k ≤ ⌊N/2⌋] G₂(N, i, k)`, over `0 = i`, `1 = k`, `2 = ⟨⟨a, ⟨b, c⟩⟩, N⟩`. -/
abbrev hT : PTm 3 := (SampleMedian.ind (var 0) (half (sndT (var 2))) * SampleMedian.ind (var 1) (half (sndT (var 2)))) *
  G2 (fstT (fstT (var 2))) (fstT (sndT (fstT (var 2)))) (sndT (sndT (fstT (var 2)))) (sndT (var 2)) (var 0) (var 1)

theorem ind_congr {k k' r r' : PTm n} (hk : Γ ⊢[PRAAx] k ≐ k') (hr : Γ ⊢[PRAAx] r ≐ r') :
    Γ ⊢[PRAAx] SampleMedian.ind k r ≐ SampleMedian.ind k' r' :=
  congrMonus (.eqRefl _) (congrMonus hk hr)

theorem gP_at (i k N y : PTm n) :
    Γ ⊢[PRAAx] inst3 gP i k (pairT N y) ≐ SampleMedian.ind i (half N) * SampleMedian.ind k (half N) := by
  have e : inst3 gP i k (pairT N y) =
      SampleMedian.ind i (half (fstT (pairT N y))) * SampleMedian.ind k (half (fstT (pairT N y))) := by simp [inst3]
  rw [e]
  have f : Γ ⊢[PRAAx] half (fstT (pairT N y)) ≐ half N := congrAp1 _ (fst_pair _ _)
  exact congrMul (ind_congr (.eqRefl _) f) (ind_congr (.eqRefl _) f)

theorem hT_at (i k a b c N : PTm n) :
    Γ ⊢[PRAAx] inst3 hT i k (pairT (pairT a (pairT b c)) N) ≐
      (SampleMedian.ind i (half N) * SampleMedian.ind k (half N)) * G2 a b c N i k := by
  have e : inst3 hT i k (pairT (pairT a (pairT b c)) N) =
      (SampleMedian.ind i (half (sndT (pairT (pairT a (pairT b c)) N))) *
        SampleMedian.ind k (half (sndT (pairT (pairT a (pairT b c)) N)))) *
      G2 (fstT (fstT (pairT (pairT a (pairT b c)) N))) (fstT (sndT (fstT (pairT (pairT a (pairT b c)) N))))
        (sndT (sndT (fstT (pairT (pairT a (pairT b c)) N)))) (sndT (pairT (pairT a (pairT b c)) N)) i k := by
    simp [inst3]
  rw [e]
  have s : Γ ⊢[PRAAx] sndT (pairT (pairT a (pairT b c)) N) ≐ N := snd_pair _ _
  have f : Γ ⊢[PRAAx] fstT (pairT (pairT a (pairT b c)) N) ≐ pairT a (pairT b c) := fst_pair _ _
  have hbc : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT a (pairT b c)) N)) ≐ pairT b c := f.sndE
  have hN : Γ ⊢[PRAAx] half (sndT (pairT (pairT a (pairT b c)) N)) ≐ half N := congrAp1 _ s
  exact congrMul (congrMul (ind_congr (.eqRefl _) hN) (ind_congr (.eqRefl _) hN))
    (G2_congr f.fstE hbc.fstE
      hbc.sndE s (.eqRefl _) (.eqRefl _))

section Pmf

variable (w Y Z : PTm 2)

/-- One cell of the joint LOTUS: `g(i, k) P(S^Y = i, S^Z = k) = [i ≤ n][k ≤ n] G₂(N, i, k)`. -/
theorem pmf_point {i k N M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hYZ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (inst2 Y (var 0) (Syn.shift x) + inst2 Z (var 0) (Syn.shift x)) one)) :
    Γ ⊢[PRAAx] inst2 (rowB (JointLotus.TB (TB w) (SB Y) (SB Z) gP)) k (pairT i (pairT (pw M N) (pairT N (pairT M x)))) ≐
      inst2 (rowB hT) k (pairT i (pairT (pairT (ap2 (sumF (w * Y)) M x)
        (pairT (ap2 (sumF (w * monus one (Y + Z))) M x) (ap2 (sumF (w * Z)) M x))) N)) := by
  rw [inst2_rowB, inst2_rowB, JointLotus.inst3_TB]
  have fi : Γ ⊢[PRAAx] fstT (pairT i (pairT (pw M N) (pairT N (pairT M x)))) ≐ i := fst_pair _ _
  have sy : Γ ⊢[PRAAx] sndT (pairT i (pairT (pw M N) (pairT N (pairT M x)))) ≐ pairT (pw M N) (pairT N (pairT M x)) :=
    snd_pair _ _
  have xe : Γ ⊢[PRAAx] sndT (sndT (pairT i (pairT (pw M N) (pairT N (pairT M x))))) ≐ pairT N (pairT M x) :=
    sy.sndE
  have me : Γ ⊢[PRAAx] fstT (sndT (pairT i (pairT (pw M N) (pairT N (pairT M x))))) ≐ pw M N :=
    sy.fstE
  refine .eqTrans ?_ ((congrInst3 hT (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans (hT_at _ _ _ _ _ _)).eqSymm
  refine (congrMul (congrInst3 gP fi (.eqRefl _) xe) (congrAp2 _ me (congrPairT (congrPairT fi (.eqRefl _)) xe))).eqTrans ?_
  exact congrMul (gP_at _ _ _ _) (count_law2 w Y Z hM hYZ)

theorem pmf_inner {i N M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hYZ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (inst2 Y (var 0) (Syn.shift x) + inst2 Z (var 0) (Syn.shift x)) one)) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB (JointLotus.TB (TB w) (SB Y) (SB Z) gP))) (succ N)
        (pairT i (pairT (pw M N) (pairT N (pairT M x)))) ≐
      ap2 (sumF (rowB hT)) (succ N) (pairT i (pairT (pairT (ap2 (sumF (w * Y)) M x)
        (pairT (ap2 (sumF (w * monus one (Y + Z))) M x) (ap2 (sumF (w * Z)) M x))) N)) := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hYZ' : Γ.map Fm.shift ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
      le (inst2 Y (var 0) (Syn.shift (Syn.shift x)) + inst2 Z (var 0) (Syn.shift (Syn.shift x))) one) := by
    simpa [Fm.shift, Syn.shift, Syn.subst_subst] using hYZ.shift
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  have hp : Syn.shift (pw M N) = pw (Syn.shift M) (Syn.shift N) := by simp [Syn.shift]
  have ea : Syn.shift (ap2 (sumF (w * Y)) M x) = ap2 (sumF (w * Y)) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have eb : Syn.shift (ap2 (sumF (w * monus one (Y + Z))) M x) =
      ap2 (sumF (w * monus one (Y + Z))) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have ec : Syn.shift (ap2 (sumF (w * Z)) M x) = ap2 (sumF (w * Z)) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  rw [hp, ea, eb, ec]
  exact pmf_point w Y Z hM'.wk hYZ'.wk

/-- `thm:sample-pmf`: for disjoint indicators `Y = [X < v]`, `Z = [X > v]` (`Y + Z ≤ 1`) on a finite law
`w` over `M ≥ 1` outcomes, the `N`-fold product law of the median event "at most `⌊N/2⌋` observations
below and at most `⌊N/2⌋` above" is
`∑_{t<M^N} P_N(t) [S^Y_N(t) ≤ ⌊N/2⌋] [S^Z_N(t) ≤ ⌊N/2⌋] =
  ∑_{i≤N} ∑_{k≤N} [i ≤ ⌊N/2⌋] [k ≤ ⌊N/2⌋] [i + k ≤ N] C(N, i) C(N − i, k) Aⁱ Cᵏ B^{N−i−k}`
with `A = ∑ w Y`, `B = ∑ w (1 − Y − Z)`, `C = ∑ w Z`; `C(N, i) C(N − i, k) = N! / (i! k! (N − i − k)!)`. -/
theorem sample_pmf {N M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hYZ : Γ ⊢[PRAAx] Fm.all (le (inst2 Y (var 0) (Syn.shift x) + inst2 Z (var 0) (Syn.shift x)) one)) :
    Γ ⊢[PRAAx] Expectation.Ew (TB w) (JointLotus.gX (SB Y) (SB Z) gP) (pw M N) (pairT N (pairT M x)) ≐
      ap2 (sumF (oB hT)) (succ N) (pairT (succ N) (pairT (pairT (ap2 (sumF (w * Y)) M x)
        (pairT (ap2 (sumF (w * monus one (Y + Z))) M x) (ap2 (sumF (w * Z)) M x))) N)) := by
  have le1 : ∀ {Δ : List (Fm PTm (n + 1))} {u v : PTm (n + 1)}, (Δ ⊢[PRAAx] le (u + v) one) → (Δ ⊢[PRAAx] le u one) :=
    fun {_ u v} h => le_of_eq_add (d := v + monus one (u + v)) (by
      have e := natEq (eq_add_of_le h); apply deriveNat; ipra_simps; linear_combination e)
  have le2 : ∀ {Δ : List (Fm PTm (n + 1))} {u v : PTm (n + 1)}, (Δ ⊢[PRAAx] le (u + v) one) → (Δ ⊢[PRAAx] le v one) :=
    fun {_ u v} h => le_of_eq_add (d := u + monus one (u + v)) (by
      have e := natEq (eq_add_of_le h); apply deriveNat; ipra_simps; linear_combination e)
  have hY : Γ ⊢[PRAAx] Fm.all (le (inst2 Y (var 0) (Syn.shift x)) one) := .allI (le1 hYZ.allOpen)
  have hZ : Γ ⊢[PRAAx] Fm.all (le (inst2 Z (var 0) (Syn.shift x)) one) := .allI (le2 hYZ.allOpen)
  have hYZb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (inst2 Y (var 0) (Syn.shift x) + inst2 Z (var 0) (Syn.shift x)) one) := .allI (.impI hYZ.allOpen.wk)
  have hbound : ∀ X : PTm 2, (Γ ⊢[PRAAx] Fm.all (le (inst2 X (var 0) (Syn.shift x)) one)) →
      (Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (pw M N)) ⟶
        lt (inst2 (SB X) (var 0) (Syn.shift (pairT N (pairT M x)))) (Syn.shift (succ N)))) := by
    intro X hX
    have hX' : Γ.map Fm.shift ⊢[PRAAx] Fm.all (le (inst2 X (var 0) (Syn.shift (Syn.shift x))) one) := by
      simpa [Fm.shift, Syn.shift, Syn.subst_subst] using hX.shift
    refine .allI (.impI ?_)
    simp only [shift_pairT]
    have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
    rw [hs]
    refine lt_congr (SB_at X _ _ _ _).eqSymm (.eqRefl _) ?_
    exact (succ_monus_succ _ _).eqTrans (SampleMedian.Sr_le X hX'.wk)
  have hK : Γ ⊢[PRAAx] succ N ≐ succ (pred (succ N)) := congrSucc (pred_succ _).eqSymm
  refine (JointLotus.multi_lotus (TB w) (SB Y) (SB Z) gP hK (hbound Y hY) (hbound Z hZ)).eqTrans ?_
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hYZ' : Γ.map Fm.shift ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
      le (inst2 Y (var 0) (Syn.shift (Syn.shift x)) + inst2 Z (var 0) (Syn.shift (Syn.shift x))) one) := by
    simpa [Fm.shift, Syn.shift, Syn.subst_subst] using hYZb.shift
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  refine (oB_at _ _ _ _).eqTrans (.eqTrans ?_ (oB_at _ _ _ _).eqSymm)
  have hp : Syn.shift (pw M N) = pw (Syn.shift M) (Syn.shift N) := by simp [Syn.shift]
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have ea : Syn.shift (ap2 (sumF (w * Y)) M x) = ap2 (sumF (w * Y)) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have eb : Syn.shift (ap2 (sumF (w * monus one (Y + Z))) M x) =
      ap2 (sumF (w * monus one (Y + Z))) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have ec : Syn.shift (ap2 (sumF (w * Z)) M x) = ap2 (sumF (w * Z)) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  rw [hp, hs, ea, eb, ec]
  exact pmf_inner w Y Z hM'.wk hYZ'.wk

end Pmf

end LeanProofs.IPRA.Probability.SampleMedianPmf
