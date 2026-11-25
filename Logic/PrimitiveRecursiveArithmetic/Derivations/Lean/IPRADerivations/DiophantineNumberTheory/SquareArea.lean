import IPRADerivations.DiophantineNumberTheory.FermatQuartic
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.CommonLemmas

/-!
# No right triangle has square area

Packet: `diophantine-number-theory/mordell_weil_ipra` (`thm:no-square-area`, with
`lem:normal-triangle`, `lem:pyth` and `lem:fermat-step`): there are no positive integers with

  `a² + b² = c²`,  `a b = 2 s²`.

A square-area triangle `(a, b, c, s)` yields one with a smaller hypotenuse (`smaller`):

* `nonprim_step` (`lem:normal-triangle`): if `g = gcd(a, b) ≥ 2`, then `g ∣ c`; one of `a/g`, `b/g`
  is even, so `a b/g² = 2K` and `s² = g² K`, whence `g ∣ s`, and `(a/g, b/g, c/g, s/g)` is one.
* `prim_even` (`lem:pyth`): for `gcd(a, b) = 1`, `a = 2H` even, `b` odd, the parametrization
  `b + n² = m²`, `H = m n`, `c = m² + n²` gives `m n b = s²` with `m, n, b` pairwise coprime;
* `prim_core` (`lem:fermat-step`): then `m = r²`, `n = s'²`, `b = w²`; `w² + n² = m²` with `w` odd
  forces `n` even (`odd_sq_sum`), so `s' = 2 s₁`, and the parametrization of `(w, n = 2H', r²)`
  gives `m'² + n'² = r²`, `m' n' = H' = 2 s₁²`: the triangle `(m', n', r, s₁)` with
  `r ≤ m < c`. This uses a second Pythagorean parametrization where the packet factors
  `m² − n² = (m + n)(m − n)`; both give a triangle with hypotenuse `r`.

The descent (`DescentEx`) runs over `⟨a, ⟨b, s⟩⟩` with hypotenuse `c`, the indicator `χ` and the
bound `⟨a, ⟨b, s⟩⟩ < (c + X)² + c + 1`, `X = (2c)² + c`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.SquareArea

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.Pythagoras (two_pos pyth_at pm pn)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd le_sq odd_sq odd_sq_sum not_both_even)
open LeanProofs.IPRA.DiophantineNumberTheory.FermatQuartic (congrSg congrPair zo_eqb zo_sg zo_mul mul_one_split
  eq_of_eqb pos_of_sg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- A square-area triangle: `a, b, s ≥ 1`, `a² + b² = c²`, `a b = 2 s²`. -/
abbrev tri (A B C S : PTm n) : Fm PTm n :=
  (A ≐ succ (pred A)) ⋏ (B ≐ succ (pred B)) ⋏ (S ≐ succ (pred S)) ⋏ (A * A + B * B ≐ C * C) ⋏
    (A * B ≐ two * (S * S))

/-- A continuation: from a triangle with hypotenuse below `C`, under any extension of `Γ`, derive `φ`. -/
def TCont (Γ : List (Fm PTm n)) (C : PTm n) (φ : Fm PTm n) : Prop :=
  ∀ (Δ : List (Fm PTm n)), (∀ (ψ : Fm PTm n), Prf PRAAx Γ ψ → Prf PRAAx Δ ψ) →
    ∀ (a b c s : PTm n), Prf PRAAx Δ (tri a b c s) → Prf PRAAx Δ (lt c C) → Prf PRAAx Δ φ

theorem TCont.wk {C : PTm n} {φ : Fm PTm n} (k : TCont Γ C φ) (χ : Fm PTm n) : TCont (χ :: Γ) C φ :=
  fun Δ l => k Δ (fun ψ h => l ψ h.wk)

theorem TCont.apply {C a b c s : PTm n} {φ : Fm PTm n} (k : TCont Γ C φ) (ht : Γ ⊢[PRAAx] tri a b c s)
    (hlt : Γ ⊢[PRAAx] lt c C) : Γ ⊢[PRAAx] φ := k Γ (fun _ h => h) a b c s ht hlt

theorem mk_tri {A B C S : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B))
    (hS : Γ ⊢[PRAAx] S ≐ succ (pred S)) (hE : Γ ⊢[PRAAx] A * A + B * B ≐ C * C)
    (hR : Γ ⊢[PRAAx] A * B ≐ two * (S * S)) : Γ ⊢[PRAAx] tri A B C S :=
  .andI hA (.andI hB (.andI hS (.andI hE hR)))

/-- `x ≤ x² < x² + y²` for `x, y ≥ 1`. -/
theorem lt_sq_add {x y : PTm n} (hy : Γ ⊢[PRAAx] y ≐ succ (pred y)) : Γ ⊢[PRAAx] lt (x * x) (x * x + y * y) := by
  refine le_of_eq_add (d := pred (y * y)) ?_
  have e := natEq (pos_mul hy hy)
  apply deriveNat; ipra_simps; linear_combination e

/-- An odd number is not twice another. -/
theorem odd_not_even {B K : PTm n} (φ : Fm PTm n) (hBo : Γ ⊢[PRAAx] B ≐ two * half B + one)
    (h : Γ ⊢[PRAAx] B ≐ two * K) : Γ ⊢[PRAAx] φ :=
  even_ne_odd _ (h.eqSymm.eqTrans hBo)

/-! ## Coprimality from `b + n² = m²` -/

theorem cop_left {m n' B : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (gmn : Γ ⊢[PRAAx] gcd m n' ≐ one)
    (e : Γ ⊢[PRAAx] B + n' * n' ≐ m * m) : Γ ⊢[PRAAx] gcd m B ≐ one := by
  have hd := gcd_pos (B := B) hm
  have hdd := gcd_dvd' (b := B) hm
  have dmm := dvd_mul' hd m (Prf.andE₁ hdd)
  have dnn := dvd_sub' hd (dvd_congr ((add_comm _ _).eqTrans e).eqSymm dmm) (Prf.andE₂ hdd)
  have hc := coprime_dvd_left hd (Prf.andE₁ hdd) (coprime_mul hm gmn gmn)
  exact eq_one_of_coprime_dvd hd ((congrGcd (.eqRefl _) (.eqRefl _)).eqTrans hc) dnn

theorem cop_right {m n' B : PTm n} (hn : Γ ⊢[PRAAx] n' ≐ succ (pred n'))
    (gmn : Γ ⊢[PRAAx] gcd m n' ≐ one) (e : Γ ⊢[PRAAx] B + n' * n' ≐ m * m) : Γ ⊢[PRAAx] gcd n' B ≐ one := by
  have hd := gcd_pos (B := B) hn
  have hdd := gcd_dvd' (b := B) hn
  have dnn := dvd_mul' hd n' (Prf.andE₁ hdd)
  have dmm := dvd_congr e (dvd_add' hd (Prf.andE₂ hdd) dnn)
  have gnm := gcd_comm_one hn gmn
  have hc := coprime_dvd_left hd (Prf.andE₁ hdd) (coprime_mul hn gnm gnm)
  exact eq_one_of_coprime_dvd hd hc dmm

/-! ## The primitive step -/

/-- From `m n b = s²` with `b + n² = m²`, `b` odd: the smaller triangle `(m', n', r, s₁)`. -/
theorem prim_core {m n' B C S : PTm n} {φ : Fm PTm n} (k : TCont Γ C φ)
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hBo : Γ ⊢[PRAAx] B ≐ two * half B + one)
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hn : Γ ⊢[PRAAx] n' ≐ succ (pred n'))
    (eB : Γ ⊢[PRAAx] B + n' * n' ≐ m * m) (eC : Γ ⊢[PRAAx] C ≐ m * m + n' * n')
    (gmn : Γ ⊢[PRAAx] gcd m n' ≐ one) (eS : Γ ⊢[PRAAx] (m * n') * B ≐ S * S) : Γ ⊢[PRAAx] φ := by
  have gmB := cop_left hm gmn eB
  have gnB := cop_right hn gmn eB
  have s₀ := natEq eS
  have er := square_of_coprime hm (coprime_mul hm gmn gmB)
    (by apply deriveNat; ipra_simps; linear_combination s₀ : Γ ⊢[PRAAx] m * (n' * B) ≐ S * S)
  have es := square_of_coprime hn (coprime_mul hn (gcd_comm_one hn gmn) gnB)
    (by apply deriveNat; ipra_simps; linear_combination s₀ : Γ ⊢[PRAAx] n' * (m * B) ≐ S * S)
  have ew := square_of_coprime hB (coprime_mul hB (gcd_comm_one hB gmB) (gcd_comm_one hB gnB))
    (by apply deriveNat; ipra_simps; linear_combination s₀ : Γ ⊢[PRAAx] B * (m * n') ≐ S * S)
  have hr := gcd_pos (B := S) hm
  have hs := gcd_pos (B := S) hn
  have hw := gcd_pos (B := S) hB
  -- `w² + n² = m²`.
  have eW : Γ ⊢[PRAAx] gcd B S * gcd B S + n' * n' ≐ m * m := (congrAdd ew.eqSymm (.eqRefl _)).eqTrans eB
  -- `w` is odd.
  have hwo : Γ ⊢[PRAAx] gcd B S ≐ two * half (gcd B S) + one := by
    refine .orE (even_or_odd (gcd B S)) ?_ Prf.hyp0
    have h : ((gcd B S ≐ two * half (gcd B S)) :: Γ) ⊢[PRAAx] B ≐ two * (half (gcd B S) * gcd B S) :=
      ew.wk.eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (by ipra_ring))
    exact odd_not_even _ hBo.wk h
  -- `n` is even.
  refine .orE (even_or_odd n') ?_ (odd_sq_sum _ hwo.wk Prf.hyp0 eW.wk)
  have hne : ((n' ≐ two * half n') :: Γ) ⊢[PRAAx] n' ≐ two * half n' := Prf.hyp0
  -- `s'` is even.
  refine .orE (even_or_odd (gcd n' S)) ?_ ?_
  swap
  · have h : ((gcd n' S ≐ two * half (gcd n' S) + one) :: (n' ≐ two * half n') :: Γ) ⊢[PRAAx]
        two * half n' ≐ two * (two * (half (gcd n' S) * half (gcd n' S)) + two * half (gcd n' S)) + one :=
      (hne.wk.eqSymm.eqTrans es.wk.wk).eqTrans (odd_sq Prf.hyp0)
    exact even_ne_odd _ h
  have hse : ((gcd n' S ≐ two * half (gcd n' S)) :: (n' ≐ two * half n') :: Γ) ⊢[PRAAx]
      gcd n' S ≐ two * half (gcd n' S) := Prf.hyp0
  have hs₁ := pos_of_eq_mul hs.wk.wk hse
  -- `n = 2H'`, `H' = 2 s₁²`.
  have en : ((gcd n' S ≐ two * half (gcd n' S)) :: (n' ≐ two * half n') :: Γ) ⊢[PRAAx]
      n' ≐ two * (two * (half (gcd n' S) * half (gcd n' S))) :=
    es.wk.wk.eqTrans ((congrMul hse hse).eqTrans (by ipra_ring))
  have hH' := pos_mul two_pos (pos_mul hs₁ hs₁)
  have hE' : ((gcd n' S ≐ two * half (gcd n' S)) :: (n' ≐ two * half n') :: Γ) ⊢[PRAAx]
      gcd B S * gcd B S + (two * (two * (half (gcd n' S) * half (gcd n' S)))) *
        (two * (two * (half (gcd n' S) * half (gcd n' S)))) ≐ (gcd m S * gcd m S) * (gcd m S * gcd m S) :=
    (congrAdd (.eqRefl _) (congrMul en.eqSymm en.eqSymm)).eqTrans (eW.wk.wk.eqTrans (congrMul er.wk.wk er.wk.wk))
  have gwn : Γ ⊢[PRAAx] gcd (gcd B S) n' ≐ one :=
    coprime_dvd_left hw (dvd_of_eq' hw ew) (gcd_comm_one hB gnB)
  have hg' := (congrGcd (.eqRefl _) en.eqSymm).eqTrans gwn.wk.wk
  have P := pyth_at hw.wk.wk hH' hE' hg'
  have eH := Prf.andE₁ (Prf.andE₂ P)
  have hm' := pos_of_eq_mul hH' (eH.eqTrans (mul_comm _ _))
  have hn' := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ P)))
  refine (k.wk _ |>.wk _).apply (mk_tri hm' hn' hs₁ (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ P))).eqSymm eH.eqSymm) ?_
  -- `r ≤ r² = m ≤ m² < m² + n² = c`.
  have l₁ := le_trans (le_sq hr) (le_congr er (.eqRefl _) (le_refl _))
  have l₂ := le_trans l₁ (le_sq hm)
  exact (lt_of_le_of_lt l₂ (le_congr (.eqRefl _) eC.eqSymm (lt_sq_add hn))).wk.wk

/-- The primitive step with `a = 2H` even and `b` odd. -/
theorem prim_even {A B C S : PTm n} {φ : Fm PTm n} (k : TCont Γ C φ)
    (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B))
    (hAe : Γ ⊢[PRAAx] A ≐ two * half A) (hBo : Γ ⊢[PRAAx] B ≐ two * half B + one)
    (hg : Γ ⊢[PRAAx] gcd A B ≐ one) (hE : Γ ⊢[PRAAx] A * A + B * B ≐ C * C)
    (hR : Γ ⊢[PRAAx] A * B ≐ two * (S * S)) : Γ ⊢[PRAAx] φ := by
  have hH := pos_of_eq_mul hA hAe
  have hE' : Γ ⊢[PRAAx] B * B + (two * half A) * (two * half A) ≐ C * C :=
    (add_comm _ _).eqTrans ((congrAdd (congrMul hAe.eqSymm hAe.eqSymm) (.eqRefl _)).eqTrans hE)
  have hg' := (congrGcd (.eqRefl _) hAe.eqSymm).eqTrans (gcd_comm_one hB hg)
  have P := pyth_at hB hH hE' hg'
  have eH := Prf.andE₁ (Prf.andE₂ P)
  have hm := pos_of_eq_mul hH (eH.eqTrans (mul_comm _ _))
  have hn := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ P)))
  have eS : Γ ⊢[PRAAx] (pm B (half A) C * pn B (half A) C) * B ≐ S * S := by
    refine mul_cancel two_pos ?_
    have a := natEq hR; have b := natEq hAe; have c := natEq eH
    apply deriveNat; ipra_simps
    linear_combination a - 𝔞 B * b - 2 * 𝔞 B * c
  exact prim_core k hB hBo hm hn (Prf.andE₁ P) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ P)))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ P)))) eS

/-! ## The non-primitive step -/

theorem c_pos {A B C : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hE : Γ ⊢[PRAAx] A * A + B * B ≐ C * C) :
    Γ ⊢[PRAAx] C ≐ succ (pred C) := by
  refine .orE (zero_or_succ C) ?_ Prf.hyp0
  have h0 := add_eq_zero_left ((hE.wk.eqTrans (congrMul Prf.hyp0 Prf.hyp0)).eqTrans (mul_zero _))
  exact succ_ne_zero' _ ((pos_mul hA hA).wk.eqSymm.eqTrans h0)

/-- With `A₁ B₁ = 2K`: divide everything by `g = gcd(a, b) ≥ 2`. -/
theorem nonprim_core {A B C S g A₁ B₁ K c : PTm n} {φ : Fm PTm n} (k : TCont Γ C φ)
    (hA₁ : Γ ⊢[PRAAx] A₁ ≐ succ (pred A₁)) (hB₁ : Γ ⊢[PRAAx] B₁ ≐ succ (pred B₁))
    (hS : Γ ⊢[PRAAx] S ≐ succ (pred S)) (hC : Γ ⊢[PRAAx] C ≐ succ (pred C))
    (hgp : Γ ⊢[PRAAx] g ≐ succ (pred g)) (hg2 : Γ ⊢[PRAAx] g ≐ succ (succ c))
    (ex : Γ ⊢[PRAAx] A ≐ g * A₁) (ey : Γ ⊢[PRAAx] B ≐ g * B₁) (hE : Γ ⊢[PRAAx] A * A + B * B ≐ C * C)
    (hR : Γ ⊢[PRAAx] A * B ≐ two * (S * S)) (hK : Γ ⊢[PRAAx] A₁ * B₁ ≐ two * K) : Γ ⊢[PRAAx] φ := by
  have hG := pos_mul hgp hgp
  have a₁ := natEq ex; have b₁ := natEq ey; have e₁ := natEq hE; have r₁ := natEq hR; have k₁ := natEq hK
  -- `g ∣ c`.
  have hcc : Γ ⊢[PRAAx] C * C ≐ (g * g) * (A₁ * A₁ + B₁ * B₁) := by
    apply deriveNat; ipra_simps
    linear_combination -e₁ + (𝔞 A + 𝔞 g * 𝔞 A₁) * a₁ + (𝔞 B + 𝔞 g * 𝔞 B₁) * b₁
  have ec := eq_of_dvd' hgp (dvd_of_sq_dvd_sq hgp hC (dvd_of_eq' hG hcc))
  have hC₁ := pos_of_eq_mul hC ec
  -- `s² = g² K`, so `g ∣ s`.
  have hss : Γ ⊢[PRAAx] S * S ≐ (g * g) * K := by
    refine mul_cancel two_pos ?_
    apply deriveNat; ipra_simps
    linear_combination -r₁ + 𝔞 B * a₁ + 𝔞 g * 𝔞 A₁ * b₁ + 𝔞 g ^ 2 * k₁
  have es := eq_of_dvd' hgp (dvd_of_sq_dvd_sq hgp hS (dvd_of_eq' hG hss))
  have hS₁ := pos_of_eq_mul hS es
  have c₁ := natEq ec; have s₁ := natEq es; have q := natEq hss
  have hE₁ : Γ ⊢[PRAAx] A₁ * A₁ + B₁ * B₁ ≐ quo C g * quo C g := by
    refine mul_cancel hG ?_
    have h := natEq hcc
    apply deriveNat; ipra_simps
    linear_combination -h + (𝔞 C + 𝔞 g * 𝔞 (quo C g)) * c₁
  have hR₁ : Γ ⊢[PRAAx] A₁ * B₁ ≐ two * (quo S g * quo S g) := by
    refine mul_cancel hG ?_
    apply deriveNat; ipra_simps
    linear_combination 𝔞 g ^ 2 * k₁ - 2 * q + 2 * (𝔞 S + 𝔞 g * 𝔞 (quo S g)) * s₁
  refine k.apply (mk_tri hA₁ hB₁ hS₁ hE₁ hR₁) ?_
  refine le_of_eq_add (d := pred (quo C g) + c * quo C g) ?_
  have g₂ := natEq hg2; have p := natEq hC₁
  apply deriveNat; ipra_simps
  linear_combination c₁ + 𝔞 (quo C g) * g₂ + p

theorem nonprim_step {A B C S c : PTm n} {φ : Fm PTm n} (k : TCont Γ C φ) (ht : Γ ⊢[PRAAx] tri A B C S)
    (hg2 : Γ ⊢[PRAAx] gcd A B ≐ succ (succ c)) : Γ ⊢[PRAAx] φ := by
  have hA := Prf.andE₁ ht; have hB := Prf.andE₁ (Prf.andE₂ ht); have hS := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ ht))
  have hE := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ ht)))
  have hR := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ ht)))
  have hgp := gcd_pos (B := B) hA
  have hgd := gcd_dvd' (b := B) hA
  have ex := eq_of_dvd' hgp (Prf.andE₁ hgd)
  have ey := eq_of_dvd' hgp (Prf.andE₂ hgd)
  have hA₁ := pos_of_eq_mul hA ex
  have hB₁ := pos_of_eq_mul hB ey
  have hC := c_pos hA hE
  have hcop := coprime_quotients (c := B) hA
  -- `A₁² + B₁² = (c/g)²`, needed for the parity of `A₁, B₁`.
  have hcc : Γ ⊢[PRAAx] (gcd A B * gcd A B) * (quo A (gcd A B) * quo A (gcd A B) + quo B (gcd A B) * quo B (gcd A B)) ≐
      (gcd A B * gcd A B) * (quo C (gcd A B) * quo C (gcd A B)) := by
    have a₁ := natEq ex; have b₁ := natEq ey; have e₁ := natEq hE
    have ec := natEq (eq_of_dvd' hgp (dvd_of_sq_dvd_sq hgp hC (dvd_of_eq' (pos_mul hgp hgp)
      (by apply deriveNat; ipra_simps
          linear_combination -e₁ + (𝔞 A + 𝔞 (gcd A B) * 𝔞 (quo A (gcd A B))) * a₁ +
            (𝔞 B + 𝔞 (gcd A B) * 𝔞 (quo B (gcd A B))) * b₁ :
        Γ ⊢[PRAAx] C * C ≐ (gcd A B * gcd A B) *
          (quo A (gcd A B) * quo A (gcd A B) + quo B (gcd A B) * quo B (gcd A B))))))
    apply deriveNat; ipra_simps
    linear_combination e₁ - (𝔞 A + 𝔞 (gcd A B) * 𝔞 (quo A (gcd A B))) * a₁ -
      (𝔞 B + 𝔞 (gcd A B) * 𝔞 (quo B (gcd A B))) * b₁ + (𝔞 C + 𝔞 (gcd A B) * 𝔞 (quo C (gcd A B))) * ec
  have hE₁ := mul_cancel (pos_mul hgp hgp) hcc
  refine .orE (even_or_odd (quo A (gcd A B))) ?_ ?_
  · have hK : ((quo A (gcd A B) ≐ two * half (quo A (gcd A B))) :: Γ) ⊢[PRAAx]
        quo A (gcd A B) * quo B (gcd A B) ≐ two * (half (quo A (gcd A B)) * quo B (gcd A B)) :=
      (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (by ipra_ring)
    exact nonprim_core (k.wk _) hA₁.wk hB₁.wk hS.wk hC.wk hgp.wk hg2.wk ex.wk ey.wk hE.wk hR.wk hK
  · refine .orE (even_or_odd (quo B (gcd A B))) ?_ ?_
    · have hK : ((quo B (gcd A B) ≐ two * half (quo B (gcd A B))) ::
          (quo A (gcd A B) ≐ two * half (quo A (gcd A B)) + one) :: Γ) ⊢[PRAAx]
          quo A (gcd A B) * quo B (gcd A B) ≐ two * (quo A (gcd A B) * half (quo B (gcd A B))) :=
        (congrMul (.eqRefl _) Prf.hyp0).eqTrans (by ipra_ring)
      exact nonprim_core ((k.wk _).wk _) hA₁.wk.wk hB₁.wk.wk hS.wk.wk hC.wk.wk hgp.wk.wk hg2.wk.wk ex.wk.wk
        ey.wk.wk hE.wk.wk hR.wk.wk hK
    · exact odd_sq_sum _ Prf.hyp1 Prf.hyp0 hE₁.wk.wk

/-! ## The step for every triangle -/

theorem smaller {A B C S : PTm n} {φ : Fm PTm n} (k : TCont Γ C φ) (ht : Γ ⊢[PRAAx] tri A B C S) :
    Γ ⊢[PRAAx] φ := by
  have hA := Prf.andE₁ ht; have hB := Prf.andE₁ (Prf.andE₂ ht)
  have hE := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ ht)))
  have hR := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ ht)))
  have hgp := gcd_pos (B := B) hA
  refine .orE (zero_or_succ (pred (gcd A B))) ?_ ?_
  · have hg1 : ((pred (gcd A B) ≐ zero) :: Γ) ⊢[PRAAx] gcd A B ≐ one := hgp.wk.eqTrans (congrSucc Prf.hyp0)
    refine .orE (even_or_odd A) ?_ ?_
    · refine .orE (even_or_odd B) (not_both_even _ hg1.wk.wk Prf.hyp1 Prf.hyp0) ?_
      exact prim_even ((k.wk _).wk _ |>.wk _) hA.wk.wk.wk hB.wk.wk.wk Prf.hyp1 Prf.hyp0 hg1.wk.wk hE.wk.wk.wk
        hR.wk.wk.wk
    · refine .orE (even_or_odd B) ?_ ?_
      · exact prim_even ((k.wk _).wk _ |>.wk _) hB.wk.wk.wk hA.wk.wk.wk Prf.hyp0 Prf.hyp1
          (gcd_comm_one hB.wk.wk.wk hg1.wk.wk) ((add_comm _ _).eqTrans hE).wk.wk.wk
          ((mul_comm _ _).eqTrans hR).wk.wk.wk
      · exact odd_sq_sum _ Prf.hyp1 Prf.hyp0 hE.wk.wk.wk
  · exact nonprim_step (k.wk _) ht.wk (hgp.wk.eqTrans (congrSucc Prf.hyp0))

/-! ## The indicator -/

/-- `χ(a, c)` for `a = ⟨A, ⟨B, S⟩⟩`. -/
abbrev chiF : PTm 2 :=
  eqb (var 0) (pairT (fstT (var 0)) (pairT (fstT (sndT (var 0))) (sndT (sndT (var 0))))) *
    (sg (fstT (var 0)) * (sg (fstT (sndT (var 0))) * (sg (sndT (sndT (var 0))) *
      (eqb (fstT (var 0) * fstT (var 0) + fstT (sndT (var 0)) * fstT (sndT (var 0))) (var 1 * var 1) *
        eqb (fstT (var 0) * fstT (sndT (var 0))) (two * (sndT (sndT (var 0)) * sndT (sndT (var 0))))))))

/-- `X(c) = (2c)² + c` bounds `⟨B, S⟩`, and `(c + X)² + c` bounds `⟨A, ⟨B, S⟩⟩`. -/
abbrev bX {n : ℕ} (c : PTm n) : PTm n := (two * c) * (two * c) + c
abbrev betaF : PTm 1 := succ ((var 0 + bX (var 0)) * (var 0 + bX (var 0)) + var 0)

theorem inst2_chi (a c : PTm n) : inst2 chiF a c =
    eqb a (pairT (fstT a) (pairT (fstT (sndT a)) (sndT (sndT a)))) *
      (sg (fstT a) * (sg (fstT (sndT a)) * (sg (sndT (sndT a)) *
        (eqb (fstT a * fstT a + fstT (sndT a) * fstT (sndT a)) (c * c) *
          eqb (fstT a * fstT (sndT a)) (two * (sndT (sndT a) * sndT (sndT a))))))) := by
  simp [inst2]

theorem inst1_beta (c : PTm n) : inst1 betaF c = succ ((c + bX c) * (c + bX c) + c) := by simp [inst1]

theorem chi_spec {a c : PTm n} (h : Γ ⊢[PRAAx] inst2 chiF a c ≐ one) :
    Γ ⊢[PRAAx] (a ≐ pairT (fstT a) (pairT (fstT (sndT a)) (sndT (sndT a)))) ⋏
      tri (fstT a) (fstT (sndT a)) c (sndT (sndT a)) := by
  rw [inst2_chi] at h
  have s₁ := mul_one_split (zo_eqb _ _) h
  have s₂ := mul_one_split (zo_sg _) (Prf.andE₂ s₁)
  have s₃ := mul_one_split (zo_sg _) (Prf.andE₂ s₂)
  have s₄ := mul_one_split (zo_sg _) (Prf.andE₂ s₃)
  have s₅ := mul_one_split (zo_eqb _ _) (Prf.andE₂ s₄)
  exact .andI (eq_of_eqb (Prf.andE₁ s₁)) (mk_tri (pos_of_sg (Prf.andE₁ s₂)) (pos_of_sg (Prf.andE₁ s₃))
    (pos_of_sg (Prf.andE₁ s₄)) (eq_of_eqb (Prf.andE₁ s₅)) (eq_of_eqb (Prf.andE₂ s₅)))

theorem chi_of_tri {A B C S : PTm n} (ht : Γ ⊢[PRAAx] tri A B C S) :
    Γ ⊢[PRAAx] inst2 chiF (pairT A (pairT B S)) C ≐ one := by
  rw [inst2_chi]
  have f := fst_pair (Γ := Γ) A (pairT B S)
  have s := snd_pair (Γ := Γ) A (pairT B S)
  have fB := (congrFst s).eqTrans (fst_pair (Γ := Γ) B S)
  have sS := (congrSnd s).eqTrans (snd_pair (Γ := Γ) B S)
  have e₁ := eqb_of_eq (congrPair (Γ := Γ) f.eqSymm (congrPair fB.eqSymm sS.eqSymm))
  have e₂ := (congrSg f).eqTrans ((congrSg (Prf.andE₁ ht)).eqTrans (sg_succ _))
  have e₃ := (congrSg fB).eqTrans ((congrSg (Prf.andE₁ (Prf.andE₂ ht))).eqTrans (sg_succ _))
  have e₄ := (congrSg sS).eqTrans ((congrSg (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ ht)))).eqTrans (sg_succ _))
  have e₅ := eqb_of_eq ((congrAdd (congrMul f f) (congrMul fB fB)).eqTrans
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ ht)))))
  have e₆ := eqb_of_eq ((congrMul f fB).eqTrans ((Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ ht)))).eqTrans
    (congrMul (.eqRefl _) (congrMul sS sS)).eqSymm))
  refine withEq e₁ fun h₁ => withEq e₂ fun h₂ => withEq e₃ fun h₃ => withEq e₄ fun h₄ =>
    withEq e₅ fun h₅ => withEq e₆ fun h₆ => ?_
  apply deriveNat; ipra_simps; rw [h₁, h₂, h₃, h₄, h₅, h₆]; ring

/-! ## The descent hypotheses -/

theorem h01 : ([] : List (Fm PTm 2)) ⊢[PRAAx]
    (inst2 chiF (var 0) (var 1) ≐ zero) ⋎ (inst2 chiF (var 0) (var 1) ≐ one) := by
  rw [inst2_chi]
  exact zo_mul (zo_eqb _ _) (zo_mul (zo_sg _) (zo_mul (zo_sg _) (zo_mul (zo_sg _) (zo_mul (zo_eqb _ _) (zo_eqb _ _)))))

theorem h0 : ([] : List (Fm PTm 2)) ⊢[PRAAx] inst2 chiF (var 0) zero ≐ zero := by
  rw [inst2_chi]
  refine .orE (zero_or_succ (fstT (var 0 : PTm 2))) ?_ ?_
  · have e : ([fstT (var 0 : PTm 2) ≐ zero] : List (Fm PTm 2)) ⊢[PRAAx] sg (fstT (var 0)) ≐ zero :=
      (congrSg Prf.hyp0).eqTrans sg_zero
    refine withEq e fun h => ?_
    apply deriveNat; ipra_simps; rw [h]; ring
  · have hf : ([fstT (var 0 : PTm 2) ≐ succ (pred (fstT (var 0)))] : List (Fm PTm 2)) ⊢[PRAAx]
        fstT (var 0) ≐ succ (pred (fstT (var 0))) := Prf.hyp0
    have h2 := pos_mul hf hf
    have hne : ((fstT (var 0 : PTm 2) ≐ succ (pred (fstT (var 0)))) :: []) ⊢[PRAAx]
        neg (fstT (var 0) * fstT (var 0) + fstT (sndT (var 0)) * fstT (sndT (var 0)) ≐ zero * zero) := by
      refine .impI ?_
      exact succ_ne_zero' _ (h2.wk.eqSymm.eqTrans (add_eq_zero_left (Prf.hyp0.eqTrans (mul_zero _))))
    have e := eqb_of_ne hne
    refine withEq e fun h => ?_
    apply deriveNat; ipra_simps; rw [h]; ring

alias le_add_mono := Common.add_le_add

/-- `⟨x, y⟩ = (x + y)² + x`. -/
theorem pair_le {x y X Y : PTm n} (hx : Γ ⊢[PRAAx] le x X) (hy : Γ ⊢[PRAAx] le y Y) :
    Γ ⊢[PRAAx] le (pairT x y) ((X + Y) * (X + Y) + X) :=
  le_add_mono (sq_le_sq (le_add_mono hx hy)) hx

theorem hb : ([inst2 chiF (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx]
    lt (var 0) (inst1 betaF (var 1)) := by
  rw [inst1_beta]
  have sp := chi_spec (Γ := ([inst2 chiF (var 0) (var 1) ≐ one] : List (Fm PTm 2))) (a := (var 0 : PTm 2))
    (c := var 1) Prf.hyp0
  have ea := Prf.andE₁ sp
  have ht := Prf.andE₂ sp
  have hA := Prf.andE₁ ht; have hB := Prf.andE₁ (Prf.andE₂ ht); have hS := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ ht))
  have hE := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ ht)))
  have hR := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ ht)))
  have lA := le_of_sq_le (le_of_eq_add (d := fstT (sndT (var 0)) * fstT (sndT (var 0))) hE.eqSymm)
  have lB := le_of_sq_le (le_of_eq_add (d := fstT (var 0) * fstT (var 0))
    (hE.eqSymm.eqTrans (add_comm _ _)))
  -- `s ≤ s² ≤ 2 s² = a b ≤ c²`.
  have lS : ([inst2 chiF (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx] le (sndT (sndT (var 0))) (var 1) := by
    refine le_of_sq_le (le_trans ?_ (le_mul_mono lA lB))
    exact le_of_eq_add (d := sndT (sndT (var 0)) * sndT (sndT (var 0)))
      (hR.eqTrans (by ipra_ring))
  have lBS := le_congr (.eqRefl _) (.eqRefl _) (pair_le lB lS)
  have lBS' : ([inst2 chiF (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx]
      le (pairT (fstT (sndT (var 0))) (sndT (sndT (var 0)))) (bX (var 1)) :=
    le_congr (.eqRefl _) (by ipra_ring) lBS
  have la := le_congr ea.eqSymm (.eqRefl _) (pair_le lA lBS')
  exact (succ_monus_succ _ _).eqTrans la

theorem hstep : ([var 1 ≐ succ (pred (var 1)), inst2 chiF (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx]
    Fm.ex (Fm.ex ((inst2 chiF (var 1) (var 0) ≐ one) ⋏ lt (var 0) (var 3))) := by
  have sp := Prf.andE₂ (chi_spec (Γ := ([var 1 ≐ succ (pred (var 1)), inst2 chiF (var 0) (var 1) ≐ one] :
    List (Fm PTm 2))) (a := (var 0 : PTm 2)) (c := var 1) Prf.hyp1)
  refine smaller (C := var 1) ?_ sp
  intro Δ _ a b c s ht hlt
  refine .exI (pairT a (pairT b s)) (.exI c ?_)
  simpa [Syn.up] using (Prf.andI (chi_of_tri ht) hlt)

theorem hyps : DescentEx.Hyps chiF betaF := ⟨h01, h0, hb, hstep⟩

/-! ## The theorem -/

/-- `thm:no-square-area`: no `a, b, s ≥ 1`, `c` with `a² + b² = c²` and `a b = 2 s²`;
variables `0 = a − 1`, `1 = b − 1`, `2 = c`, `3 = s − 1`. -/
abbrev squareAreaFormula : Fm PTm 4 :=
  neg ((succ (var 0) * succ (var 0) + succ (var 1) * succ (var 1) ≐ var 2 * var 2) ⋏
    (succ (var 0) * succ (var 1) ≐ two * (succ (var 3) * succ (var 3))))

theorem square_area : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 squareAreaFormula := by
  refine closeUniv 4 (.impI ?_)
  have ht : ([(succ (var 0) * succ (var 0) + succ (var 1) * succ (var 1) ≐ var 2 * var 2) ⋏
      (succ (var 0) * succ (var 1) ≐ two * (succ (var 3) * succ (var 3)))] : List (Fm PTm 4)) ⊢[PRAAx]
      tri (succ (var 0)) (succ (var 1)) (var 2) (succ (var 3)) :=
    mk_tri (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm)
      (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0)
  have d := inst (Γ := [(succ (var 0) * succ (var 0) + succ (var 1) * succ (var 1) ≐ var 2 * var 2) ⋏
      (succ (var 0) * succ (var 1) ≐ two * (succ (var 3) * succ (var 3)))])
    (.impI (DescentEx.descent hyps)) (![pairT (succ (var 0)) (pairT (succ (var 1)) (succ (var 3))), var 2] : Fin 2 → PTm 4)
  simp only [Fm.subst_imp, Fm.subst_eq, subst_inst2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Fm.subst_bot] at d
  exact .impE d (chi_of_tri ht)

end LeanProofs.IPRA.DiophantineNumberTheory.SquareArea
