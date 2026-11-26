import IPRADerivations.DiophantineNumberTheory.KhinchinK2Widths
import IPRADerivations.DiophantineNumberTheory.KhinchinK2RoundZ
import IPRADerivations.Foundations.FiniteSetExponential
import IPRADerivations.Foundations.BlockPartitionSum
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.SubstCommand
import IPRADerivations.Core.Header

/-!
# One complete (K2) round from `ψ` and `D` (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"Amplification by the finitely many
residual gaps": "At each stage, write `[0,1] ∖ U_j` as a finite list of closed rational gaps. For each gap of
positive length, apply the block construction to its interior `J` and add its block union to `U_j` … Freeze the old
gap list at the beginning of the round … If `R_j = |[0,1] ∖ U_j|`, (K11) gives `R_{j+1} ≤ (1 − 1/b₀) R_j`."

A round starts from the coarse grid of `G = p + 1` cells and the residual bits `w_g ∈ {0, 1}`, stored as the binary
code `c` (`w_g = ⌊c/2^g⌋ mod 2`, `evB`). Every cell, uncovered or not, receives the block of
`KhinchinK2Widths.cell_cover`; all the round's data are explicit terms in `p` and the parameters `N, C, x`:

* `K₀ = 512 G + N`, `B = D(2^{K₀})` scales, `Q = 2^{K₀+B}`, numerator range `M = ⟨⟨C, x⟩, Q⟩`,
  `R = 4 Q² C`, `G' = G R²`, and `r = R! R²` fine cells per coarse cell, so the fine grid is `T = R! G' = r G`;
* `hcov_all`, `hH_all`, `hw_all`: the three per-cell hypotheses of `KhinchinK2RoundZ.k2_round_z`, discharged;
* `tB`: the next round's residual bit at fine cell `y = g r + k`: `w_g [the block of cell g missed y]`
  (`KhinchinRoundBits.fB`); its code `c' = code(tB, rG, 2)` (`FiniteSetExponential.code`) is the next state;
* `chain`: `Σ_{y < rG} w'_y = Σ_{g<G} rs_g` (the code decodes by `ev_curry_of_lt`, the fine sum splits into the
  coarse blocks by `BlockPartitionSum.block_sum`, each block is the cell residual by `cell_eq`);
* `round_step`: `16384 Σ_{y<rG} w'_y ≤ 16383 r Σ_{g<G} w_g`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinK2Step

open_ipra
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement (pos_of_eq)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (shift_inst2')
open LeanProofs.IPRA.Foundations.FiniteSetExponential (code ev_curry_of_lt dg_lt pair_fst pair_snd)
open LeanProofs.IPRA.Foundations.BlockPartitionSum (blockB inst2_blockB block_sum)
open LeanProofs.IPRA.Foundations.CrossingSearch (monus_of_eq)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockScales (Xt Qk bB pw_mono2)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellParams (αc γc b0c cell_hH)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinMargin (monus_le')
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundBits (fB fB_at f_le_one)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundCounts (rsB wB inst2_rsB inst2_wB)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundWrapper (px)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinK2RoundZ (vZ k2_round_z)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinK2Widths (monoF kdF shift_monoF pos_of_one one_le_pw kd_tail
  wbK hW_pt r4_at cell_cover sh le_pairT_right)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The round's data -/

/-- `K₀ = 512 G + N`, `G = p + 1`. -/
def K0r (p N : PTm n) : PTm n := num 512 * succ p + N
/-- `B = D(2^{K₀})` scales. -/
def Br (Dm : PTm 2) (p N x : PTm n) : PTm n := inst2 Dm (pw two (K0r p N)) x
/-- `Q = 2^{K₀+B}`. -/
def Qr (Dm : PTm 2) (p N x : PTm n) : PTm n := pw two (K0r p N + Br Dm p N x)
/-- `R = 4 Q² C`. -/
def Rr (Dm : PTm 2) (p N C x : PTm n) : PTm n := num 4 * (Qr Dm p N x * Qr Dm p N x) * C
/-- `G' = G R²`. -/
def Gr (Dm : PTm 2) (p N C x : PTm n) : PTm n := succ p * (Rr Dm p N C x * Rr Dm p N C x)
/-- `r = R! R²` fine cells per coarse cell. -/
def rr (Dm : PTm 2) (p N C x : PTm n) : PTm n := fact (Rr Dm p N C x) * (Rr Dm p N C x * Rr Dm p N C x)
/-- The packed round parameters of `KhinchinRoundWrapper.px`. -/
abbrev xr (Dm : PTm 2) (p N C x : PTm n) : PTm n :=
  px (rr Dm p N C x) (Br Dm p N x) (K0r p N) (pairT (pairT C x) (Qr Dm p N x)) (Rr Dm p N C x) (Gr Dm p N C x) p

ipra_subst K0r
ipra_subst Br
ipra_subst Qr [subst_ap2]
ipra_subst Rr
ipra_subst Gr
ipra_subst rr [subst_ap2]

theorem hK_r (p N : PTm n) : Γ ⊢[PRAAx] le (num 512 * succ p) (K0r p N) := by
  show Γ ⊢[PRAAx] le (num 512 * succ p) (num 512 * succ p + N)
  ipra_le 𝔞 N

theorem hQ_r (Dm : PTm 2) (p N x : PTm n) :
    Γ ⊢[PRAAx] le (pw two (K0r p N + Br Dm p N x)) (Qr Dm p N x) := le_refl _

theorem hR4_r (Dm : PTm 2) (p N C x : PTm n) :
    Γ ⊢[PRAAx] le (num 4 * (pw two (K0r p N + Br Dm p N x) * pw two (K0r p N + Br Dm p N x)) * C)
      (Rr Dm p N C x) := le_refl _

theorem hRG_r (Dm : PTm 2) (p N C x : PTm n) :
    Γ ⊢[PRAAx] le (Rr Dm p N C x * Rr Dm p N C x) (Gr Dm p N C x) := by
  show Γ ⊢[PRAAx] le (Rr Dm p N C x * Rr Dm p N C x) (succ p * (Rr Dm p N C x * Rr Dm p N C x))
  ipra_le 𝔞 p * 𝔞 (Rr Dm p N C x) * 𝔞 (Rr Dm p N C x)

theorem hT_r (Dm : PTm 2) (p N C x : PTm n) :
    Γ ⊢[PRAAx] fact (Rr Dm p N C x) * Gr Dm p N C x ≐ rr Dm p N C x * succ p := by
  show Γ ⊢[PRAAx] fact (Rr Dm p N C x) * (succ p * (Rr Dm p N C x * Rr Dm p N C x)) ≐
    fact (Rr Dm p N C x) * (Rr Dm p N C x * Rr Dm p N C x) * succ p
  ipra_ring

theorem hM_r (Dm : PTm 2) (p N C x : PTm n) : Γ ⊢[PRAAx] le one (pairT (pairT C x) (Qr Dm p N x)) :=
  le_trans (one_le_pw (K0r p N + Br Dm p N x)) (le_pairT_right (one_le_pw (K0r p N + Br Dm p N x)))

theorem hD_r (Ψ Dm : PTm 2) {p N C x : PTm n} (hKD : Γ ⊢[PRAAx] kdF Ψ Dm C x) :
    Γ ⊢[PRAAx] le (C + ap2 (sumF Ψ) (pw two (K0r p N)) x) (ap2 (sumF Ψ) (pw two (K0r p N + Br Dm p N x)) x) :=
  kd_tail Ψ Dm (K0r p N) hKD

theorem hr_r (Dm : PTm 2) {p N C x : PTm n} (hC : Γ ⊢[PRAAx] le one C) :
    Γ ⊢[PRAAx] rr Dm p N C x ≐ succ (pred (rr Dm p N C x)) := by
  have hQ := one_le_pw (Γ := Γ) (K0r p N + Br Dm p N x)
  have hR : Γ ⊢[PRAAx] le one (Rr Dm p N C x) := by
    show Γ ⊢[PRAAx] le one (num 4 * (pw two (K0r p N + Br Dm p N x) * pw two (K0r p N + Br Dm p N x)) * C)
    ipra_le 4 * 𝔞 (pw two (K0r p N + Br Dm p N x)) * 𝔞 (pw two (K0r p N + Br Dm p N x)) * sl hC +
      4 * 𝔞 (pw two (K0r p N + Br Dm p N x)) * sl hQ + 4 * sl hQ + 3
  have ef := natEq (fact_pos (Γ := Γ) (Rr Dm p N C x))
  refine pos_of_one ?_
  show Γ ⊢[PRAAx] le one (fact (Rr Dm p N C x) * (Rr Dm p N C x * Rr Dm p N C x))
  ipra_le 𝔞 (pred (fact (Rr Dm p N C x))) * 𝔞 (Rr Dm p N C x) * 𝔞 (Rr Dm p N C x) +
    𝔞 (Rr Dm p N C x) * sl hR + sl hR with 𝔞 (Rr Dm p N C x) * 𝔞 (Rr Dm p N C x) * ef

/-! ## The per-cell hypotheses of the round -/

/-- `hcov` of `k2_round_z`: the block of every cell covers its share. -/
theorem hcov_all (Ψ Dm : PTm 2) {p N C x : PTm n} (hC : Γ ⊢[PRAAx] le one C) (hmono : Γ ⊢[PRAAx] monoF Ψ x)
    (hKD : Γ ⊢[PRAAx] kdF Ψ Dm C x) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ p)) ⟶
      le (monus (γc (var 0)) (αc (var 0)) * (fact (Syn.shift (Rr Dm p N C x)) * Syn.shift (Gr Dm p N C x)))
        (num 8192 * succ (b0c (Syn.shift p)) *
          ap2 (sumF (sg (oB (bB (wbK Ψ)))))
            (fact (Syn.shift (Rr Dm p N C x)) * Syn.shift (Gr Dm p N C x) *
              Syn.shift (pairT (pairT C x) (Qr Dm p N x)))
            (pairT (Syn.shift (Br Dm p N x)) (Xt (Syn.shift (K0r p N)) (Syn.shift (pairT (pairT C x) (Qr Dm p N x)))
              (Syn.shift (Rr Dm p N C x)) (Syn.shift (Gr Dm p N C x)) (αc (var 0)) (γc (var 0))
              (b0c (Syn.shift p)))))) := by
  refine .allI (.impI ?_)
  let ψ0 : Fm PTm (n + 1) := lt (var 0) (Syn.shift (succ p))
  have hg : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift p)) := by
    have h0 : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift (succ p)) := Prf.hyp0
    rwa [show Syn.shift (succ p) = succ (Syn.shift p) by simp [Syn.shift]] at h0
  have hm := sh ψ0 hmono
  rw [shift_monoF] at hm
  have hC' : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift C) := by
    simpa [Fm.shift, Syn.shift] using sh ψ0 hC
  have hD' : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift C + ap2 (sumF Ψ) (pw two (Syn.shift (K0r p N))) (Syn.shift x))
      (ap2 (sumF Ψ) (pw two (Syn.shift (K0r p N) + Syn.shift (Br Dm p N x))) (Syn.shift x)) := by
    simpa [Fm.shift, Syn.shift] using sh ψ0 (hD_r Ψ Dm (p := p) (N := N) hKD)
  have hK' : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx] le (num 512 * succ (Syn.shift p)) (Syn.shift (K0r p N)) := by
    simpa [Fm.shift, Syn.shift] using sh ψ0 (hK_r (Γ := Γ) p N)
  have hQ' : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx]
      le (pw two (Syn.shift (K0r p N) + Syn.shift (Br Dm p N x))) (Syn.shift (Qr Dm p N x)) := by
    simpa [Fm.shift, Syn.shift] using sh ψ0 (hQ_r (Γ := Γ) Dm p N x)
  have hR4' : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx]
      le (num 4 * (pw two (Syn.shift (K0r p N) + Syn.shift (Br Dm p N x)) *
        pw two (Syn.shift (K0r p N) + Syn.shift (Br Dm p N x))) * Syn.shift C) (Syn.shift (Rr Dm p N C x)) := by
    simpa [Fm.shift, Syn.shift] using sh ψ0 (hR4_r (Γ := Γ) Dm p N C x)
  have hRG' : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx]
      le (Syn.shift (Rr Dm p N C x) * Syn.shift (Rr Dm p N C x)) (Syn.shift (Gr Dm p N C x)) := by
    simpa [Fm.shift, Syn.shift] using sh ψ0 (hRG_r (Γ := Γ) Dm p N C x)
  rw [shift_pairT, shift_pairT]
  exact cell_cover Ψ hg hC' hm hD' hK' hQ' hR4' hRG'

/-- `succ p ≤ Q_k²` for `Q_k = 2^{K₀+k}` and `K₀ ≥ 512 (p+1)`. -/
theorem gQ {p K0 : PTm n} (k : PTm n) (hK : Γ ⊢[PRAAx] le (num 512 * succ p) K0) :
    Γ ⊢[PRAAx] le (succ p) (Qk K0 k * Qk K0 k) := by
  have h1 := LeanProofs.IPRA.AnalyticNumberTheory.Valuation.lt_pw (Γ := Γ) (le_refl two) K0
  have h0 : Γ ⊢[PRAAx] le zero k := by ipra_le 𝔞 k
  have h2 : Γ ⊢[PRAAx] le (pw two K0) (Qk K0 k) :=
    le_congr (KhinchinBlockGeo.congrPw2 (add_zero K0)) (.eqRefl _) (pw_mono2 (K0 := K0) h0)
  have h3 := one_le_pw (Γ := Γ) (K0 + k)
  ipra_le 𝔞 (Qk K0 k) * sl h3 + sl h2 + sl h1 + sl hK + 511 * 𝔞 p + 512

/-- The right margin of one scale in one cell. -/
theorem hH_pt (Ψ : PTm 2) {g k p K0 B C x Q R G r : PTm n} (hk : Γ ⊢[PRAAx] lt k B) (hC : Γ ⊢[PRAAx] le one C)
    (hR4 : Γ ⊢[PRAAx] le (num 4 * (pw two (K0 + B) * pw two (K0 + B)) * C) R)
    (hT : Γ ⊢[PRAAx] fact R * G ≐ r * succ p) (hK : Γ ⊢[PRAAx] le (num 512 * succ p) K0) :
    Γ ⊢[PRAAx] le (fact R * G * γc g +
        inst2 (wbK Ψ) k (Xt K0 (pairT (pairT C x) Q) R G (αc g) (γc g) (b0c p)) * succ (b0c p))
      ((r * g + r) * succ (b0c p)) := by
  have hW := hW_pt Ψ (x := x) (Q := Q) (G := G) (α := αc g) (γ := γc g) (b0 := b0c p) hC
    (r4_at (le_of_lt hk) hR4)
  have hW' := le_congr (.eqRefl _) hT hW
  have cH := cell_hH (g := g) hW' (gQ k hK)
  have eT := natEq hT
  ipra_le sl cH with (-(4 * 𝔞 g + 3)) * eT

/-- `hH` of `k2_round_z`: the margins of every scale in every cell. -/
theorem hH_all (Ψ Dm : PTm 2) {p N C x : PTm n} (hC : Γ ⊢[PRAAx] le one C) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ p)) ⟶
      Fm.all (lt (var 0) (Syn.shift (Syn.shift (Br Dm p N x))) ⟶
        le (fact (Syn.shift (Syn.shift (Rr Dm p N C x))) * Syn.shift (Syn.shift (Gr Dm p N C x)) *
              Syn.shift (γc (var 0)) +
            inst2 (wbK Ψ) (var 0) (Xt (Syn.shift (Syn.shift (K0r p N)))
              (Syn.shift (Syn.shift (pairT (pairT C x) (Qr Dm p N x)))) (Syn.shift (Syn.shift (Rr Dm p N C x)))
              (Syn.shift (Syn.shift (Gr Dm p N C x))) (Syn.shift (αc (var 0))) (Syn.shift (γc (var 0)))
              (Syn.shift (b0c (Syn.shift p)))) * succ (Syn.shift (b0c (Syn.shift p))))
          (Syn.shift (Syn.shift (rr Dm p N C x) * var 0 + Syn.shift (rr Dm p N C x)) *
            succ (Syn.shift (b0c (Syn.shift p)))))) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let ψ0 : Fm PTm (n + 1) := lt (var 0) (Syn.shift (succ p))
  let ψ1 : Fm PTm (n + 2) := lt (var 0) (Syn.shift (Syn.shift (Br Dm p N x)))
  have s2 : ∀ {φ : Fm PTm n}, (Γ ⊢[PRAAx] φ) → ((ψ1 :: (ψ0 :: Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx]
      Fm.shift (Fm.shift φ)) := fun h => sh ψ1 (sh ψ0 h)
  have hC' : (ψ1 :: (ψ0 :: Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx] le one (Syn.shift (Syn.shift C)) := by
    simpa [Fm.shift, Syn.shift] using s2 hC
  have hR4' : (ψ1 :: (ψ0 :: Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx]
      le (num 4 * (pw two (Syn.shift (Syn.shift (K0r p N)) + Syn.shift (Syn.shift (Br Dm p N x))) *
          pw two (Syn.shift (Syn.shift (K0r p N)) + Syn.shift (Syn.shift (Br Dm p N x)))) * Syn.shift (Syn.shift C))
        (Syn.shift (Syn.shift (Rr Dm p N C x))) := by
    simpa [Fm.shift, Syn.shift] using s2 (hR4_r (Γ := Γ) Dm p N C x)
  have hT' : (ψ1 :: (ψ0 :: Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx]
      fact (Syn.shift (Syn.shift (Rr Dm p N C x))) * Syn.shift (Syn.shift (Gr Dm p N C x)) ≐
        Syn.shift (Syn.shift (rr Dm p N C x)) * succ (Syn.shift (Syn.shift p)) := by
    simpa [Fm.shift, Syn.shift] using s2 (hT_r (Γ := Γ) Dm p N C x)
  have hK' : (ψ1 :: (ψ0 :: Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx]
      le (num 512 * succ (Syn.shift (Syn.shift p))) (Syn.shift (Syn.shift (K0r p N))) := by
    simpa [Fm.shift, Syn.shift] using s2 (hK_r (Γ := Γ) p N)
  rw [show Syn.shift (γc (var 0 : PTm (n + 1))) = γc (var 1) by simp [Syn.shift],
    show Syn.shift (αc (var 0 : PTm (n + 1))) = αc (var 1) by simp [Syn.shift],
    show Syn.shift (b0c (Syn.shift p)) = b0c (Syn.shift (Syn.shift p)) by simp [Syn.shift],
    show Syn.shift (Syn.shift (rr Dm p N C x) * var 0 + Syn.shift (rr Dm p N C x)) =
      Syn.shift (Syn.shift (rr Dm p N C x)) * var 1 + Syn.shift (Syn.shift (rr Dm p N C x)) by
      simp [Syn.shift]]
  rw [shift_pairT, shift_pairT, shift_pairT, shift_pairT]
  exact hH_pt Ψ Prf.hyp0 hC' hR4' hT' hK'

/-! ## The residual bits -/

/-- The residual bit of cell `g` in the code `y = ⟨c, x⟩`: `w_g = ⌊c / 2^g⌋ mod 2`. -/
def wbit : PTm 2 := rem (quo (fstT (var 1)) (pw two (var 0))) two

theorem inst2_wbit (g y : PTm n) : inst2 wbit g y = rem (quo (fstT y) (pw two g)) two := by
  simp [inst2, wbit, subst_ap2]

/-- The bit of a code: `evB(g, c) = ⌊c / 2^g⌋ mod 2`. -/
def evB : PTm 2 := rem (quo (var 1) (pw two (var 0))) two

theorem inst2_evB (g c : PTm n) : inst2 evB g c = rem (quo c (pw two g)) two := by
  simp [inst2, evB, subst_ap2]

theorem two_pos : Γ ⊢[PRAAx] two ≐ succ (pred two) := pos_of_one (by ipra_le 1)

theorem wbit_le (g y : PTm n) : Γ ⊢[PRAAx] le (inst2 wbit g y) one := by
  rw [inst2_wbit]
  have h := dg_lt (Γ := Γ) two_pos g (fstT y)
  ipra_le sl h

/-- `hw` of `k2_round_z`. -/
theorem hw_all (p y : PTm n) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ p)) ⟶ le (inst2 wbit (var 0) (Syn.shift y)) one) :=
  .allI (.impI (wbit_le _ _))

/-- The block endpoints `e(g) = g r` (with `r = fstT (sndT X)`). -/
def eB : PTm 2 := var 0 * fstT (sndT (var 1))

theorem inst2_eB (g y : PTm n) : inst2 eB g y = g * fstT (sndT y) := by simp [inst2, eB]

/-- The next residual bit at fine cell `y` (cell `g = ⌊y/r⌋`, offset `k = y mod r`): `w_g [v(k, g) = 0]`. -/
def tB (wb : PTm 2) : PTm 2 :=
  Syn.subst ![rem (var 0) (fstT (sndT (var 1))),
    pairT (inst2 wbit (quo (var 0) (fstT (sndT (var 1)))) (var 1)) (pairT (quo (var 0) (fstT (sndT (var 1)))) (var 1))]
    (fB (vZ wb))

theorem inst2_tB (wb : PTm 2) (y X : PTm n) :
    inst2 (tB wb) y X = inst2 (fB (vZ wb)) (rem y (fstT (sndT X)))
      (pairT (inst2 wbit (quo y (fstT (sndT X))) X) (pairT (quo y (fstT (sndT X))) X)) := by
  simp only [inst2, tB]
  rw [Syn.subst_subst]
  exact congrArg (fun σ => Syn.subst σ (fB (vZ wb))) (funext fun i => by fin_cases i <;> simp [wbit, subst_ap2])

theorem tB_at (wb : PTm 2) {g k r X : PTm n} (hr : Γ ⊢[PRAAx] r ≐ succ (pred r))
    (er : Γ ⊢[PRAAx] fstT (sndT X) ≐ r) (hk : Γ ⊢[PRAAx] lt k r) :
    Γ ⊢[PRAAx] inst2 (tB wb) (g * fstT (sndT X) + k) X ≐
      inst2 (fB (vZ wb)) k (pairT (inst2 wbit g X) (pairT g X)) := by
  rw [inst2_tB]
  have hm : Γ ⊢[PRAAx] fstT (sndT X) ≐ succ (pred (fstT (sndT X))) := pos_of_eq (er.eqTrans hr)
  have hk' := lt_congr (.eqRefl k) er.eqSymm hk
  have eq := pair_fst (i := g) hm hk'
  have er' := pair_snd (i := g) hm hk'
  exact congrInst2 (fB (vZ wb)) er' (congrPairT (congrInst2 wbit eq (.eqRefl X)) (congrPairT eq (.eqRefl X)))

theorem tB_lt (wb : PTm 2) (y X : PTm n) : Γ ⊢[PRAAx] lt (inst2 (tB wb) y X) two := by
  rw [inst2_tB]
  have e := fB_at (Γ := Γ) (vZ wb) (rem y (fstT (sndT X))) (inst2 wbit (quo y (fstT (sndT X))) X)
    (pairT (quo y (fstT (sndT X))) X)
  have h := f_le_one (wbit_le (Γ := Γ) (quo y (fstT (sndT X))) X)
    (monus_le' one (sg (inst2 (vZ wb) (rem y (fstT (sndT X))) (pairT (quo y (fstT (sndT X))) X))))
  have h2 := le_congr e.eqSymm (.eqRefl _) h
  ipra_le sl h2

/-- A coarse block of the next residual is the cell residual `rs_g` of `KhinchinRoundCounts`. -/
theorem cell_eq (wb : PTm 2) {g r X : PTm n} (hr : Γ ⊢[PRAAx] r ≐ succ (pred r))
    (er : Γ ⊢[PRAAx] fstT (sndT X) ≐ r) :
    Γ ⊢[PRAAx] inst2 (blockB (tB wb) eB) g X ≐ inst2 (rsB wbit (vZ wb)) g (pairT r X) := by
  rw [inst2_blockB, inst2_rsB, inst2_eB, inst2_eB]
  have el : Γ ⊢[PRAAx] monus (succ g * fstT (sndT X)) (g * fstT (sndT X)) ≐ r := by
    refine monus_of_eq ?_
    ipra_lc natEq er
  have inner : Γ ⊢[PRAAx] ap2 (sumF (offB (tB wb))) r (pairT (g * fstT (sndT X)) X) ≐
      ap2 (sumF (fB (vZ wb))) r (pairT (inst2 wbit g X) (pairT g X)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    let ψ0 : Fm PTm (n + 1) := lt (var 0) (Syn.shift r)
    rw [inst2_offB, shift_pairT, shift_pairT, shift_pairT, shift_inst2']
    have hr' : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx] Syn.shift r ≐ succ (pred (Syn.shift r)) := by
      simpa [Fm.shift, Syn.shift] using sh ψ0 hr
    have er' : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx] fstT (sndT (Syn.shift X)) ≐ Syn.shift r := by
      simpa [Fm.shift, Syn.shift] using sh ψ0 er
    have t := tB_at wb (g := Syn.shift g) hr' er' Prf.hyp0
    have e1 : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx] fstT (pairT (Syn.shift (g * fstT (sndT X))) (Syn.shift X)) + var 0 ≐
        Syn.shift g * fstT (sndT (Syn.shift X)) + var 0 := by
      refine congrAdd ((fst_pair _ _).eqTrans ?_) (.eqRefl _)
      rw [show Syn.shift (g * fstT (sndT X)) = Syn.shift g * fstT (sndT (Syn.shift X)) by simp [Syn.shift]]
      exact .eqRefl _
    exact (congrInst2 (tB wb) e1 (snd_pair _ _)).eqTrans t
  refine (congrAp2 (sumF (offB (tB wb))) el (.eqRefl _)).eqTrans (inner.eqTrans ?_)
  exact congrAp2 (sumF (fB (vZ wb))) (fst_pair _ _).eqSymm
    (congrPairT (congrInst2 wbit (.eqRefl g) (snd_pair _ _).eqSymm) (congrPairT (.eqRefl g) (snd_pair _ _).eqSymm))

/-- The next residual count is the sum of the cell residuals: `Σ_{y<rG} w'_y = Σ_{g<G} rs_g`. -/
theorem chain (wb : PTm 2) {p r X : PTm n} (hr : Γ ⊢[PRAAx] r ≐ succ (pred r))
    (er : Γ ⊢[PRAAx] fstT (sndT X) ≐ r) :
    Γ ⊢[PRAAx] ap2 (sumF evB) (succ (pred (r * succ p))) (code (tB wb) (r * succ p) two X) ≐
      ap2 (sumF (rsB wbit (vZ wb))) (succ p) (pairT r X) := by
  have e := natEq hr
  have hN : Γ ⊢[PRAAx] r * succ p ≐ succ (pred (r * succ p)) := by
    refine pos_of_one ?_
    ipra_le 𝔞 (pred r) * 𝔞 p + 𝔞 (pred r) + 𝔞 p with (𝔞 p + 1) * e
  have s1 := congrAp2 (sumF evB) hN.eqSymm (.eqRefl (code (tB wb) (r * succ p) two X))
  have s2 : Γ ⊢[PRAAx] ap2 (sumF evB) (r * succ p) (code (tB wb) (r * succ p) two X) ≐
      ap2 (sumF (tB wb)) (r * succ p) X := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_evB, show Syn.shift (code (tB wb) (r * succ p) two X) =
      code (tB wb) (Syn.shift (r * succ p)) two (Syn.shift X) by simp [Syn.shift]]
    exact ev_curry_of_lt (tB wb) two_pos Prf.hyp0 (tB_lt wb _ _)
  have s3 : Γ ⊢[PRAAx] ap2 (sumF (tB wb)) (r * succ p) X ≐ ap2 (sumF (tB wb)) (inst2 eB (succ p) X) X := by
    refine congrAp2 _ ?_ (.eqRefl _)
    rw [inst2_eB]
    have e' := natEq er
    apply deriveNat; ipra_simps; linear_combination -(𝔞 p + 1) * e'
  have h0 : Γ ⊢[PRAAx] inst2 eB zero X ≐ zero := by
    rw [inst2_eB]; ipra_ring
  have hmono : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ p)) ⟶
      le (inst2 eB (var 0) (Syn.shift X)) (inst2 eB (succ (var 0)) (Syn.shift X))) := by
    refine .allI (.impI ?_)
    rw [inst2_eB, inst2_eB]
    ipra_le 𝔞 (fstT (sndT (Syn.shift X)))
  have s4 := block_sum (tB wb) eB (succ p) X h0 hmono
  have s5 : Γ ⊢[PRAAx] ap2 (sumF (blockB (tB wb) eB)) (succ p) X ≐
      ap2 (sumF (rsB wbit (vZ wb))) (succ p) (pairT r X) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    let ψ0 : Fm PTm (n + 1) := lt (var 0) (Syn.shift (succ p))
    rw [shift_pairT]
    have hr' : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx] Syn.shift r ≐ succ (pred (Syn.shift r)) := by
      simpa [Fm.shift, Syn.shift] using sh ψ0 hr
    have er' : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx] fstT (sndT (Syn.shift X)) ≐ Syn.shift r := by
      simpa [Fm.shift, Syn.shift] using sh ψ0 er
    exact cell_eq wb hr' er'
  exact s1.eqTrans (s2.eqTrans (s3.eqTrans (s4.eqTrans s5)))

/-- The coarse residual count `Σ_g w_g` read from the code. -/
theorem wsum_eq {p r X c : PTm n} (ec : Γ ⊢[PRAAx] fstT X ≐ c) :
    Γ ⊢[PRAAx] ap2 (sumF (wB wbit)) (succ p) (pairT r X) ≐ ap2 (sumF evB) (succ p) c := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  let ψ0 : Fm PTm (n + 1) := lt (var 0) (Syn.shift (succ p))
  rw [inst2_wB, inst2_wbit, inst2_evB, shift_pairT]
  have ec' : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx] fstT (Syn.shift X) ≐ Syn.shift c := by
    simpa [Fm.shift, Syn.shift] using sh ψ0 ec
  exact congrAp2 remF (congrAp2 quoF ((congrFst (snd_pair _ _)).eqTrans ec') (.eqRefl _)) (.eqRefl _)

/-! ## The round -/

/-- One full round of (K2): with the next code `c' = code(tB, rG, 2)` of the residual bits,
`16384 Σ_{y<rG} w'_y ≤ 16383 r Σ_{g<G} w_g`. -/
theorem round_step (Ψ Dm : PTm 2) {p c N C x : PTm n} (hC : Γ ⊢[PRAAx] le one C) (hmono : Γ ⊢[PRAAx] monoF Ψ x)
    (hKD : Γ ⊢[PRAAx] kdF Ψ Dm C x) :
    Γ ⊢[PRAAx] le (succ (num 16383) * ap2 (sumF evB) (succ (pred (rr Dm p N C x * succ p)))
        (code (tB (wbK Ψ)) (rr Dm p N C x * succ p) two (pairT c (xr Dm p N C x))))
      ((num 16383 * rr Dm p N C x) * ap2 (sumF evB) (succ p) c) := by
  have K := k2_round_z (wbK Ψ) wbit (z := c) (hT_r Dm p N C x) (hM_r Dm p N C x)
    (hw_all p (pairT c (xr Dm p N C x)))
    (hcov_all Ψ Dm (p := p) (N := N) hC hmono hKD) (hH_all Ψ Dm (p := p) (N := N) (x := x) hC)
  have er : Γ ⊢[PRAAx] fstT (sndT (pairT c (xr Dm p N C x))) ≐ rr Dm p N C x :=
    (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have ec : Γ ⊢[PRAAx] fstT (pairT c (xr Dm p N C x)) ≐ c := fst_pair _ _
  exact le_congr (congrMul (.eqRefl _) (chain (wbK Ψ) (p := p) (hr_r Dm (p := p) (N := N) hC) er).eqSymm)
    (congrMul (.eqRefl _) (wsum_eq ec)) K

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinK2Step
