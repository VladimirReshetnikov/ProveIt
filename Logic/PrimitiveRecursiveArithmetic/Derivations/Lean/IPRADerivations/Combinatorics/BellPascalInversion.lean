import IPRADerivations.Combinatorics.BellStirling
import IPRADerivations.Combinatorics.CatalanNarayana

/-!
# A Pascal inversion for the Bell numbers

Packet: `combinatorics/bell_numbers_ipra` (`eq:general-pascal-inversion`, a consequence of
`lem:finite-shift`): for all `n, r`,

  `∑_{j ≤ n} C(n, j) B_{r+j} = ∑_{i ≤ r} (−1)^{r−i} C(r, i) B_{n+i+1}`.

The packet obtains it from the umbral functional, `𝓛(X^r (X + 1)^n) = 𝓛(X^{n+1} (X − 1)^r)`. Here
the signed sum is split by the parity of `r − i` into natural numbers `G⁺(n, r)` (even `r − i`)
and `G⁻(n, r)` (odd `r − i`), and the statement is `F(n, r) + G⁻(n, r) = G⁺(n, r)` with `F` the left
side:

* `F_pascal`: `F(n + 1, r) = F(n, r) + F(n, r + 1)`, by Pascal's rule (`X^r (X + 1)^{n+1}`);
* `Gp_pascal`, `Gm_pascal`: `G^±(n, r + 1) = G^∓(n, r) + G^±(n + 1, r)`, by Pascal's rule and the
  parity flip `ev(y + 1) = od(y)`, `od(y + 1) = ev(y)` (`X^{n+1} (X − 1)^{r+1}`);
* `claim_zero`: at `r = 0` both sides are `B_{n+1}`, the Bell recurrence;
* `claim_step`: the two recurrences carry the identity from `(n, r)` and `(n + 1, r)` to
  `(n, r + 1)`;
* `pascal_inversion`: induction on `r` for all `n` at once, as the vanishing of the violation count
  over `n < M − r`.

Its case `n = 0` is Pascal inversion of the Bell recurrence.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellPascalInversion

open_ipra
open LeanProofs.IPRA.Combinatorics.Stirling (gle gle_of_le)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_above gb_pascal)
open LeanProofs.IPRA.Combinatorics.StirlingBinomial (shift_y)
open LeanProofs.IPRA.Combinatorics.CatalanNarayana (le_of_lt_succ)
open LeanProofs.IPRA.Combinatorics.Bell (bell BL bell_succ recB inst2_rec)
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eq_of_viol viol_of_eq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Signs -/

/-- `1` for even `x`, `0` for odd `x`. -/
abbrev ev {n : ℕ} (x : PTm n) : PTm n := monus one (par x)
/-- `1` for odd `x`, `0` for even `x`. -/
abbrev od {n : ℕ} (x : PTm n) : PTm n := par x

theorem congrBell {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] bell a ≐ bell b := congrFst (congrAp1 BL h)
theorem congrOd {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] od a ≐ od b := congrAp1 parF h
theorem congrEv {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] ev a ≐ ev b :=
  congrMonus (.eqRefl _) (congrOd h)

theorem od_succ (y : PTm n) : Γ ⊢[PRAAx] od (succ y) ≐ ev y := par_succ y

theorem ev_succ (y : PTm n) : Γ ⊢[PRAAx] ev (succ y) ≐ od y := by
  refine (congrMonus (.eqRefl _) (par_succ y)).eqTrans ?_
  refine .orE (par_cases y) ?_ ?_
  · have h : ((par y ≐ zero) :: Γ) ⊢[PRAAx] par y ≐ zero := Prf.hyp0
    exact (congrMonus (.eqRefl _) ((congrMonus (.eqRefl _) h).eqTrans (monus_zero _))).eqTrans
      ((monus_self _).eqTrans h.eqSymm)
  · have h : ((par y ≐ one) :: Γ) ⊢[PRAAx] par y ≐ one := Prf.hyp0
    exact (congrMonus (.eqRefl _) ((congrMonus (.eqRefl _) h).eqTrans (monus_self _))).eqTrans
      ((monus_zero _).eqTrans h.eqSymm)

theorem ev_zero : Γ ⊢[PRAAx] ev (zero : PTm n) ≐ one :=
  (congrMonus (.eqRefl _) par_zero).eqTrans (monus_zero _)

theorem shift_succ (a : PTm n) : Syn.shift (succ a) = succ (Syn.shift a) := by simp [Syn.shift]

/-! ## The left side `F(n, r) = ∑_{j ≤ n} C(n, j) B_{r+j}` -/

/-- Over `0 = j`, `1 = ⟨n, r⟩`. -/
abbrev fB : PTm 2 := gb (fstT (var 1)) (var 0) * bell (sndT (var 1) + var 0)
/-- `C(n, j) B_{r+1+j}`. -/
abbrev fB' : PTm 2 := gb (fstT (var 1)) (var 0) * bell (succ (sndT (var 1)) + var 0)

abbrev F {n : ℕ} (N R : PTm n) : PTm n := ap2 (sumF fB) (succ N) (pairT N R)

theorem inst2_fB (j x : PTm n) : inst2 fB j x = gb (fstT x) j * bell (sndT x + j) := by simp [inst2]
theorem inst2_fB' (j x : PTm n) : inst2 fB' j x = gb (fstT x) j * bell (succ (sndT x) + j) := by simp [inst2]

theorem fpt (j N R : PTm n) : Γ ⊢[PRAAx] inst2 fB j (pairT N R) ≐ gb N j * bell (R + j) := by
  rw [inst2_fB]
  exact congrMul (congrGb (fst_pair _ _) (.eqRefl _)) (congrBell (congrAdd (snd_pair _ _) (.eqRefl _)))

theorem fpt' (j N R : PTm n) : Γ ⊢[PRAAx] inst2 fB' j (pairT N R) ≐ gb N j * bell (succ R + j) := by
  rw [inst2_fB']
  exact congrMul (congrGb (fst_pair _ _) (.eqRefl _)) (congrBell (congrAdd (congrSucc (snd_pair _ _)) (.eqRefl _)))

theorem f_head (N R : PTm n) : Γ ⊢[PRAAx] inst2 fB zero (pairT N R) ≐ bell R :=
  (fpt _ _ _).eqTrans ((congrMul (gb_zero N) (congrBell (add_zero R))).eqTrans (one_mul _))

/-- `F(n, r) = B_r + ∑_{j ≤ n} C(n, j + 1) B_{r+j+1}`. -/
theorem F_split (N R : PTm n) :
    Γ ⊢[PRAAx] F N R ≐ bell R + ap2 (sumF (shiftBody fB)) (succ N) (pairT N R) := by
  have ext : Γ ⊢[PRAAx] ap2 (sumF fB) (succ (succ N)) (pairT N R) ≐ F N R := by
    refine (sum_succ' fB (succ N) (pairT N R)).eqTrans ?_
    refine (congrAdd (.eqRefl _) ((fpt _ _ _).eqTrans ?_)).eqTrans (add_zero _)
    exact (congrMul (gb_above (le_refl (succ N))) (.eqRefl _)).eqTrans (zero_mul _)
  exact ext.eqSymm.eqTrans ((sum_shift fB (succ N) (pairT N R)).eqTrans (congrAdd (f_head N R) (.eqRefl _)))

theorem fpas (j N R : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody fB) j (pairT (succ N) R) ≐ inst2 (addBody (shiftBody fB) fB') j (pairT N R) := by
  rw [inst2_shiftBody, inst2_addBody, inst2_shiftBody]
  ipra_lc natEq (fpt (Γ := Γ) (succ j) (succ N) R) - natEq (fpt (Γ := Γ) (succ j) N R) - natEq (fpt' (Γ := Γ) j N R) +
    𝔞(bell (R + succ j)) * natEq (gb_pascal (Γ := Γ) N j) -
    𝔞(gle j N) * 𝔞(binom N j) * natEq (congrBell (Γ := Γ) (by ipra_ring : Γ ⊢[PRAAx] succ R + j ≐ R + succ j))

/-- `F(n + 1, r) = F(n, r) + F(n, r + 1)`. -/
theorem F_pascal (N R : PTm n) : Γ ⊢[PRAAx] F (succ N) R ≐ F N R + F N (succ R) := by
  refine (sum_shift fB (succ N) (pairT (succ N) R)).eqTrans ?_
  have hs : Γ ⊢[PRAAx] ap2 (sumF (shiftBody fB)) (succ N) (pairT (succ N) R) ≐
      ap2 (sumF (addBody (shiftBody fB) fB')) (succ N) (pairT N R) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y, shift_y, shift_succ]
    exact fpas _ _ _
  have hf' : Γ ⊢[PRAAx] ap2 (sumF fB') (succ N) (pairT N R) ≐ F N (succ R) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y, shift_y, shift_succ]
    exact (fpt' _ _ _).eqTrans (fpt _ _ _).eqSymm
  refine (congrAdd (f_head _ _) (hs.eqTrans ((sum_add _ _ _ _).eqTrans (congrAdd (.eqRefl _) hf')))).eqTrans ?_
  exact (add_assoc _ _ _).eqSymm.eqTrans (congrAdd (F_split N R).eqSymm (.eqRefl _))

/-! ## The right side, split by the parity of `r − i` -/

/-- `ev(r − i) C(r, i) B_{n+i+1}`, over `0 = i`, `1 = ⟨n, r⟩`. -/
abbrev gpB : PTm 2 := ev (monus (sndT (var 1)) (var 0)) * gb (sndT (var 1)) (var 0) * bell (succ (fstT (var 1) + var 0))
/-- `od(r − i) C(r, i) B_{n+i+1}`. -/
abbrev gmB : PTm 2 := od (monus (sndT (var 1)) (var 0)) * gb (sndT (var 1)) (var 0) * bell (succ (fstT (var 1) + var 0))

abbrev Gp {n : ℕ} (N R : PTm n) : PTm n := ap2 (sumF gpB) (succ R) (pairT N R)
abbrev Gm {n : ℕ} (N R : PTm n) : PTm n := ap2 (sumF gmB) (succ R) (pairT N R)

theorem inst2_gp (i x : PTm n) :
    inst2 gpB i x = ev (monus (sndT x) i) * gb (sndT x) i * bell (succ (fstT x + i)) := by simp [inst2]
theorem inst2_gm (i x : PTm n) :
    inst2 gmB i x = od (monus (sndT x) i) * gb (sndT x) i * bell (succ (fstT x + i)) := by simp [inst2]

theorem gppt (i N R : PTm n) :
    Γ ⊢[PRAAx] inst2 gpB i (pairT N R) ≐ ev (monus R i) * gb R i * bell (succ (N + i)) := by
  rw [inst2_gp]
  exact congrMul (congrMul (congrEv (congrMonus (snd_pair _ _) (.eqRefl _))) (congrGb (snd_pair _ _) (.eqRefl _)))
    (congrBell (congrSucc (congrAdd (fst_pair _ _) (.eqRefl _))))

theorem gmpt (i N R : PTm n) :
    Γ ⊢[PRAAx] inst2 gmB i (pairT N R) ≐ od (monus R i) * gb R i * bell (succ (N + i)) := by
  rw [inst2_gm]
  exact congrMul (congrMul (congrOd (congrMonus (snd_pair _ _) (.eqRefl _))) (congrGb (snd_pair _ _) (.eqRefl _)))
    (congrBell (congrSucc (congrAdd (fst_pair _ _) (.eqRefl _))))

/-- `w(r − i) C(r, i + 1) B_{n+i+2}` and `w(r − i) C(r, i) B_{n+i+2}`, for `w = ev, od`. -/
abbrev hpB : PTm 2 := ev (monus (sndT (var 1)) (var 0)) * gb (sndT (var 1)) (succ (var 0)) *
  bell (succ (fstT (var 1) + succ (var 0)))
abbrev kpB : PTm 2 := ev (monus (sndT (var 1)) (var 0)) * gb (sndT (var 1)) (var 0) *
  bell (succ (succ (fstT (var 1)) + var 0))
abbrev hmB : PTm 2 := od (monus (sndT (var 1)) (var 0)) * gb (sndT (var 1)) (succ (var 0)) *
  bell (succ (fstT (var 1) + succ (var 0)))
abbrev kmB : PTm 2 := od (monus (sndT (var 1)) (var 0)) * gb (sndT (var 1)) (var 0) *
  bell (succ (succ (fstT (var 1)) + var 0))

theorem inst2_hp (i x : PTm n) : inst2 hpB i x =
    ev (monus (sndT x) i) * gb (sndT x) (succ i) * bell (succ (fstT x + succ i)) := by simp [inst2]
theorem inst2_kp (i x : PTm n) : inst2 kpB i x =
    ev (monus (sndT x) i) * gb (sndT x) i * bell (succ (succ (fstT x) + i)) := by simp [inst2]
theorem inst2_hm (i x : PTm n) : inst2 hmB i x =
    od (monus (sndT x) i) * gb (sndT x) (succ i) * bell (succ (fstT x + succ i)) := by simp [inst2]
theorem inst2_km (i x : PTm n) : inst2 kmB i x =
    od (monus (sndT x) i) * gb (sndT x) i * bell (succ (succ (fstT x) + i)) := by simp [inst2]

theorem gpas_p (j N R : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody gpB) j (pairT N (succ R)) ≐ inst2 (addBody hpB kpB) j (pairT N R) := by
  rw [inst2_shiftBody, inst2_addBody, inst2_hp, inst2_kp]
  ipra_lc natEq ((gppt (Γ := Γ) (succ j) N (succ R)).eqTrans (congrMul (congrMul (congrEv (succ_monus_succ R j)) (.eqRefl (gb (succ R) (succ j)))) (.eqRefl (bell (succ (N + succ j)))))) -
    natEq (congrMul (congrMul (congrEv (congrMonus (snd_pair (Γ := Γ) N R) (.eqRefl j))) (congrGb (snd_pair (Γ := Γ) N R) (.eqRefl (succ j)))) (congrBell (congrSucc (congrAdd (fst_pair (Γ := Γ) N R) (.eqRefl (succ j)))))) -
    natEq (congrMul (congrMul (congrEv (congrMonus (snd_pair (Γ := Γ) N R) (.eqRefl j))) (congrGb (snd_pair (Γ := Γ) N R) (.eqRefl j))) (congrBell (congrSucc (congrAdd (congrSucc (fst_pair (Γ := Γ) N R)) (.eqRefl j))))) +
    𝔞(ev (monus R j)) * 𝔞(bell (succ (N + succ j))) * natEq (gb_pascal (Γ := Γ) R j) -
    𝔞(ev (monus R j)) * 𝔞(gle j R) * 𝔞(binom R j) * natEq (congrBell (Γ := Γ) (by ipra_ring : Γ ⊢[PRAAx] succ (succ N + j) ≐ succ (N + succ j)))

theorem gpas_m (j N R : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody gmB) j (pairT N (succ R)) ≐ inst2 (addBody hmB kmB) j (pairT N R) := by
  rw [inst2_shiftBody, inst2_addBody, inst2_hm, inst2_km]
  ipra_lc natEq ((gmpt (Γ := Γ) (succ j) N (succ R)).eqTrans (congrMul (congrMul (congrOd (succ_monus_succ R j)) (.eqRefl (gb (succ R) (succ j)))) (.eqRefl (bell (succ (N + succ j)))))) -
    natEq (congrMul (congrMul (congrOd (congrMonus (snd_pair (Γ := Γ) N R) (.eqRefl j))) (congrGb (snd_pair (Γ := Γ) N R) (.eqRefl (succ j)))) (congrBell (congrSucc (congrAdd (fst_pair (Γ := Γ) N R) (.eqRefl (succ j)))))) -
    natEq (congrMul (congrMul (congrOd (congrMonus (snd_pair (Γ := Γ) N R) (.eqRefl j))) (congrGb (snd_pair (Γ := Γ) N R) (.eqRefl j))) (congrBell (congrSucc (congrAdd (congrSucc (fst_pair (Γ := Γ) N R)) (.eqRefl j))))) +
    𝔞(od (monus R j)) * 𝔞(bell (succ (N + succ j))) * natEq (gb_pascal (Γ := Γ) R j) -
    𝔞(od (monus R j)) * 𝔞(gle j R) * 𝔞(binom R j) * natEq (congrBell (Γ := Γ) (by ipra_ring : Γ ⊢[PRAAx] succ (succ N + j) ≐ succ (N + succ j)))

/-- `ev(r − i) C(r, i + 1) = od(r − i − 1) C(r, i + 1)`, for every `i`. -/
theorem hp_pt (j N R : PTm n) :
    Γ ⊢[PRAAx] inst2 hpB j (pairT N R) ≐ inst2 (shiftBody gmB) j (pairT N R) := by
  rw [inst2_hp, inst2_shiftBody]
  refine .eqTrans ?_ (gmpt _ _ _).eqSymm
  have c₁ : Γ ⊢[PRAAx] ev (monus (sndT (pairT N R)) j) * gb (sndT (pairT N R)) (succ j) ≐ ev (monus R j) * gb R (succ j) :=
    congrMul (congrEv (congrMonus (snd_pair N R) (.eqRefl j))) (congrGb (snd_pair N R) (.eqRefl (succ j)))
  refine congrMul (c₁.eqTrans ?_) (congrBell (congrSucc (congrAdd (fst_pair N R) (.eqRefl (succ j)))))
  · refine .orE (lt_or_le j R) ?_ ?_
    · have hl : (lt j R :: Γ) ⊢[PRAAx] lt j R := Prf.hyp0
      have e₀ : (lt j R :: Γ) ⊢[PRAAx] R ≐ succ (monus R (succ j)) + j := by
        ipra_lc natEq (eq_add_of_le hl)
      have e : (lt j R :: Γ) ⊢[PRAAx] monus R j ≐ succ (monus R (succ j)) :=
        (congrMonus e₀ (.eqRefl _)).eqTrans (add_monus _ _)
      exact congrMul ((congrEv e).eqTrans (ev_succ _)) (.eqRefl _)
    · have z : (le R j :: Γ) ⊢[PRAAx] gb R (succ j) ≐ zero := gb_above ((succ_monus_succ _ _).eqTrans Prf.hyp0)
      exact ((congrMul (.eqRefl _) z).eqTrans (mul_zero _)).eqTrans ((congrMul (.eqRefl _) z).eqTrans (mul_zero _)).eqSymm

/-- `od(r − i) C(r, i + 1) = ev(r − i − 1) C(r, i + 1)`, for every `i`. -/
theorem hm_pt (j N R : PTm n) :
    Γ ⊢[PRAAx] inst2 hmB j (pairT N R) ≐ inst2 (shiftBody gpB) j (pairT N R) := by
  rw [inst2_hm, inst2_shiftBody]
  refine .eqTrans ?_ (gppt _ _ _).eqSymm
  have c₁ : Γ ⊢[PRAAx] od (monus (sndT (pairT N R)) j) * gb (sndT (pairT N R)) (succ j) ≐ od (monus R j) * gb R (succ j) :=
    congrMul (congrOd (congrMonus (snd_pair N R) (.eqRefl j))) (congrGb (snd_pair N R) (.eqRefl (succ j)))
  refine congrMul (c₁.eqTrans ?_) (congrBell (congrSucc (congrAdd (fst_pair N R) (.eqRefl (succ j)))))
  · refine .orE (lt_or_le j R) ?_ ?_
    · have hl : (lt j R :: Γ) ⊢[PRAAx] lt j R := Prf.hyp0
      have e₀ : (lt j R :: Γ) ⊢[PRAAx] R ≐ succ (monus R (succ j)) + j := by
        ipra_lc natEq (eq_add_of_le hl)
      have e : (lt j R :: Γ) ⊢[PRAAx] monus R j ≐ succ (monus R (succ j)) :=
        (congrMonus e₀ (.eqRefl _)).eqTrans (add_monus _ _)
      exact congrMul ((congrOd e).eqTrans (od_succ _)) (.eqRefl _)
    · have z : (le R j :: Γ) ⊢[PRAAx] gb R (succ j) ≐ zero := gb_above ((succ_monus_succ _ _).eqTrans Prf.hyp0)
      exact ((congrMul (.eqRefl _) z).eqTrans (mul_zero _)).eqTrans ((congrMul (.eqRefl _) z).eqTrans (mul_zero _)).eqSymm

theorem kp_pt (j N R : PTm n) : Γ ⊢[PRAAx] inst2 kpB j (pairT N R) ≐ inst2 gpB j (pairT (succ N) R) := by
  rw [inst2_kp]
  refine .eqTrans ?_ (gppt _ _ _).eqSymm
  exact congrMul (congrMul (congrEv (congrMonus (snd_pair _ _) (.eqRefl _))) (congrGb (snd_pair _ _) (.eqRefl _)))
    (congrBell (congrSucc (congrAdd (congrSucc (fst_pair _ _)) (.eqRefl _))))

theorem km_pt (j N R : PTm n) : Γ ⊢[PRAAx] inst2 kmB j (pairT N R) ≐ inst2 gmB j (pairT (succ N) R) := by
  rw [inst2_km]
  refine .eqTrans ?_ (gmpt _ _ _).eqSymm
  exact congrMul (congrMul (congrOd (congrMonus (snd_pair _ _) (.eqRefl _))) (congrGb (snd_pair _ _) (.eqRefl _)))
    (congrBell (congrSucc (congrAdd (congrSucc (fst_pair _ _)) (.eqRefl _))))

/-- `G^±(n, r) = w(r) B_{n+1} + ∑_{i ≤ r} w(r − i − 1) C(r, i + 1) B_{n+i+2}`. -/
theorem Gm_split (N R : PTm n) :
    Γ ⊢[PRAAx] Gm N R ≐ od R * bell (succ N) + ap2 (sumF (shiftBody gmB)) (succ R) (pairT N R) := by
  have ext : Γ ⊢[PRAAx] ap2 (sumF gmB) (succ (succ R)) (pairT N R) ≐ Gm N R := by
    refine (sum_succ' gmB (succ R) (pairT N R)).eqTrans ?_
    refine (congrAdd (.eqRefl _) ((gmpt _ _ _).eqTrans ?_)).eqTrans (add_zero _)
    exact (congrMul ((congrMul (.eqRefl _) (gb_above (le_refl (succ R)))).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans
      (zero_mul _)
  have h0 : Γ ⊢[PRAAx] inst2 gmB zero (pairT N R) ≐ od R * bell (succ N) :=
    (gmpt _ _ _).eqTrans (congrMul ((congrMul (congrOd (monus_zero R)) (gb_zero R)).eqTrans ((mul_comm _ _).eqTrans (one_mul _)))
      (congrBell (congrSucc (add_zero N))))
  exact ext.eqSymm.eqTrans ((sum_shift gmB (succ R) (pairT N R)).eqTrans (congrAdd h0 (.eqRefl _)))

theorem Gp_split (N R : PTm n) :
    Γ ⊢[PRAAx] Gp N R ≐ ev R * bell (succ N) + ap2 (sumF (shiftBody gpB)) (succ R) (pairT N R) := by
  have ext : Γ ⊢[PRAAx] ap2 (sumF gpB) (succ (succ R)) (pairT N R) ≐ Gp N R := by
    refine (sum_succ' gpB (succ R) (pairT N R)).eqTrans ?_
    refine (congrAdd (.eqRefl _) ((gppt _ _ _).eqTrans ?_)).eqTrans (add_zero _)
    exact (congrMul ((congrMul (.eqRefl _) (gb_above (le_refl (succ R)))).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans
      (zero_mul _)
  have h0 : Γ ⊢[PRAAx] inst2 gpB zero (pairT N R) ≐ ev R * bell (succ N) :=
    (gppt _ _ _).eqTrans (congrMul ((congrMul (congrEv (monus_zero R)) (gb_zero R)).eqTrans ((mul_comm _ _).eqTrans (one_mul _)))
      (congrBell (congrSucc (add_zero N))))
  exact ext.eqSymm.eqTrans ((sum_shift gpB (succ R) (pairT N R)).eqTrans (congrAdd h0 (.eqRefl _)))

/-- `G⁺(n, r + 1) = G⁻(n, r) + G⁺(n + 1, r)`. -/
theorem Gp_pascal (N R : PTm n) : Γ ⊢[PRAAx] Gp N (succ R) ≐ Gm N R + Gp (succ N) R := by
  refine (sum_shift gpB (succ R) (pairT N (succ R))).eqTrans ?_
  have h0 : Γ ⊢[PRAAx] inst2 gpB zero (pairT N (succ R)) ≐ od R * bell (succ N) :=
    (gppt _ _ _).eqTrans (congrMul ((congrMul ((congrEv (monus_zero _)).eqTrans (ev_succ R)) (gb_zero _)).eqTrans
      ((mul_comm _ _).eqTrans (one_mul _))) (congrBell (congrSucc (add_zero N))))
  have hs : Γ ⊢[PRAAx] ap2 (sumF (shiftBody gpB)) (succ R) (pairT N (succ R)) ≐
      ap2 (sumF (addBody hpB kpB)) (succ R) (pairT N R) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y, shift_y, shift_succ]
    exact gpas_p _ _ _
  have hh : Γ ⊢[PRAAx] ap2 (sumF hpB) (succ R) (pairT N R) ≐ ap2 (sumF (shiftBody gmB)) (succ R) (pairT N R) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y]
    exact hp_pt _ _ _
  have hk : Γ ⊢[PRAAx] ap2 (sumF kpB) (succ R) (pairT N R) ≐ Gp (succ N) R := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y, shift_y, shift_succ]
    exact kp_pt _ _ _
  refine (congrAdd h0 (hs.eqTrans ((sum_add _ _ _ _).eqTrans (congrAdd hh hk)))).eqTrans ?_
  exact (add_assoc _ _ _).eqSymm.eqTrans (congrAdd (Gm_split N R).eqSymm (.eqRefl _))

/-- `G⁻(n, r + 1) = G⁺(n, r) + G⁻(n + 1, r)`. -/
theorem Gm_pascal (N R : PTm n) : Γ ⊢[PRAAx] Gm N (succ R) ≐ Gp N R + Gm (succ N) R := by
  refine (sum_shift gmB (succ R) (pairT N (succ R))).eqTrans ?_
  have h0 : Γ ⊢[PRAAx] inst2 gmB zero (pairT N (succ R)) ≐ ev R * bell (succ N) :=
    (gmpt _ _ _).eqTrans (congrMul ((congrMul ((congrOd (monus_zero _)).eqTrans (od_succ R)) (gb_zero _)).eqTrans
      ((mul_comm _ _).eqTrans (one_mul _))) (congrBell (congrSucc (add_zero N))))
  have hs : Γ ⊢[PRAAx] ap2 (sumF (shiftBody gmB)) (succ R) (pairT N (succ R)) ≐
      ap2 (sumF (addBody hmB kmB)) (succ R) (pairT N R) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y, shift_y, shift_succ]
    exact gpas_m _ _ _
  have hh : Γ ⊢[PRAAx] ap2 (sumF hmB) (succ R) (pairT N R) ≐ ap2 (sumF (shiftBody gpB)) (succ R) (pairT N R) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y]
    exact hm_pt _ _ _
  have hk : Γ ⊢[PRAAx] ap2 (sumF kmB) (succ R) (pairT N R) ≐ Gm (succ N) R := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y, shift_y, shift_succ]
    exact km_pt _ _ _
  refine (congrAdd h0 (hs.eqTrans ((sum_add _ _ _ _).eqTrans (congrAdd hh hk)))).eqTrans ?_
  exact (add_assoc _ _ _).eqSymm.eqTrans (congrAdd (Gp_split N R).eqSymm (.eqRefl _))

/-! ## The induction -/

/-- `r = 0`: `F(n, 0) = B_{n+1} = G⁺(n, 0)`, `G⁻(n, 0) = 0`. -/
theorem claim_zero (N : PTm n) : Γ ⊢[PRAAx] F N zero + Gm N zero ≐ Gp N zero := by
  have hF : Γ ⊢[PRAAx] F N zero ≐ bell (succ N) := by
    refine .eqTrans ?_ (bell_succ N).eqSymm
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    have ez : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
    rw [shift_y, inst2_rec, shift_succ, ez]
    have hk := le_of_lt_succ (Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift) (φ := lt (var 0) (succ (Syn.shift N))))
    exact (fpt _ _ _).eqTrans (congrMul ((congrMul (gle_of_le hk) (.eqRefl _)).eqTrans (one_mul _))
      (congrBell (zero_add _)))
  have m0 : Γ ⊢[PRAAx] monus (zero : PTm n) zero ≐ zero := monus_zero _
  have hP : Γ ⊢[PRAAx] Gp N zero ≐ bell (succ N) := by
    refine ((sum_singleton gpB (pairT N zero)).eqTrans (gppt _ _ _)).eqTrans ?_
    exact (congrMul ((congrMul ((congrEv m0).eqTrans ev_zero) (gb_zero _)).eqTrans (one_mul _))
      (congrBell (congrSucc (add_zero N)))).eqTrans (one_mul _)
  have hM : Γ ⊢[PRAAx] Gm N zero ≐ zero := by
    refine ((sum_singleton gmB (pairT N zero)).eqTrans (gmpt _ _ _)).eqTrans ?_
    exact (congrMul ((congrMul ((congrOd m0).eqTrans par_zero) (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans
      (zero_mul _)
  exact (congrAdd hF hM).eqTrans ((add_zero _).eqTrans hP.eqSymm)

/-- `(n, r)` and `(n + 1, r)` give `(n, r + 1)`. -/
theorem claim_step {N R : PTm n} (h₀ : Γ ⊢[PRAAx] F N R + Gm N R ≐ Gp N R)
    (h₁ : Γ ⊢[PRAAx] F (succ N) R + Gm (succ N) R ≐ Gp (succ N) R) :
    Γ ⊢[PRAAx] F N (succ R) + Gm N (succ R) ≐ Gp N (succ R) := by
  ipra_lc natEq (Gm_pascal (Γ := Γ) N R) - natEq (Gp_pascal (Γ := Γ) N R) - natEq (F_pascal (Γ := Γ) N R) + natEq h₁ -
    natEq h₀

/-- At level `r`, the sum over indices below `M − r`. -/
abbrev zeroWindowSum (body : PTm 2) (M r : PTm n) : PTm n :=
  ap2 (sumF body) (monus M r) r

/-- A pointwise successor proof makes the smaller window sum zero. -/
theorem zero_window_step (body : PTm 2) {M R : PTm n}
    (ih : Γ ⊢[PRAAx] zeroWindowSum body M R ≐ zero)
    (step : lt (var 0) (monus (Syn.shift M) (succ (Syn.shift R))) :: Γ.map Fm.shift ⊢[PRAAx]
      (zeroWindowSum body (Syn.shift M) (Syn.shift R) ≐ zero) ⟶
        (inst2 body (var 0) (succ (Syn.shift R)) ≐ zero)) :
    Γ ⊢[PRAAx] zeroWindowSum body M (succ R) ≐ zero := by
  refine sum_zero_of_bounded body _ _ (.allI (.impI ?_))
  have shifted : Γ.map Fm.shift ⊢[PRAAx] zeroWindowSum body (Syn.shift M) (Syn.shift R) ≐ zero := by
    simpa [Fm.shift, Syn.shift, zeroWindowSum] using ih.shift
  simpa [Syn.shift] using Prf.impE step shifted.wk

/-- Induction on the level and a window of size `N + R + 1` give the entry at `(N, R)`. -/
theorem zero_window_entry (body : PTm 2) (N R : PTm n)
    (base : ([] : List (Fm PTm 1)) ⊢[PRAAx] zeroWindowSum body (var 0) zero ≐ zero)
    (step : [zeroWindowSum body (var 1 : PTm 2) (var 0) ≐ zero] ⊢[PRAAx]
      zeroWindowSum body (var 1) (succ (var 0)) ≐ zero) :
    Γ ⊢[PRAAx] inst2 body N R ≐ zero := by
  have all : ([] : List (Fm PTm 2)) ⊢[PRAAx] zeroWindowSum body (var 1) (var 0) ≐ zero := by
    ipra_ind [zeroWindowSum, subst_ap2]
    · exact base
    · exact step
  have h : Γ ⊢[PRAAx] zeroWindowSum body (succ (N + R)) R ≐ zero := by
    simpa [zeroWindowSum] using inst (Γ := Γ) all (![R, succ (N + R)] : Fin 2 → PTm n)
  have size : Γ ⊢[PRAAx] monus (succ (N + R)) R ≐ succ N :=
    (congrMonus (by ipra_ring : Γ ⊢[PRAAx] succ (N + R) ≐ succ N + R) (.eqRefl _)).eqTrans (add_monus _ _)
  exact sum_zero_elim body h (le_congr (.eqRefl _) size.eqSymm (le_refl (succ N)))

/-- `1 ∸ [F(n, r) + G⁻(n, r) = G⁺(n, r)]`, over `0 = n`, `1 = r`. -/
abbrev vB : PTm 2 := monus one (eqb (F (var 0) (var 1) + Gm (var 0) (var 1)) (Gp (var 0) (var 1)))

theorem inst2_v (N R : PTm n) : inst2 vB N R = monus one (eqb (F N R + Gm N R) (Gp N R)) := by simp [inst2]

theorem psi_base (M : PTm n) : Γ ⊢[PRAAx] ap2 (sumF vB) (monus M zero) zero ≐ zero := by
  refine sum_zero_of_all vB zero (.allI ?_) _
  simpa only [Syn.shift, ConciseIPRA.PTm.subst_zero, inst2_v] using
    viol_of_eq (claim_zero (Γ := Γ.map Fm.shift) (var 0))

/-- `j < M − (r + 1)` gives `j + 1 < M − r`. -/
theorem lt_shift {j M R : PTm n} (h : Γ ⊢[PRAAx] lt j (monus M (succ R))) : Γ ⊢[PRAAx] lt (succ j) (monus M R) := by
  refine .orE (lt_or_le R M) ?_ ?_
  · exact le_congr (.eqRefl _) (Common.monus_succ_of_lt Prf.hyp0).eqSymm
      ((succ_monus_succ _ _).eqTrans h.wk)
  · exact lt_zero_absurd _ (lt_congr (.eqRefl _) (le_trans Prf.hyp0 (le_succ_self R)) h.wk)

theorem step_pt {M R j : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF vB) (monus M R) R ≐ zero)
    (hj : Γ ⊢[PRAAx] lt j (monus M (succ R))) :
    Γ ⊢[PRAAx] monus one (eqb (F j (succ R) + Gm j (succ R)) (Gp j (succ R))) ≐ zero := by
  have h₁ := lt_shift hj
  have h₀ : Γ ⊢[PRAAx] lt j (monus M R) := le_trans (le_succ_self (succ j)) h₁
  have v₀ := sum_zero_elim vB ih h₀; have v₁ := sum_zero_elim vB ih h₁
  rw [inst2_v] at v₀ v₁
  exact viol_of_eq (claim_step (eq_of_viol v₀) (eq_of_viol v₁))

theorem psi_step {M R : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF vB) (monus M R) R ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF vB) (monus M (succ R)) (succ R) ≐ zero := by
  refine zero_window_step vB ih (.impI ?_)
  rw [inst2_v]
  exact step_pt Prf.hyp0 Prf.hyp1

/-- `eq:general-pascal-inversion`: `∑_{j ≤ n} C(n, j) B_{r+j} + ∑_{r − i odd} C(r, i) B_{n+i+1}
= ∑_{r − i even} C(r, i) B_{n+i+1}`. -/
theorem pascal_inversion (N R : PTm n) : Γ ⊢[PRAAx] F N R + Gm N R ≐ Gp N R := by
  have v := zero_window_entry (Γ := Γ) vB N R (psi_base _) (psi_step Prf.hyp0)
  rw [inst2_v] at v
  exact eq_of_viol v

end LeanProofs.IPRA.Combinatorics.BellPascalInversion
