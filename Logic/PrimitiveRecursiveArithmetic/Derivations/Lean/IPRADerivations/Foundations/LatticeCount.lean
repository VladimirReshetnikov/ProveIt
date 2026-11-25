import IPRADerivations.Foundations.IntervalCover
import IPRADerivations.Core.Gcd
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# Counting integers in intervals

Framework (packet `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: "An open
interval of length `t` contains between `t − 1` and `t + 1` integers", used for (K5)):

* `exact_count`: `Σ_{c<T} [lo ≤ c < hi] = hi ∸ lo` for `hi ≤ T`;
* `monus_succ_split`: `(T ∸ lo) + [lo ≤ T] = (T + 1) ∸ lo`.

The body reads its endpoints from the pair parameter `⟨lo, hi⟩`.
-/

namespace LeanProofs.IPRA.Foundations.LatticeCount

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Foundations.IntervalCover (cnt)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `[lo ≤ c < hi]` in `(c, ⟨lo, hi⟩)`. -/
abbrev icB : PTm 2 := cnt (fstT (var 1)) (sndT (var 1)) (var 0)

/-- `Σ_{c<T} [lo ≤ c < hi]`. -/
abbrev icS (T lo hi : PTm n) : PTm n := ap2 (sumF icB) T (pairT lo hi)

theorem icS_succ (T lo hi : PTm n) : Γ ⊢[PRAAx] icS (succ T) lo hi ≐ icS T lo hi + cnt lo hi T := by
  refine (sum_succ' icB T (pairT lo hi)).eqTrans (congrAdd (.eqRefl _) ?_)
  have e : inst2 icB T (pairT lo hi) = cnt (fstT (pairT lo hi)) (sndT (pairT lo hi)) T := by simp [inst2, Signum.sg]
  rw [e]
  exact congrMul (congrMonus (.eqRefl _) (congrMonus (fst_pair _ _) (.eqRefl _)))
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrMonus (snd_pair _ _) (.eqRefl _))))

/-- `(T ∸ lo) + [lo ≤ T] = (T + 1) ∸ lo`. -/
theorem monus_succ_split (T lo : PTm n) :
    Γ ⊢[PRAAx] monus T lo + monus one (monus lo T) ≐ monus (succ T) lo := by
  refine .orE (lt_or_le T lo) ?_ ?_
  · -- `T < lo`: both sides `0`
    let Δ : List (Fm PTm n) := lt T lo :: Γ
    have h0 : Δ ⊢[PRAAx] monus T lo ≐ zero := le_of_lt Prf.hyp0
    have e := eq_add_of_le (Γ := Δ) Prf.hyp0
    have hm : Δ ⊢[PRAAx] monus lo T ≐ succ (monus lo (succ T)) := by
      refine (congrMonus (?_ : _ ⊢[PRAAx] lo ≐ T + succ (monus lo (succ T))) (.eqRefl _)).eqTrans (add_monus' _ _)
      have a := natEq e
      apply deriveNat; ipra_simps; linear_combination a
    have h1 : Δ ⊢[PRAAx] monus one (monus lo T) ≐ zero :=
      (congrMonus (.eqRefl _) hm).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))
    exact (congrAdd h0 h1).eqTrans ((add_zero _).eqTrans (Prf.hyp0 : Δ ⊢[PRAAx] lt T lo).eqSymm)
  · -- `lo ≤ T`: `(T ∸ lo) + 1`
    let Δ : List (Fm PTm n) := le lo T :: Γ
    have h1 : Δ ⊢[PRAAx] monus one (monus lo T) ≐ one := (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)
    have hT := eq_add_of_le (Γ := Δ) Prf.hyp0
    have e : Δ ⊢[PRAAx] monus (succ T) lo ≐ succ (monus T lo) := by
      refine (congrMonus (?_ : _ ⊢[PRAAx] succ T ≐ lo + succ (monus T lo)) (.eqRefl _)).eqTrans (add_monus' _ _)
      have a := natEq hT
      apply deriveNat; ipra_simps; linear_combination a
    exact (congrAdd (.eqRefl _) h1).eqTrans ((succ_eq_add_one _).eqSymm.eqTrans e.eqSymm)

/-- The invariant of `exact_count`. -/
def exactInv (T lo hi : PTm n) : Fm PTm n :=
  (le T hi ⟶ (icS T lo hi ≐ monus T lo)) ⋏ (le hi T ⟶ (icS T lo hi ≐ monus hi lo))

@[simp] theorem subst_exactInv {k : ℕ} (σ : Fin n → PTm k) (T lo hi : PTm n) :
    (exactInv T lo hi).subst σ = exactInv (Syn.subst σ T) (Syn.subst σ lo) (Syn.subst σ hi) := by
  simp [exactInv, subst_ap2]

theorem exact_step {T lo hi : PTm n} (ih : Γ ⊢[PRAAx] exactInv T lo hi) :
    Γ ⊢[PRAAx] exactInv (succ T) lo hi := by
  have es := icS_succ (Γ := Γ) T lo hi
  refine .orE (lt_or_le T hi) ?_ ?_
  · -- `T < hi`: `cnt = [lo ≤ T]`
    let Δ : List (Fm PTm n) := lt T hi :: Γ
    have hT : Δ ⊢[PRAAx] icS T lo hi ≐ monus T lo := Prf.impE (Prf.andE₁ ih.wk) (le_of_lt Prf.hyp0)
    have e3 := eq_add_of_le (Γ := Δ) Prf.hyp0
    have hs : Δ ⊢[PRAAx] sg (monus hi T) ≐ one := by
      have hm : Δ ⊢[PRAAx] monus hi T ≐ succ (monus hi (succ T)) := by
        refine (congrMonus (?_ : _ ⊢[PRAAx] hi ≐ T + succ (monus hi (succ T))) (.eqRefl _)).eqTrans (add_monus' _ _)
        ipra_lc natEq e3
      exact (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hm)).eqTrans (sg_succ _)
    have hc : Δ ⊢[PRAAx] cnt lo hi T ≐ monus one (monus lo T) :=
      (congrMul (.eqRefl _) hs).eqTrans ((mul_comm _ _).eqTrans (one_mul _))
    have hnext : Δ ⊢[PRAAx] icS (succ T) lo hi ≐ monus (succ T) lo :=
      es.wk.eqTrans ((congrAdd hT hc).eqTrans (monus_succ_split T lo))
    refine .andI (.impI hnext.wk) (.impI ?_)
    -- `hi ≤ T + 1` with `T < hi`: `hi = T + 1`
    have hh : (le hi (succ T) :: Δ) ⊢[PRAAx] succ T ≐ hi := le_antisymm Prf.hyp1 Prf.hyp0
    exact hnext.wk.eqTrans (congrMonus hh (.eqRefl _))
  · -- `hi ≤ T`: `cnt = 0`
    let Δ : List (Fm PTm n) := le hi T :: Γ
    have hT : Δ ⊢[PRAAx] icS T lo hi ≐ monus hi lo := Prf.impE (Prf.andE₂ ih.wk) Prf.hyp0
    have hc : Δ ⊢[PRAAx] cnt lo hi T ≐ zero :=
      (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans sg_zero)).eqTrans
        (mul_zero _)
    have hnext : Δ ⊢[PRAAx] icS (succ T) lo hi ≐ monus hi lo :=
      es.wk.eqTrans ((congrAdd hT hc).eqTrans (add_zero _))
    refine .andI (.impI ?_) (.impI hnext.wk)
    exact .botE _ (not_succ_le_self _ _ (le_trans Prf.hyp0 (Prf.hyp1 : (le (succ T) hi :: Δ) ⊢[PRAAx] le hi T)))

/-- `Σ_{c<T} [lo ≤ c < hi] = hi ∸ lo` for `hi ≤ T`. -/
theorem exact_count (T lo hi : PTm n) (h : Γ ⊢[PRAAx] le hi T) : Γ ⊢[PRAAx] icS T lo hi ≐ monus hi lo := by
  have hall : Γ ⊢[PRAAx] Fm.all (exactInv (var 0) (Syn.shift lo) (Syn.shift hi)) := by
    refine PRA.qfInd _ ⟨⟨le_QF _ _, trivial⟩, ⟨le_QF _ _, trivial⟩⟩ ?_ ?_
    · rw [subst_exactInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      refine .andI (.impI ?_) (.impI ?_)
      · exact (sum_zero _ _).eqTrans (zero_monus _).eqSymm
      · -- `hi ≤ 0`, so `hi = 0`
        have h0 : ((le hi zero) :: Γ) ⊢[PRAAx] hi ≐ zero := le_antisymm Prf.hyp0 (zero_le _)
        exact (sum_zero _ _).eqTrans ((zero_monus _).eqSymm.eqTrans (congrMonus h0.eqSymm (.eqRefl _)))
    · rw [subst_exactInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact exact_step Prf.hyp0
  have a := Prf.allE T hall
  rw [subst_exactInv] at a
  simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at a
  exact Prf.impE (Prf.andE₂ a) h

/-! ## Integers in a dilated interval -/

section Dilated

variable {u v β b0 p : PTm n}

/-- `[u < pβ] = [⌊u/β⌋ + 1 ≤ p]` for `β = b0 + 1`. -/
theorem floor_ind (hβ : Γ ⊢[PRAAx] β ≐ succ b0) :
    Γ ⊢[PRAAx] sg (monus (p * β) u) ≐ monus one (monus (succ (quo u β)) p) := by
  have d := div_mod_at (Γ := Γ) (x := u) hβ
  refine .orE (lt_or_le (quo u β) p) ?_ ?_
  · -- `⌊u/β⌋ < p`: both `1`
    let Δ : List (Fm PTm n) := lt (quo u β) p :: Γ
    have ep := natEq (eq_add_of_le (Γ := Δ) Prf.hyp0)
    have hm : Δ ⊢[PRAAx] monus (p * β) u ≐
        succ (monus β (succ (rem u β)) + β * monus p (succ (quo u β))) := by
      refine (congrMonus (?_ : _ ⊢[PRAAx] p * β ≐ u + succ (monus β (succ (rem u β)) + β * monus p (succ (quo u β))))
        (.eqRefl _)).eqTrans (add_monus' _ _)
      have eu' := natEq (Γ := Δ) (Prf.andE₁ d).wk
      have er' := natEq (Γ := Δ) (eq_add_of_le (Prf.andE₂ d)).wk
      apply deriveNat; ipra_simps
      linear_combination er' - eu' + 𝔞 β * ep
    have h0 : Δ ⊢[PRAAx] monus (succ (quo u β)) p ≐ zero := Prf.hyp0
    exact ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hm)).eqTrans (sg_succ _)).eqTrans
      ((congrMonus (.eqRefl _) h0).eqTrans (monus_zero _)).eqSymm
  · -- `p ≤ ⌊u/β⌋`: both `0`
    let Δ : List (Fm PTm n) := le p (quo u β) :: Γ
    have ep := natEq (eq_add_of_le (Γ := Δ) Prf.hyp0)
    have hm : Δ ⊢[PRAAx] monus (p * β) u ≐ zero := by
      refine le_of_eq_add (d := β * monus (quo u β) p + rem u β) ?_
      have eu' := natEq (Γ := Δ) (Prf.andE₁ d).wk
      apply deriveNat; ipra_simps
      rw [eu', ep]; ring
    have hs : Δ ⊢[PRAAx] monus (succ (quo u β)) p ≐ succ (monus (quo u β) p) := by
      refine (congrMonus (?_ : _ ⊢[PRAAx] succ (quo u β) ≐ p + succ (monus (quo u β) p)) (.eqRefl _)).eqTrans
        (add_monus' _ _)
      ipra_lc ep
    exact ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hm)).eqTrans sg_zero).eqTrans
      ((congrMonus (.eqRefl _) hs).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))).eqSymm

/-- `[pβ < v] = [p < ⌈v/β⌉]`, `⌈v/β⌉ = ⌊(v + b0)/β⌋` for `β = b0 + 1`. -/
theorem ceil_ind (hβ : Γ ⊢[PRAAx] β ≐ succ b0) :
    Γ ⊢[PRAAx] sg (monus v (p * β)) ≐ sg (monus (quo (v + b0) β) p) := by
  have d := div_mod_at (Γ := Γ) (x := v + b0) hβ
  refine .orE (lt_or_le p (quo (v + b0) β)) ?_ ?_
  · -- `p < ⌈v/β⌉`: both positive
    let Δ : List (Fm PTm n) := lt p (quo (v + b0) β) :: Γ
    have ep := natEq (eq_add_of_le (Γ := Δ) Prf.hyp0)
    have ew := natEq (Γ := Δ) (Prf.andE₁ d).wk
    have eb := natEq (Γ := Δ) hβ.wk
    -- `v = pβ + 1 + (β (Q − p − 1) + R)` where `v + b0 = βQ + R`
    have hm : Δ ⊢[PRAAx] monus v (p * β) ≐ succ (β * monus (quo (v + b0) β) (succ p) + rem (v + b0) β) := by
      refine (congrMonus (?_ : _ ⊢[PRAAx] v ≐ p * β + succ (β * monus (quo (v + b0) β) (succ p) + rem (v + b0) β))
        (.eqRefl _)).eqTrans (add_monus' _ _)
      ipra_lc ew + 𝔞 β * ep + eb
    have hq : Δ ⊢[PRAAx] monus (quo (v + b0) β) p ≐ succ (monus (quo (v + b0) β) (succ p)) := by
      refine (congrMonus (?_ : _ ⊢[PRAAx] quo (v + b0) β ≐ p + succ (monus (quo (v + b0) β) (succ p))) (.eqRefl _)).eqTrans
        (add_monus' _ _)
      ipra_lc ep
    exact ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hm)).eqTrans (sg_succ _)).eqTrans
      ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hq)).eqTrans (sg_succ _)).eqSymm
  · -- `⌈v/β⌉ ≤ p`: both `0`
    let Δ : List (Fm PTm n) := le (quo (v + b0) β) p :: Γ
    have ep := natEq (eq_add_of_le (Γ := Δ) Prf.hyp0)
    have ew := natEq (Γ := Δ) (Prf.andE₁ d).wk
    have eb := natEq (Γ := Δ) hβ.wk
    have hm : Δ ⊢[PRAAx] monus v (p * β) ≐ zero := by
      refine le_of_eq_add (d := β * monus p (quo (v + b0) β) + monus β (succ (rem (v + b0) β))) ?_
      ipra_lc 𝔞 β * ep - ew - eb + natEq (Γ := Δ) (eq_add_of_le (Prf.andE₂ d)).wk
    exact ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hm)).eqTrans sg_zero).eqTrans
      ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans sg_zero).eqSymm

/-- `[u < pβ] · [pβ < v]` in `(p, ⟨u, ⟨v, β⟩⟩)`. -/
abbrev dcB : PTm 2 :=
  sg (monus (var 0 * sndT (sndT (var 1))) (fstT (var 1))) * sg (monus (fstT (sndT (var 1))) (var 0 * sndT (sndT (var 1))))

/-- `#{p < B : u < pβ < v}`. -/
abbrev dS (B u v β : PTm n) : PTm n := ap2 (sumF dcB) B (pairT u (pairT v β))

alias sg_congr := Common.congrSg

theorem dc_point (hβ : Γ ⊢[PRAAx] β ≐ succ b0) (p : PTm n) :
    Γ ⊢[PRAAx] inst2 dcB p (pairT u (pairT v β)) ≐ inst2 icB p (pairT (succ (quo u β)) (quo (v + b0) β)) := by
  have e1 : inst2 dcB p (pairT u (pairT v β)) =
      sg (monus (p * sndT (sndT (pairT u (pairT v β)))) (fstT (pairT u (pairT v β)))) *
        sg (monus (fstT (sndT (pairT u (pairT v β)))) (p * sndT (sndT (pairT u (pairT v β))))) := by
    simp [inst2, Signum.sg]
  have e2 : inst2 icB p (pairT (succ (quo u β)) (quo (v + b0) β)) =
      cnt (fstT (pairT (succ (quo u β)) (quo (v + b0) β))) (sndT (pairT (succ (quo u β)) (quo (v + b0) β))) p := by
    simp [inst2, Signum.sg]
  rw [e1, e2]
  have hz1 : Γ ⊢[PRAAx] fstT (pairT u (pairT v β)) ≐ u := fst_pair _ _
  have hz2 : Γ ⊢[PRAAx] fstT (sndT (pairT u (pairT v β))) ≐ v := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have hz3 : Γ ⊢[PRAAx] sndT (sndT (pairT u (pairT v β))) ≐ β := (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  have hb : Γ ⊢[PRAAx] p * sndT (sndT (pairT u (pairT v β))) ≐ p * β := congrMul (.eqRefl _) hz3
  refine (congrMul (sg_congr (congrMonus hb hz1)) (sg_congr (congrMonus hz2 hb))).eqTrans ?_
  refine (congrMul (floor_ind hβ) (ceil_ind hβ)).eqTrans ?_
  exact (congrMul (congrMonus (.eqRefl _) (congrMonus (fst_pair _ _) (.eqRefl _)))
    (sg_congr (congrMonus (snd_pair _ _) (.eqRefl _)))).eqSymm

/-- `#{p < B : u < pβ < v} = ⌈v/β⌉ ∸ (⌊u/β⌋ + 1)` when `⌈v/β⌉ ≤ B`. -/
theorem dS_eq (B : PTm n) (hβ : Γ ⊢[PRAAx] β ≐ succ b0) (hB : Γ ⊢[PRAAx] le (quo (v + b0) β) B) :
    Γ ⊢[PRAAx] dS B u v β ≐ monus (quo (v + b0) β) (succ (quo u β)) := by
  refine (sum_congr_bounded dcB icB _ _ B (.allI (.impI ?_))).eqTrans (exact_count B _ _ hB)
  have hβ' : (lt (var 0) (Syn.shift B) :: Γ.map Fm.shift) ⊢[PRAAx] Syn.shift β ≐ succ (Syn.shift b0) := by
    have a := hβ.shift
    simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_succ] at a
    exact a.wk
  have e1 : Syn.shift (pairT u (pairT v β)) = pairT (Syn.shift u) (pairT (Syn.shift v) (Syn.shift β)) := by
    simp [Syn.shift]
  have e2 : Syn.shift (pairT (succ (quo u β)) (quo (v + b0) β)) =
      pairT (succ (quo (Syn.shift u) (Syn.shift β))) (quo (Syn.shift v + Syn.shift b0) (Syn.shift β)) := by
    simp [Syn.shift, subst_ap2]
  rw [e1, e2]
  exact dc_point hβ' _

/-- An open interval of length `(v − u)/β` holds between `(v − u)/β − 1` and `(v − u)/β + 1`
integers: `β · count + u ≤ v + β` and `v ≤ β · count + u + β`, for `u ≤ v`. -/
theorem dilated_bounds (B : PTm n) (hβ : Γ ⊢[PRAAx] β ≐ succ b0) (hB : Γ ⊢[PRAAx] le (quo (v + b0) β) B)
    (huv : Γ ⊢[PRAAx] le u v) :
    Γ ⊢[PRAAx] le (β * dS B u v β + u) (v + β) ⋏ le v (β * dS B u v β + u + β) := by
  have hds := dS_eq (u := u) B hβ hB
  have du := div_mod_at (Γ := Γ) (x := u) hβ
  have dv := div_mod_at (Γ := Γ) (x := v + b0) hβ
  refine .orE (lt_or_le (quo (v + b0) β) (succ (quo u β))) ?_ ?_
  · -- `⌈v/β⌉ ≤ ⌊u/β⌋`: no integers
    let Δ : List (Fm PTm n) := lt (quo (v + b0) β) (succ (quo u β)) :: Γ
    have h0 : Δ ⊢[PRAAx] monus (quo (v + b0) β) (succ (quo u β)) ≐ zero := le_of_lt Prf.hyp0
    have eu' := natEq (Γ := Δ) (Prf.andE₁ du).wk
    have ew' := natEq (Γ := Δ) (Prf.andE₁ dv).wk
    have eR' := natEq (Γ := Δ) (eq_add_of_le (Prf.andE₂ dv)).wk
    refine .andI (le_of_eq_add (d := monus v u + β) ?_)
      (le_of_eq_add (d := β * monus (quo u β) (quo (v + b0) β) + rem u β + monus β (succ (rem (v + b0) β)) + succ b0) ?_)
    · ipra_lc natEq (eq_add_of_le (Γ := Δ) huv.wk) - 𝔞 β * natEq (hds.wk.eqTrans h0)
    · ipra_lc 𝔞 β * natEq (hds.wk.eqTrans h0) +
        𝔞 β * natEq (eq_add_of_le (Γ := Δ) ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)) + eu' - ew' + eR'
  · -- `⌊u/β⌋ + 1 ≤ ⌈v/β⌉`: the count is `D = Q − q − 1`
    let Δ : List (Fm PTm n) := le (succ (quo u β)) (quo (v + b0) β) :: Γ
    have eu' := natEq (Γ := Δ) (Prf.andE₁ du).wk
    have er' := natEq (Γ := Δ) (eq_add_of_le (Prf.andE₂ du)).wk
    have ew' := natEq (Γ := Δ) (Prf.andE₁ dv).wk
    have eR' := natEq (Γ := Δ) (eq_add_of_le (Prf.andE₂ dv)).wk
    have eb' := natEq (Γ := Δ) hβ.wk
    refine .andI (le_of_eq_add (d := two + monus β (succ (rem u β)) + rem (v + b0) β) ?_)
      (le_of_eq_add (d := monus β (succ (rem (v + b0) β)) + rem u β) ?_)
    · ipra_lc eb' + er' + ew' - eu' + 𝔞 β * natEq (eq_add_of_le (Γ := Δ) Prf.hyp0) - 𝔞 β * natEq (Γ := Δ) hds.wk
    · ipra_lc eR' - eb' - ew' + eu' - 𝔞 β * natEq (eq_add_of_le (Γ := Δ) Prf.hyp0) + 𝔞 β * natEq (Γ := Δ) hds.wk

end Dilated

end LeanProofs.IPRA.Foundations.LatticeCount
