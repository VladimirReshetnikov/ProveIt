import IPRADerivations.DiophantineNumberTheory.RectangleCount
import IPRADerivations.AnalyticNumberTheory.GcdFiber
import IPRADerivations.AnalyticNumberTheory.FactorialLambda
import IPRADerivations.AnalyticNumberTheory.ConvolutionAssoc
import IPRADerivations.Core.LinearCombination

/-!
# The parity conversion in Eisenstein's lemma

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex`, §"From products to
floor sums", "The parity conversion":

  "If `e_i = 0` then `r_i = b_i`. If `e_i = 1` then `r_i = p − b_i`, whence `r_i ≡ 1 + b_i (mod 2)` because `p` is
  odd. […] Sum the ordinary division identities `a i = p t_i + r_i` and use `eq:perm` to get
  `B ≡ a B ≡ p S_p(a) + Σ r_i ≡ S_p(a) + B + N_p(a) (mod 2)`. It follows that `S_p(a)` and `N_p(a)` have the same
  parity."

For an odd `p = 2h + 1`, an odd `a` and `1 ≤ i ≤ h`, with `t_i = ⌊a i / p⌋`, `r_i = a i mod p`, `e_i = [r_i > h]`,
`b_i = min(r_i, p − r_i)`, `S_p(a) = Σ t_i`, `N_p(a) = Σ e_i`, this module derives

  `Σ_i b_i = Σ_i i`   implies   `par S_p(a) = par N_p(a)`                               (`eisenstein_parity`),

and `par (floorSum p a) = par N_p(a)` under the same hypothesis (`floor_parity`), where `floorSum` is the sum of
`QuadraticReciprocityGoal`. The indices are `i < h` with `i + 1` in place of `i`.

The hypothesis `Σ b_i = Σ i` is the additive half of `eq:perm` (the folded residues form a permutation of
`1, …, h`); it is not derived here. Neither are Gauss's lemma `eq:gauss` and Euler's criterion `eq:euler`, so
Eisenstein's lemma itself is not derived.

* `rV`, `tV`, `eV`, `wV`, `bV`: the values `r_i`, `t_i`, `e_i`, `e_i (p − r_i)`, `b_i`;
* `p2`: `r + 2 e (p − r) = b + e p`, the two cases of the folding in one identity;
* `total_alg`: the final identity `(S + N) + 2 h (S + N) = 2 (a' B + W)` over opaque terms.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.EisensteinParity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (sg_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt' sum2_lift)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (lift3 at_pair)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.DiophantineNumberTheory.QuadraticReciprocityGoal (floorSum)
open LeanProofs.IPRA.DiophantineNumberTheory.RectangleCount (fsB inst3_fsB)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The values -/

/-- `r_i = (i + 1) a mod p`. -/
abbrev rV (i p a : PTm n) : PTm n := rem (succ i * a) p
/-- `t_i = ⌊(i + 1) a / p⌋`. -/
abbrev tV (i p a : PTm n) : PTm n := quo (succ i * a) p
/-- `e_i = [r_i > ⌊p/2⌋]`. -/
abbrev eV (i p a : PTm n) : PTm n := sg (monus (rV i p a) (half p))
/-- `e_i (p − r_i)`. -/
abbrev wV (i p a : PTm n) : PTm n := eV i p a * monus p (rV i p a)
/-- `b_i = min(r_i, p − r_i)`, as `e_i (p − r_i) + (1 − e_i) r_i`. -/
abbrev bV (i p a : PTm n) : PTm n := wV i p a + monus one (eV i p a) * rV i p a

theorem p2_zero {E ne R M p : PTm n} (hE : Γ ⊢[PRAAx] E ≐ zero) (hn : Γ ⊢[PRAAx] ne ≐ one) :
    Γ ⊢[PRAAx] R + (E * M + E * M) ≐ (E * M + ne * R) + E * p := by
  ipra_lc (𝔞 M - 𝔞 p) * natEq hE - 𝔞 R * natEq hn

theorem p2_one {E ne R M p : PTm n} (hE : Γ ⊢[PRAAx] E ≐ one) (hn : Γ ⊢[PRAAx] ne ≐ zero)
    (x : Γ ⊢[PRAAx] p ≐ R + M) : Γ ⊢[PRAAx] R + (E * M + E * M) ≐ (E * M + ne * R) + E * p := by
  ipra_lc (𝔞 M - 𝔞 p) * natEq hE - 𝔞 R * natEq hn - natEq x

/-- `r + 2 e (p − r) = b + e p`: for `e = 0` it is `r = b`, for `e = 1` it is `r + b = p`. -/
theorem p2 {p : PTm n} (i a : PTm n) (hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] rV i p a + (wV i p a + wV i p a) ≐ bV i p a + eV i p a * p := by
  have x : Γ ⊢[PRAAx] p ≐ rV i p a + monus p (rV i p a) := eq_add_of_le (le_of_lt (rem_lt' hp1 _))
  refine .orE (zero_or_succ (monus (rV i p a) (half p))) ?_ ?_
  · have hE : ((monus (rV i p a) (half p) ≐ zero) :: Γ) ⊢[PRAAx] eV i p a ≐ zero :=
      (congrSg Prf.hyp0).eqTrans sg_zero
    exact p2_zero hE ((congrMonus (.eqRefl _) hE).eqTrans (monus_zero _))
  · have hE : ((monus (rV i p a) (half p) ≐ succ (pred (monus (rV i p a) (half p)))) :: Γ) ⊢[PRAAx]
        eV i p a ≐ one := sg_pos Prf.hyp0
    exact p2_one hE ((congrMonus (.eqRefl _) hE).eqTrans (monus_self _)) x.wk

/-! ## The bodies, over `0 = i`, `1 = ⟨p, a⟩` -/

abbrev mB : PTm 2 := succ (var 0) * sndT (var 1)
abbrev idB : PTm 2 := succ (var 0)
abbrev rB : PTm 2 := rV (var 0) (fstT (var 1)) (sndT (var 1))
abbrev tB : PTm 2 := tV (var 0) (fstT (var 1)) (sndT (var 1))
abbrev eB : PTm 2 := eV (var 0) (fstT (var 1)) (sndT (var 1))
abbrev wB : PTm 2 := wV (var 0) (fstT (var 1)) (sndT (var 1))
abbrev bB : PTm 2 := bV (var 0) (fstT (var 1)) (sndT (var 1))
/-- `p t_i`. -/
abbrev ptB : PTm 2 := fstT (var 1) * tB
/-- `e_i p`. -/
abbrev epB : PTm 2 := eB * fstT (var 1)

theorem inst2_mB (i x : PTm n) : inst2 mB i x = succ i * sndT x := by simp [inst2]
theorem inst2_idB (i x : PTm n) : inst2 idB i x = succ i := by simp [inst2]
theorem inst2_rB (i x : PTm n) : inst2 rB i x = rV i (fstT x) (sndT x) := by simp [inst2]
theorem inst2_tB (i x : PTm n) : inst2 tB i x = tV i (fstT x) (sndT x) := by simp [inst2]
theorem inst2_eB (i x : PTm n) : inst2 eB i x = eV i (fstT x) (sndT x) := by simp [inst2, subst_ap1]
theorem inst2_wB (i x : PTm n) : inst2 wB i x = wV i (fstT x) (sndT x) := by simp [inst2, subst_ap1]
theorem inst2_bB (i x : PTm n) : inst2 bB i x = bV i (fstT x) (sndT x) := by simp [inst2, subst_ap1]
theorem inst2_ptB (i x : PTm n) : inst2 ptB i x = fstT x * tV i (fstT x) (sndT x) := by simp [inst2]
theorem inst2_epB (i x : PTm n) : inst2 epB i x = eV i (fstT x) (sndT x) * fstT x := by
  simp [inst2, subst_ap1]

/-! ## The sums -/

theorem comm_alg (u v : PTm n) : Γ ⊢[PRAAx] u * v ≐ v * u := mul_comm u v

/-- The final identity: `(S + N) + 2 h (S + N) = 2 (a' B + W)`. -/
theorem total_alg {S N h a' B W p M R Bb a : PTm n} (m1 : Γ ⊢[PRAAx] M ≐ p * S + R)
    (m2 : Γ ⊢[PRAAx] M ≐ a * B) (s2 : Γ ⊢[PRAAx] R + (W + W) ≐ Bb + p * N) (hperm : Γ ⊢[PRAAx] Bb ≐ B)
    (ea : Γ ⊢[PRAAx] a ≐ two * a' + one) (ep : Γ ⊢[PRAAx] p ≐ two * h + one) :
    Γ ⊢[PRAAx] (S + N) + two * (h * (S + N)) ≐ zero + two * (a' * B + W) := by
  ipra_lc -(𝔞 S + 𝔞 N) * natEq ep - natEq m1 - natEq s2 + natEq m2 - natEq hperm + 𝔞 B * natEq ea

/-- `Σ b_i = Σ i` gives `par S_p(a) = par N_p(a)` for odd `p` and odd `a`. -/
theorem eisenstein_parity {p a : PTm n} (hp : Γ ⊢[PRAAx] par p ≐ one) (ha : Γ ⊢[PRAAx] par a ≐ one)
    (hperm : Γ ⊢[PRAAx] ap2 (sumF bB) (half p) (pairT p a) ≐ ap2 (sumF idB) (half p) (pairT p a)) :
    Γ ⊢[PRAAx] par (ap2 (sumF tB) (half p) (pairT p a)) ≐ par (ap2 (sumF eB) (half p) (pairT p a)) := by
  have ep := odd_of hp
  have ea := odd_of ha
  have hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p) :=
    pos_of_eq_succ (c := two * half p) (ep.eqTrans (by ipra_ring))
  have hp1' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ succ (pred (Syn.shift p)) := by
    simpa [Fm.shift, Syn.shift] using hp1.shift
  -- `Σ (i + 1) a = p Σ t_i + Σ r_i`
  have pt : Γ ⊢[PRAAx] ap2 (sumF ptB) (half p) (pairT p a) ≐ p * ap2 (sumF tB) (half p) (pairT p a) := by
    refine sum_scale ptB tB (half p) p (pairT p a) (pairT p a) (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [inst2_ptB, inst2_tB]
    exact congrMul (fst_pair _ _) (.eqRefl _)
  have m1 : Γ ⊢[PRAAx] ap2 (sumF mB) (half p) (pairT p a) ≐
      p * ap2 (sumF tB) (half p) (pairT p a) + ap2 (sumF rB) (half p) (pairT p a) := by
    refine (sum_add2 ptB rB mB (.allI (.impI ?_))).eqTrans (congrAdd pt (.eqRefl _))
    simp only [shift_pairT]
    rw [inst2_mB, inst2_ptB, inst2_rB]
    have d := div_eq (Γ := lt (var 0) (Syn.shift (half p)) :: Γ.map Fm.shift) (j := succ (var 0) * Syn.shift a)
      hp1'.wk
    exact (congrMul (.eqRefl _) (snd_pair _ _)).eqTrans (d.eqTrans (congrAdd
      (congrMul (fst_pair _ _).eqSymm (congrAp2 quoF (congrMul (.eqRefl _) (snd_pair _ _)).eqSymm
        (fst_pair _ _).eqSymm))
      (congrAp2 remF (congrMul (.eqRefl _) (snd_pair _ _)).eqSymm (fst_pair _ _).eqSymm)))
  -- `Σ (i + 1) a = a Σ (i + 1)`
  have m2 : Γ ⊢[PRAAx] ap2 (sumF mB) (half p) (pairT p a) ≐ a * ap2 (sumF idB) (half p) (pairT p a) := by
    refine sum_scale mB idB (half p) a (pairT p a) (pairT p a) (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [inst2_mB, inst2_idB]
    exact (congrMul (.eqRefl _) (snd_pair _ _)).eqTrans (mul_comm _ _)
  -- `Σ r_i + 2 Σ e_i (p − r_i) = Σ b_i + p Σ e_i`
  have pe : Γ ⊢[PRAAx] ap2 (sumF epB) (half p) (pairT p a) ≐ p * ap2 (sumF eB) (half p) (pairT p a) := by
    refine sum_scale epB eB (half p) p (pairT p a) (pairT p a) (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [inst2_epB, inst2_eB]
    exact (congrMul (.eqRefl _) (fst_pair _ _)).eqTrans (mul_comm _ _)
  have s2 : Γ ⊢[PRAAx] ap2 (sumF rB) (half p) (pairT p a) +
      (ap2 (sumF wB) (half p) (pairT p a) + ap2 (sumF wB) (half p) (pairT p a)) ≐
      ap2 (sumF bB) (half p) (pairT p a) + p * ap2 (sumF eB) (half p) (pairT p a) := by
    have l := (sum_add (Γ := Γ) rB (addBody wB wB) (half p) (pairT p a)).eqTrans
      (congrAdd (.eqRefl _) (sum_add wB wB (half p) (pairT p a)))
    have r := (sum_add (Γ := Γ) bB epB (half p) (pairT p a)).eqTrans (congrAdd (.eqRefl _) pe)
    refine l.eqSymm.eqTrans (.eqTrans (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))) r)
    simp only [shift_pairT]
    rw [inst2_addBody, inst2_addBody, inst2_addBody, inst2_rB, inst2_wB, inst2_bB, inst2_epB]
    have hf : (lt (var 0) (Syn.shift (half p)) :: Γ.map Fm.shift) ⊢[PRAAx]
        fstT (pairT (Syn.shift p) (Syn.shift a)) ≐ succ (pred (fstT (pairT (Syn.shift p) (Syn.shift a)))) :=
      (fst_pair _ _).eqTrans (hp1'.wk.eqTrans (congrSucc (congrPred (fst_pair _ _))).eqSymm)
    exact p2 _ _ hf
  have t := total_alg m1 m2 s2 hperm ea ep
  have ev : Γ ⊢[PRAAx] par (ap2 (sumF tB) (half p) (pairT p a) + ap2 (sumF eB) (half p) (pairT p a)) ≐ zero :=
    (par_add_two _ _).eqSymm.eqTrans ((congrAp1 parF t).eqTrans ((par_add_two _ _).eqTrans par_zero))
  exact par_eq_of_add_even ev

/-- `floorSum p a` is `S_p(a)`. -/
theorem floorSum_eq (p a : PTm n) :
    Γ ⊢[PRAAx] floorSum p a ≐ ap2 (sumF tB) (half p) (pairT p a) := by
  refine (sum2_lift (Γ := Γ) fsB (half p) p a).eqTrans (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
  simp only [shift_pairT]
  rw [inst2_tB]
  have h := at_pair (Γ := lt (var 0) (Syn.shift (half p)) :: Γ.map Fm.shift) fsB (var 0) (Syn.shift p) (Syn.shift a)
  rw [inst3_fsB] at h
  exact h.eqTrans (congrAp2 quoF (congrMul (.eqRefl _) (snd_pair _ _)).eqSymm (fst_pair _ _).eqSymm)

/-- `Σ b_i = Σ i` gives `par (floorSum p a) = par N_p(a)` for odd `p` and odd `a`. -/
theorem floor_parity {p a : PTm n} (hp : Γ ⊢[PRAAx] par p ≐ one) (ha : Γ ⊢[PRAAx] par a ≐ one)
    (hperm : Γ ⊢[PRAAx] ap2 (sumF bB) (half p) (pairT p a) ≐ ap2 (sumF idB) (half p) (pairT p a)) :
    Γ ⊢[PRAAx] par (floorSum p a) ≐ par (ap2 (sumF eB) (half p) (pairT p a)) :=
  (congrAp1 parF (floorSum_eq p a)).eqTrans (eisenstein_parity hp ha hperm)

end LeanProofs.IPRA.DiophantineNumberTheory.EisensteinParity
