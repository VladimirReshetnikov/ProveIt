import IPRADerivations.AnalyticNumberTheory.CanonicalPowers
import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.Core.Search
import IPRADerivations.Probability.Variance
import IPRADerivations.Core.Fubini
import IPRADerivations.Combinatorics.CatalanConvolution
import IPRADerivations.Analysis.RationalArithmetic.RationalClosure
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header

/-!
# The canonical root decomposition

Packet: `analytic-number-theory/goldbach_euler_ipra`, Lemma `lem:canonical`: every `N ≥ 2` has
exactly one canonical representation `N = r^e` with `r` root-free (`RF`, see
`AnalyticNumberTheory/CanonicalPowers`) and `e ≥ 1`, and `r`, `e` are primitive-recursive
functions of `N`.

The packet computes `e` as the gcd of the prime exponents. Here `e` is the largest exponent for
which `N` is a perfect power, found by two bounded searches (`Core/Search`):

* `rootT e N`: the least `w ≤ N` with `w^e = N` (`N + 1` if none), a search with body `|w^e − N|`;
* `KT N`: the least `k < N` with `rootT (N − k) N ≤ N`; then `eT N = N − KT N` and
  `rT N = rootT (eT N) N`.

Derived, for `N ≥ 2`:

* `canonical_pow`: `rT N ^ eT N = N`, with `eT N ≥ 1` (`e_pos`), because `e = 1` always succeeds;
* `maximal`: if `w^{e'} = N` with `w, e' ≤ N` and `e' ≥ 1`, then `e' ≤ eT N`;
* `canonical_RF`: `rT N` is root-free: `rT N = w^d` with `d ≥ 2` would give
  `N = w^{d·e}` with `d·e > e`, and `w, d·e ≤ N` (since `d·e < 2^{d·e} ≤ w^{d·e}`), against
  maximality;
* `canonical_unique`: any canonical `N = u^j` has `u = rT N` and `j = eT N`
  (`canonical_injective`);
* `perfect_canonical` (`cor:perfect-bij`, surjectivity; injectivity is `canonical_injective`): a
  perfect power `N = w^d` with `w, d ≥ 2` has `eT N ≥ d ≥ 2`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.CanonicalDecomposition

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.CanonicalPowers
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.CatalanConvolution (monus_monus)
open LeanProofs.IPRA.Analysis.RationalClosure (succ_le_two_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (eq_succ_pred)
open LeanProofs.IPRA.Probability.Variance (ad)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The searches -/

/-- `|w^e − N|` at `(w, ⟨e, N⟩)`. -/
abbrev fB : PTm 2 := ad (pw (var 0) (fstT (var 1))) (sndT (var 1))
/-- The least `w ≤ N` with `w^e = N`, or `N + 1`. -/
abbrev rootT (e N : PTm n) : PTm n := Search.mu fB (succ N) (pairT e N)
/-- Zero exactly when `N − k` is an exponent of `N`; variables `0 = k`, `1 = N`. -/
abbrev gB : PTm 2 := monus (succ (rootT (monus (var 1) (var 0)) (var 1))) (succ (var 1))
/-- The least `k < N` for which `N − k` is an exponent. -/
abbrev KT (N : PTm n) : PTm n := Search.mu gB N N
/-- The canonical exponent `e = N − K`. -/
abbrev eT (N : PTm n) : PTm n := monus N (KT N)
/-- The canonical root `r = rootT e N`. -/
abbrev rT (N : PTm n) : PTm n := rootT (eT N) N

theorem inst2_f (w y : PTm n) : inst2 fB w y = ad (pw w (fstT y)) (sndT y) := by simp [inst2]
theorem inst2_g (k N : PTm n) : inst2 gB k N = monus (succ (rootT (monus N k) N)) (succ N) := by
  simp [inst2]

/-! ## Elementary facts -/

theorem ad_zero {a b : PTm n} (h : Γ ⊢[PRAAx] ad a b ≐ zero) : Γ ⊢[PRAAx] a ≐ b :=
  le_antisymm (add_eq_zero_left h) (add_eq_zero_right h)

theorem ad_of_eq {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] ad a b ≐ zero :=
  (congrAdd (le_congr (.eqRefl a) h (le_refl a)) (le_congr h (.eqRefl a) (le_refl a))).eqTrans (add_zero _)

alias two_le_pos := Common.pos_of_two_le

/-- `x^k = M ≥ 2` forces `x ≥ 2`. -/
theorem two_le_base {x k M : PTm n} (h : Γ ⊢[PRAAx] pw x k ≐ M) (hM : Γ ⊢[PRAAx] le two M) :
    Γ ⊢[PRAAx] le two x := by
  refine .orE (lt_or_le one x) Prf.hyp0 ?_
  have a := pw_le_pw k (Prf.hyp0 : (le x one :: Γ) ⊢[PRAAx] _)
  exact not_succ_le_self one _ (le_trans hM.wk (le_congr h.wk (pw_one_base k) a))

theorem f_at (w e N : PTm n) : Γ ⊢[PRAAx] inst2 fB w (pairT e N) ≐ ad (pw w e) N := by
  rw [inst2_f]
  have h₁ : Γ ⊢[PRAAx] pw w (fstT (pairT e N)) ≐ pw w e := congrPw (.eqRefl w) (fst_pair e N)
  have h₂ : Γ ⊢[PRAAx] sndT (pairT e N) ≐ N := snd_pair e N
  exact congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁)

/-! ## The root search -/

theorem root_hit {w e N : PTm n} (hw : Γ ⊢[PRAAx] pw w e ≐ N) (hwN : Γ ⊢[PRAAx] le w N) :
    Γ ⊢[PRAAx] lt (rootT e N) (succ N) ⋏ (pw (rootT e N) e ≐ N) := by
  have hl : Γ ⊢[PRAAx] lt w (succ N) := (succ_monus_succ w N).eqTrans hwN
  have s := Search.search_found (f := fB) ((f_at w e N).eqTrans (ad_of_eq hw)) hl
  exact .andI (Prf.andE₁ s) (ad_zero ((f_at _ e N).eqSymm.eqTrans (Prf.andE₁ (Prf.andE₂ s))))

theorem root_spec {e N : PTm n} (h : Γ ⊢[PRAAx] lt (rootT e N) (succ N)) :
    Γ ⊢[PRAAx] pw (rootT e N) e ≐ N := by
  have s := Search.search_spec (Γ := Γ) (f := fB) (succ N) zero (pairT e N)
  exact ad_zero ((f_at _ e N).eqSymm.eqTrans (Prf.impE (Prf.andE₁ (Prf.andE₂ s)) h))

theorem g_zero_of {w e N : PTm n} (hw : Γ ⊢[PRAAx] pw w e ≐ N) (hwN : Γ ⊢[PRAAx] le w N)
    (heN : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx] inst2 gB (monus N e) N ≐ zero := by
  rw [inst2_g]
  have c : Γ ⊢[PRAAx] rootT (monus N (monus N e)) N ≐ rootT e N :=
    congrAp2 (Search.muF fB) (.eqRefl _) (congrPairT (monus_monus heN) (.eqRefl N))
  exact (congrMonus (congrSucc c) (.eqRefl _)).eqTrans (Prf.andE₁ (root_hit hw hwN))

/-! ## The exponent search -/

/-- Maximality: `w^{e'} = N`, `w, e' ≤ N`, `e' ≥ 1` give `e' ≤ eT N`. -/
theorem maximal {w e N : PTm n} (hw : Γ ⊢[PRAAx] pw w e ≐ N) (hwN : Γ ⊢[PRAAx] le w N)
    (heN : Γ ⊢[PRAAx] le e N) (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) : Γ ⊢[PRAAx] le e (eT N) := by
  have hlt : Γ ⊢[PRAAx] lt (monus N e) N := by
    refine le_of_eq_add (d := pred e) ?_
    ipra_lc natEq (eq_add_of_le heN) + natEq he
  have s := Search.search_found (f := gB) (g_zero_of hw hwN heN) hlt
  refine le_of_eq_add (d := monus (monus N e) (KT N)) ?_
  ipra_lc -natEq (eq_add_of_le (le_trans (le_succ_self _) (Prf.andE₁ s))) + natEq (eq_add_of_le heN) +
    natEq (eq_add_of_le (Prf.andE₂ (Prf.andE₂ s)))

theorem K_lt {N : PTm n} (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] lt (KT N) N ⋏ (inst2 gB (KT N) N ≐ zero) := by
  have h₁ : Γ ⊢[PRAAx] le one N := le_trans (le_succ_self one) hN
  have g := g_zero_of (pw_one N) (le_refl N) h₁
  have hlt : Γ ⊢[PRAAx] lt (monus N one) N := by
    refine le_of_eq_add (d := zero) ?_
    ipra_lc natEq (eq_add_of_le h₁)
  have s := Search.search_found (f := gB) g hlt
  exact .andI (Prf.andE₁ s) (Prf.andE₁ (Prf.andE₂ s))

/-- `rT N ^ eT N = N`. -/
theorem canonical_pow {N : PTm n} (hN : Γ ⊢[PRAAx] le two N) : Γ ⊢[PRAAx] pw (rT N) (eT N) ≐ N := by
  have z := Prf.andE₂ (K_lt hN)
  rw [inst2_g] at z
  exact root_spec z

/-- `eT N ≥ 1`. -/
theorem e_pos {N : PTm n} (hN : Γ ⊢[PRAAx] le two N) : Γ ⊢[PRAAx] eT N ≐ succ (pred (eT N)) := by
  have k := Prf.andE₁ (K_lt hN)
  show Γ ⊢[PRAAx] monus N (KT N) ≐ succ (pred (monus N (KT N)))
  refine eq_succ_pred (y := monus N (succ (KT N))) ?_
  ipra_lc natEq (eq_add_of_le k) - natEq (eq_add_of_le (le_trans (le_succ_self _) k))

/-! ## Root-freeness and uniqueness -/

theorem no_root {N w d : PTm n} (hN : Γ ⊢[PRAAx] le two N) (hd : Γ ⊢[PRAAx] le two d)
    (h : Γ ⊢[PRAAx] pw w d ≐ rT N) : Γ ⊢[PRAAx] Fm.bot := by
  have hp := canonical_pow hN
  have he := e_pos hN
  have hwN' : Γ ⊢[PRAAx] pw w (d * eT N) ≐ N :=
    (pw_mul w d (eT N)).eqSymm.eqTrans ((congrPw h (.eqRefl _)).eqTrans hp)
  have hr2 := two_le_base hp hN
  have hw2 := two_le_base h hr2
  have hde := pos_mul (two_le_pos hd) he
  have hwpos := two_le_pos hw2
  have hwN : Γ ⊢[PRAAx] le w N :=
    le_congr hwpos.eqSymm ((congrPw hwpos.eqSymm hde.eqSymm).eqTrans hwN')
      (le_self_pw (pred w) (pred (d * eT N)))
  have hdeN : Γ ⊢[PRAAx] le (d * eT N) N :=
    le_trans (le_succ_self _) (le_trans (succ_le_two_pow _)
      (le_congr (.eqRefl _) hwN' (pw_le_pw (d * eT N) hw2)))
  have m := maximal hwN' hwN hdeN hde
  have l₃ : Γ ⊢[PRAAx] le (succ (eT N)) (d * eT N) := by
    refine le_of_eq_add (d := pred (eT N) + monus d two * eT N) ?_
    ipra_lc 𝔞 (eT N) * natEq (eq_add_of_le hd) + natEq he
  exact not_succ_le_self (eT N) _ (le_trans l₃ m)

theorem shift_shift_rT (N : PTm n) : Syn.shift (Syn.shift (rT N)) = rT (Syn.shift (Syn.shift N)) := by
  simp [Syn.shift]

/-- `rT N` is root-free. -/
theorem canonical_RF {N : PTm n} (hN : Γ ⊢[PRAAx] le two N) : Γ ⊢[PRAAx] RF (rT N) := by
  refine .andI (two_le_base (canonical_pow hN) hN) ?_
  refine .allI (.allI (.impI (.impI ?_)))
  have hN' : ((Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx] le two (Syn.shift (Syn.shift N)) := by
    simpa [Fm.shift, Syn.shift] using hN.shift.shift
  rw [shift_shift_rT]
  exact no_root hN'.wk.wk Prf.hyp1 Prf.hyp0

/-- `lem:canonical`, uniqueness: a canonical `N = u^j` has `u = rT N` and `j = eT N`. -/
theorem canonical_unique {N u j : PTm n} (hN : Γ ⊢[PRAAx] le two N) (hu : Γ ⊢[PRAAx] RF u)
    (hj : Γ ⊢[PRAAx] j ≐ succ (pred j)) (h : Γ ⊢[PRAAx] pw u j ≐ N) :
    Γ ⊢[PRAAx] (u ≐ rT N) ⋏ (j ≐ eT N) :=
  canonical_injective hu (canonical_RF hN) hj (e_pos hN) (h.eqTrans (canonical_pow hN).eqSymm)

/-- `cor:perfect-bij`, surjectivity: a perfect power `N = w^d` (`w, d ≥ 2`) has canonical exponent
`eT N ≥ d ≥ 2`, so `N = (rT N)^{eT N}` is the image of a pair with `RF(rT N)` and `eT N ≥ 2`. -/
theorem perfect_canonical {N w d : PTm n} (h : Γ ⊢[PRAAx] pw w d ≐ N)
    (hw : Γ ⊢[PRAAx] le two w) (hd : Γ ⊢[PRAAx] le two d) : Γ ⊢[PRAAx] le d (eT N) ⋏ le two (eT N) := by
  have hdpos := two_le_pos hd
  have hwpos := two_le_pos hw
  have hwN : Γ ⊢[PRAAx] le w N :=
    le_congr hwpos.eqSymm ((congrPw hwpos.eqSymm hdpos.eqSymm).eqTrans h) (le_self_pw (pred w) (pred d))
  have hdN : Γ ⊢[PRAAx] le d N :=
    le_trans (le_succ_self _) (le_trans (succ_le_two_pow _) (le_congr (.eqRefl _) h (pw_le_pw d hw)))
  have m := maximal h hwN hdN hdpos
  exact .andI m (le_trans hd m)

end LeanProofs.IPRA.AnalyticNumberTheory.CanonicalDecomposition
