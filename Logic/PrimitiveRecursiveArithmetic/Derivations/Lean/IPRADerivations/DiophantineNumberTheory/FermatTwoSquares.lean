import IPRADerivations.DiophantineNumberTheory.ThueGrid
import IPRADerivations.DiophantineNumberTheory.QuadraticSupplements
import IPRADerivations.Combinatorics.IndependentSets
import IPRADerivations.AnalyticNumberTheory.BertrandFactor

/-!
# Fermat's theorem on sums of two squares, with primitive recursive witnesses

Packet: `diophantine-number-theory/fermat_two_squares_ipra_2026-11-22`, `fermat_two_squares_ipra.tex`,
`thm:main`: for a prime `p`, `p` is a sum of two squares if and only if `p = 2` or `p ≡ 1 (mod 4)`, with the
witness-bearing form `A(p)² + B(p)² = p`.

* `rt p`: the root of `−1` modulo `p` returned by the bounded search of the quadratic-reciprocity modules
  (`QuadraticSupplements.root_of_sign` at the residue `p − 1`);
* `mod4_parities`: `p ≡ 1 (mod 4)` gives `p` odd and `⌊p/2⌋` even;
* `root_minus_one`: for an odd prime `p` with `⌊p/2⌋` even, `p ∣ rt(p)² + 1`. This is the first supplementary
  law `(−1/p) = (−1)^{(p−1)/2}` (`QuadraticSupplements.minus_one_law`); the paper obtains the root as the
  half-factorial from Wilson's theorem (`lem:root`);
* `two_squares_of_mod4`: `G₁(p, rt p)² + G₂(p, rt p)² = p` (`ThueGrid.root_to_squares`);
* `Aw`, `Bw`, `fermat_witness`: the total witnesses, equal to `1, 1` at `p = 2`, with
  `Aw(p)² + Bw(p)² = p` for a prime `p` with `p = 2` or `p ≡ 1 (mod 4)`;
* `odd_of_prime_ne_two`: a prime other than `2` is odd;
* `mod4_of_squares`: an odd `p = a² + b²` has `p ≡ 1 (mod 4)`, by the four parity patterns of `a`, `b`;
* `fermat_converse_open`: for a prime `p = a² + b²`: `p = 2` or `p ≡ 1 (mod 4)`;
* **`fermat_forward`**, **`fermat_converse`**: the two directions as closed sentences. The converse is
  universally quantified over `a`, `b`, which is the constructive form of "if `p` is represented".

Not derived: the bounds `1 ≤ A(p) ≤ B(p) ≤ ⌊√p⌋` of the sorted witnesses (the outputs here are not sorted), the
half-factorial form of the root, and the independent construction by bounded descent.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.FermatTwoSquares

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm dmu)
open LeanProofs.IPRA.Combinatorics.IndependentSets (half_double half_double_succ)
open LeanProofs.IPRA.DiophantineNumberTheory.PairProduct (sqB)
open LeanProofs.IPRA.DiophantineNumberTheory.QuadraticSupplements (root_of_sign minus_one_law)
open LeanProofs.IPRA.DiophantineNumberTheory.ThueGrid (G1 G2 root_to_squares)
open LeanProofs.IPRA.Foundations.BoundedReflection (wit eqb_cases eq_of_eqb one_ne_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The root of `−1` -/

/-- The root of `−1` modulo `p` found by the bounded search. -/
abbrev rt (p : PTm n) : PTm n := wit sqB p (pairT p (pred p))

theorem four_pos : Γ ⊢[PRAAx] (two * two : PTm n) ≐ succ (pred (two * two)) :=
  pos_of_eq_succ (c := succ two) (by ipra_ring)

/-- `p ≡ 1 (mod 4)` gives `p` odd and `⌊p/2⌋` even. -/
theorem mod4_parities {p : PTm n} (h : Γ ⊢[PRAAx] rem p (two * two) ≐ one) :
    Γ ⊢[PRAAx] (par p ≐ one) ⋏ (par (half p) ≐ zero) := by
  have d := natEq (Prf.andE₁ (dm (Γ := Γ) four_pos p)); have hn := natEq h
  have e : Γ ⊢[PRAAx] p ≐ two * (two * quo p (two * two)) + one := by
    ipra_lc d + hn
  refine .andI ((congrAp1 parF e).eqTrans (par_double_succ _)) ?_
  exact (congrAp1 parF ((congrAp1 halfF e).eqTrans (half_double_succ _))).eqTrans (par_double _)

/-- For an odd prime `p` with `⌊p/2⌋` even: `p ∣ rt(p)² + 1`. -/
theorem root_minus_one {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (hh : Γ ⊢[PRAAx] par (half p) ≐ zero) : Γ ⊢[PRAAx] dvd p (rt p * rt p + one) := by
  have hp1 := p_pos (prime_two hp)
  have r := Prf.andE₂ (root_of_sign ((minus_one_law hp hodd).eqTrans hh))
  have a := rem_add_congr hp1 r (.eqRefl (rem one p))
  have e : Γ ⊢[PRAAx] pred p + one ≐ p * one + zero := by
    ipra_lc -natEq hp1
  exact a.eqTrans ((congrAp2 remF e (.eqRefl _)).eqTrans ((rem_add_mul hp1 one zero).eqTrans (rem_zero p)))

/-- For an odd prime `p` with `⌊p/2⌋` even: `G₁² + G₂² = p`. -/
theorem two_squares_of_mod4 {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (hh : Γ ⊢[PRAAx] par (half p) ≐ zero) :
    Γ ⊢[PRAAx] G1 p (rt p) * G1 p (rt p) + G2 p (rt p) * G2 p (rt p) ≐ p :=
  root_to_squares (p_pos (prime_two hp)) (root_minus_one hp hodd hh)

/-! ## The total witnesses -/

/-- `A(p)`: `1` at `p = 2`, otherwise `G₁(p, rt p)`. -/
abbrev Aw (p : PTm n) : PTm n := eqb p two + monus one (eqb p two) * G1 p (rt p)

/-- `B(p)`: `1` at `p = 2`, otherwise `G₂(p, rt p)`. -/
abbrev Bw (p : PTm n) : PTm n := eqb p two + monus one (eqb p two) * G2 p (rt p)

theorem two_case {Eb M X Y p : PTm n} (e1 : Γ ⊢[PRAAx] Eb ≐ one) (m0 : Γ ⊢[PRAAx] M ≐ zero)
    (ep : Γ ⊢[PRAAx] p ≐ two) :
    Γ ⊢[PRAAx] (Eb + M * X) * (Eb + M * X) + (Eb + M * Y) * (Eb + M * Y) ≐ p := by
  ipra_lc (𝔞 Eb + 𝔞 M * 𝔞 X + 1) * natEq e1 + 𝔞 X * (𝔞 Eb + 𝔞 M * 𝔞 X + 1) * natEq m0 +
    (𝔞 Eb + 𝔞 M * 𝔞 Y + 1) * natEq e1 + 𝔞 Y * (𝔞 Eb + 𝔞 M * 𝔞 Y + 1) * natEq m0 - natEq ep

theorem odd_case {Eb M X Y p : PTm n} (e0 : Γ ⊢[PRAAx] Eb ≐ zero) (m1 : Γ ⊢[PRAAx] M ≐ one)
    (h : Γ ⊢[PRAAx] X * X + Y * Y ≐ p) :
    Γ ⊢[PRAAx] (Eb + M * X) * (Eb + M * X) + (Eb + M * Y) * (Eb + M * Y) ≐ p := by
  ipra_lc (𝔞 Eb + 𝔞 M * 𝔞 X + 𝔞 X) * natEq e0 + 𝔞 X * (𝔞 Eb + 𝔞 M * 𝔞 X + 𝔞 X) * natEq m1 +
    (𝔞 Eb + 𝔞 M * 𝔞 Y + 𝔞 Y) * natEq e0 + 𝔞 Y * (𝔞 Eb + 𝔞 M * 𝔞 Y + 𝔞 Y) * natEq m1 + natEq h

theorem par_two : Γ ⊢[PRAAx] par (two : PTm n) ≐ zero := by
  have e : Γ ⊢[PRAAx] (two : PTm n) ≐ two * one := by ipra_ring
  exact (congrAp1 parF e).eqTrans (par_double one)

/-- The witness-bearing form of `thm:main`: for a prime `p` with `p = 2` or `p ≡ 1 (mod 4)`:
`A(p)² + B(p)² = p`. -/
theorem fermat_witness {p : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (h : Γ ⊢[PRAAx] (p ≐ two) ⋎ (rem p (two * two) ≐ one)) :
    Γ ⊢[PRAAx] Aw p * Aw p + Bw p * Bw p ≐ p := by
  refine .orE h ?_ ?_
  · have ep : ((p ≐ two) :: Γ) ⊢[PRAAx] p ≐ two := Prf.hyp0
    have e1 := eqb_of_eq ep
    have m0 := (congrMonus (.eqRefl (one : PTm n)) e1).eqTrans (monus_self one)
    exact two_case e1 m0 ep
  · have hm : ((rem p (two * two) ≐ one) :: Γ) ⊢[PRAAx] rem p (two * two) ≐ one := Prf.hyp0
    have pr := mod4_parities hm
    have e0 : ((rem p (two * two) ≐ one) :: Γ) ⊢[PRAAx] eqb p two ≐ zero := by
      refine .orE (eqb_cases p two) Prf.hyp0 ?_
      have ep := eq_of_eqb (Prf.hyp0 (Γ := (rem p (two * two) ≐ one) :: Γ) (φ := eqb p two ≐ one))
      exact one_ne_zero _ ((Prf.andE₁ pr).wk.eqSymm.eqTrans ((congrAp1 parF ep).eqTrans par_two))
    have m1 := (congrMonus (.eqRefl (one : PTm n)) e0).eqTrans (monus_zero one)
    exact odd_case e0 m1 (two_squares_of_mod4 hp.wk (Prf.andE₁ pr) (Prf.andE₂ pr))

/-! ## The converse -/

/-- A prime other than `2` is odd. -/
theorem odd_of_prime_ne_two {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hne : Γ ⊢[PRAAx] neg (p ≐ two)) :
    Γ ⊢[PRAAx] par p ≐ one := by
  refine .orE (par_cases p) ?_ Prf.hyp0
  have ep : ((par p ≐ zero) :: Γ) ⊢[PRAAx] p ≐ two * half p :=
    (half_par p).eqTrans ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _))
  exact .botE _ (.impE hne.wk (prime_eq_of_dvd hp.wk (le_refl two) (dvd_of_eq ep)).eqSymm)

theorem ee_alg {a b p a' b' : PTm n} (ea : Γ ⊢[PRAAx] a ≐ two * a') (eb : Γ ⊢[PRAAx] b ≐ two * b')
    (e : Γ ⊢[PRAAx] a * a + b * b ≐ p) : Γ ⊢[PRAAx] p ≐ two * (two * (a' * a') + two * (b' * b')) := by
  ipra_lc -natEq e + (𝔞 a + 2 * 𝔞 a') * natEq ea + (𝔞 b + 2 * 𝔞 b') * natEq eb

theorem oo_alg {a b p a' b' : PTm n} (ea : Γ ⊢[PRAAx] a ≐ two * a' + one)
    (eb : Γ ⊢[PRAAx] b ≐ two * b' + one) (e : Γ ⊢[PRAAx] a * a + b * b ≐ p) :
    Γ ⊢[PRAAx] p ≐ two * (two * (a' * a') + two * a' + two * (b' * b') + two * b' + one) := by
  ipra_lc -natEq e + (𝔞 a + 2 * 𝔞 a' + 1) * natEq ea + (𝔞 b + 2 * 𝔞 b' + 1) * natEq eb

theorem eo_alg {a b p a' b' : PTm n} (ea : Γ ⊢[PRAAx] a ≐ two * a') (eb : Γ ⊢[PRAAx] b ≐ two * b' + one)
    (e : Γ ⊢[PRAAx] a * a + b * b ≐ p) :
    Γ ⊢[PRAAx] p ≐ (two * two) * (a' * a' + b' * b' + b') + one := by
  ipra_lc -natEq e + (𝔞 a + 2 * 𝔞 a') * natEq ea + (𝔞 b + 2 * 𝔞 b' + 1) * natEq eb

theorem one_lt_four : Γ ⊢[PRAAx] lt (one : PTm n) (two * two) :=
  le_of_eq_add (d := two) (by ipra_ring)

/-- An even number is not odd. -/
theorem even_absurd {p c : PTm n} (φ : Fm PTm n) (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (e : Γ ⊢[PRAAx] p ≐ two * c) : Γ ⊢[PRAAx] φ :=
  one_ne_zero φ (hodd.eqSymm.eqTrans ((congrAp1 parF e).eqTrans (par_double c)))

/-- An odd sum of two squares is `≡ 1 (mod 4)`. -/
theorem mod4_of_squares {p a b : PTm n} (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (e : Γ ⊢[PRAAx] a * a + b * b ≐ p) : Γ ⊢[PRAAx] rem p (two * two) ≐ one := by
  refine .orE (even_or_odd a) ?_ ?_
  · refine .orE (even_or_odd b) ?_ ?_
    · exact even_absurd _ hodd.wk.wk (ee_alg Prf.hyp1 Prf.hyp0 e.wk.wk)
    · exact Prf.andE₂ (dmu four_pos (eo_alg Prf.hyp1 Prf.hyp0 e.wk.wk) one_lt_four)
  · refine .orE (even_or_odd b) ?_ ?_
    · exact Prf.andE₂ (dmu four_pos (eo_alg Prf.hyp0 Prf.hyp1 ((add_comm _ _).eqTrans e.wk.wk)) one_lt_four)
    · exact even_absurd _ hodd.wk.wk (oo_alg Prf.hyp1 Prf.hyp0 e.wk.wk)

/-- The converse of `thm:main`: a prime `p = a² + b²` is `2` or `≡ 1 (mod 4)`. -/
theorem fermat_converse_open {p a b : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (e : Γ ⊢[PRAAx] a * a + b * b ≐ p) : Γ ⊢[PRAAx] (p ≐ two) ⋎ (rem p (two * two) ≐ one) := by
  refine .orE (eqb_cases p two) ?_ (.orI₁ (eq_of_eqb Prf.hyp0))
  have e0 : ((eqb p two ≐ zero) :: Γ) ⊢[PRAAx] eqb p two ≐ zero := Prf.hyp0
  have hne : ((eqb p two ≐ zero) :: Γ) ⊢[PRAAx] neg (p ≐ two) :=
    .impI (one_ne_zero _ ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans e0.wk))
  exact .orI₂ (mod4_of_squares (odd_of_prime_ne_two hp.wk hne) e.wk)

/-! ## The closed sentences -/

/-- `∀ p. prime p → (p = 2 ∨ p ≡ 1 (mod 4)) → A(p)² + B(p)² = p`. -/
abbrev forwardSentence : Fm PTm 0 :=
  univ 1 (prime (var 0) ⟶ ((var 0 ≐ two) ⋎ (rem (var 0) (two * two) ≐ one)) ⟶
    (Aw (var 0) * Aw (var 0) + Bw (var 0) * Bw (var 0) ≐ var 0))

/-- `∀ a b p. prime p → a² + b² = p → p = 2 ∨ p ≡ 1 (mod 4)`; variables `0 = p`, `1 = a`, `2 = b`. -/
abbrev converseSentence : Fm PTm 0 :=
  univ 3 (prime (var 0) ⟶ (var 1 * var 1 + var 2 * var 2 ≐ var 0) ⟶
    ((var 0 ≐ two) ⋎ (rem (var 0) (two * two) ≐ one)))

/-- Fermat's theorem, existence with witnesses, as a closed sentence of iPRA. -/
theorem fermat_forward : ([] : List (Fm PTm 0)) ⊢[PRAAx] forwardSentence :=
  closeUniv 1 (.impI (.impI (fermat_witness Prf.hyp1 Prf.hyp0)))

/-- Fermat's theorem, the converse, as a closed sentence of iPRA. -/
theorem fermat_converse : ([] : List (Fm PTm 0)) ⊢[PRAAx] converseSentence :=
  closeUniv 3 (.impI (.impI (fermat_converse_open Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.DiophantineNumberTheory.FermatTwoSquares

export_ipra DiophantineNumberTheory.FermatTwoSquares (odd_of_prime_ne_two)
