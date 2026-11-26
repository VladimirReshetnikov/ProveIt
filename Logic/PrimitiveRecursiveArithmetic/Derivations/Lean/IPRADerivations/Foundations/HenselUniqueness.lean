import IPRADerivations.Foundations.HenselIteration
import IPRADerivations.Foundations.FilteredLiftingStep
import IPRADerivations.Core.Header

/-!
# Uniqueness of the filtered lift for one polynomial equation over `ℤ`

Packet: `foundations/ipra_coherent_methods_2026-11-15`, `paper/sections/04_lifting.tex`, Theorem
`thm:filtered-lifting` ("Finite filtered lifting"), the uniqueness clause: `b_{N−1}` "is the unique root `x`
satisfying `x − a ∈ (F^1 B)^m`". "`0 = P(x) − P(y) = J(y) d + R` ... gives
`d = (I − U J(a)) d − U (J(y) − J(a)) d − U R`" (2), so `d ∈ F^k` gives `d ∈ F^{k+1}`.

For one equation `P : PE 1` over the integers with `F^k = q^k ℤ`, roots modulo `q^N`:

* `toZ_ev_congr`: evaluation respects equality of the arguments;
* `num_add`, `pw_split`: `q^{(j+2)+E} = q · q^{j+1} · q^E`;
* `unique_step`: if `P(x), P(y) ∈ q^N`, `y − a = q σ`, `1 − U J(a) = q e`, `x − y = q^{K'+1} ω` and
  `q^N = q · q^{K'+1} · q_r`, then `x − y ∈ q^{K'+2}` with an explicit witness: the Taylor identity at `y`
  (`FilteredTaylor.taylor_exact`, `P(x) − P(y) = J(y) d + d² τ`), the difference witness of `J(y) − J(a)`
  (`FilteredTaylor.diff_exact`), and the ring identity `FilteredLiftingStep.hensel_unique_ring`;
* `unique_root`: for `x ≡ a ≡ y (mod q)` with `P(x) ≡ P(y) ≡ 0 (mod q^N)`, `x ≡ y (mod q^{j+1})` for every
  `j + 1 ≤ N`; at `j = N − 1`, `x ≡ y (mod q^N)`: the root of `HenselIteration.invariant` is unique.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.HenselUniqueness

open_ipra
open LeanProofs.IPRA.Analysis.PolynomialRemainder (PE ev dv)
open LeanProofs.IPRA.Foundations.FilteredTaylor (pd tq ls taylor_exact diff_exact dv_eq)
open LeanProofs.IPRA.Foundations.HenselIteration (pt jac)
open LeanProofs.IPRA.Foundations.FilteredLiftingStep (hensel_unique_ring)

variable {k : ℕ} {Γ : List (Fm PTm k)}

set_option hygiene false in
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- Evaluation respects equality of the arguments. -/
theorem toZ_ev_congr {d : ℕ} {x y : Fin d → ZT k} (h : ∀ i, ZT.toZ Γ (x i) = ZT.toZ Γ (y i)) (e : PE d) :
    ZT.toZ Γ (ev e x) = ZT.toZ Γ (ev e y) := by
  induction e with
  | const p q => rfl
  | var i => exact h i
  | add f g ihf ihg => simp only [ev, ZT.toZ_add, ihf, ihg]
  | mul f g ihf ihg => simp only [ev, ZT.toZ_mul, ihf, ihg]

/-- `num (a + b) = num a + num b`. -/
theorem num_add (a : ℕ) : (b : ℕ) → Γ ⊢[PRAAx] (num (a + b) : PTm k) ≐ num a + num b
  | 0 => (add_zero _).eqSymm
  | b + 1 => (congrSucc (num_add a b)).eqTrans (add_succ _ _).eqSymm

/-- `q^{(j+2)+E} = q · q^{j+1} · q^E`. -/
theorem pw_split (q : PTm k) (j E : ℕ) :
    Γ ⊢[PRAAx] pw q (num (j + 2 + E)) ≐ q * pw q (num (j + 1)) * pw q (num E) := by
  have a := natEq ((congrAp2 _ (num_add (Γ := Γ) (j + 2) E) (.eqRefl q)).eqTrans (pw_add q (num (j + 2)) (num E)))
  have b := natEq (pw_succ (Γ := Γ) q (num (j + 1)))
  apply deriveNat; ipra_simps
  rw [a]
  change 𝔞 (pw q (succ (num (j + 1)))) * _ = _
  rw [b]; ring

variable {P : PE 1} {U : ZT k}

/-- One step of the uniqueness argument: `x − y ∈ q^{K'+1}` gives `x − y ∈ q^{K'+2}`. -/
theorem unique_step {a x y σ eW sx sy ω : ZT k} {q Nt K' qr : PTm k}
    (hx : Γ ⊢[PRAAx] ZT.eq (ev P (pt x)) (ZT.ofNat (pw q Nt) * sx))
    (hy : Γ ⊢[PRAAx] ZT.eq (ev P (pt y)) (ZT.ofNat (pw q Nt) * sy))
    (hσ : Γ ⊢[PRAAx] ZT.eq (y + -a) (ZT.ofNat q * σ))
    (hH : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 1 + -(U * jac P a)) (ZT.ofNat q * eW))
    (hd : Γ ⊢[PRAAx] ZT.eq (x + -y) (ZT.ofNat (pw q (succ K')) * ω))
    (hN : Γ ⊢[PRAAx] pw q Nt ≐ q * pw q (succ K') * qr) :
    Γ ⊢[PRAAx] ZT.eq (x + -y) (ZT.ofNat (pw q (succ (succ K'))) *
      (eW * ω + -(U * (σ * ls (pd P 0) (pt y) (pt a) 0) * ω) +
        -(U * ZT.ofNat (pw q K') * ω * ω * tq P (pt y) (pt (x + -y)) 0 0) + U * ZT.ofNat qr * (sx + -sy))) := by
  have ex := ZT.toZ_eq hx
  have ey := ZT.toZ_eq hy
  have eS := ZT.toZ_eq hσ
  have eH := ZT.toZ_eq hH
  have ed := ZT.toZ_eq hd
  have eN := natEq hN
  have eK := natEq (pw_succ (Γ := Γ) q K')
  have eK1 := natEq (pw_succ (Γ := Γ) q (succ K'))
  have eT := taylor_exact (Γ := Γ) (x := pt y) (v := pt (x + -y)) P
  have eD := diff_exact (Γ := Γ) (x := pt y) (y := pt a) (pd P 0)
  have eV := dv_eq (Γ := Γ) (x := pt y) (v := pt (x + -y)) P
  have ec := toZ_ev_congr (Γ := Γ) (x := fun i => pt y i + pt (x + -y) i) (y := pt x)
    (fun _ => by simp only [pt, ZT.toZ_add, ZT.toZ_neg]; ring) P
  simp only [Analysis.PolynomialRemainder.rem, ZT.toZ_sub, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat,
    ZT.toZ_natLit, Nat.cast_one, Fin.sum_univ_one, pt, jac] at ex ey eS eH ed eT eD eV ec
  simp only [Q.mk_mul, map_mul] at eN eK eK1
  -- `J(y) d + d² τ = q^N (s_x − s_y)`
  have hT : ZT.toZ Γ (ev (pd P 0) (pt y)) * ZT.toZ Γ (x + -y) +
      ZT.toZ Γ (x + -y) * ZT.toZ Γ (x + -y) * ZT.toZ Γ (tq P (pt y) (pt (x + -y)) 0 0) =
      𝔞 (pw q Nt) * (ZT.toZ Γ sx - ZT.toZ Γ sy) := by
    simp only [ZT.toZ_add, ZT.toZ_neg, pt]
    rw [ec] at eT
    linear_combination -eT - eV + ex - ey
  have hJ : ZT.toZ Γ (ev (pd P 0) (pt y)) - ZT.toZ Γ (ev (pd P 0) (pt a)) =
      𝔞 q * (ZT.toZ Γ σ * ZT.toZ Γ (ls (pd P 0) (pt y) (pt a) 0)) := by
    linear_combination eD + ZT.toZ Γ (ls (pd P 0) (pt y) (pt a) 0) * eS
  have hH' : 1 - ZT.toZ Γ U * ZT.toZ Γ (ev (pd P 0) (pt a)) = 𝔞 q * ZT.toZ Γ eW := by
    linear_combination eH
  have hd' : ZT.toZ Γ (x + -y) = 𝔞 (pw q (succ K')) * ZT.toZ Γ ω := by
    simp only [ZT.toZ_add, ZT.toZ_neg]; linear_combination ed
  have hq : 𝔞 (pw q (succ K')) = 𝔞 q * 𝔞 (pw q K') := by linear_combination eK
  have hN' : 𝔞 (pw q Nt) = 𝔞 q * 𝔞 (pw q (succ K')) * 𝔞 qr := by linear_combination eN
  have r := hensel_unique_ring hT hH' hJ hd' hq hN'
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat] at r ⊢
  linear_combination r - (ZT.toZ Γ eW * ZT.toZ Γ ω -
      ZT.toZ Γ U * (ZT.toZ Γ σ * ZT.toZ Γ (ls (pd P 0) (pt y) (pt a) 0)) * ZT.toZ Γ ω -
      ZT.toZ Γ U * 𝔞 (pw q K') * ZT.toZ Γ ω * ZT.toZ Γ ω * ZT.toZ Γ (tq P (pt y) (pt (x + -y)) 0 0) +
      ZT.toZ Γ U * 𝔞 qr * (ZT.toZ Γ sx - ZT.toZ Γ sy)) * eK1

/-- Uniqueness: two roots modulo `q^N` congruent to `a` modulo `q` agree modulo `q^{j+1}` for `j + 1 ≤ N`. -/
theorem unique_root {a x y σx σy eW sx sy : ZT k} {q : PTm k} {N : ℕ}
    (hx : Γ ⊢[PRAAx] ZT.eq (ev P (pt x)) (ZT.ofNat (pw q (num N)) * sx))
    (hy : Γ ⊢[PRAAx] ZT.eq (ev P (pt y)) (ZT.ofNat (pw q (num N)) * sy))
    (hσx : Γ ⊢[PRAAx] ZT.eq (x + -a) (ZT.ofNat q * σx))
    (hσy : Γ ⊢[PRAAx] ZT.eq (y + -a) (ZT.ofNat q * σy))
    (hH : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 1 + -(U * jac P a)) (ZT.ofNat q * eW)) :
    ∀ j : ℕ, j + 1 ≤ N → ∃ δ : ZT k, Γ ⊢[PRAAx] ZT.eq (x + -y) (ZT.ofNat (pw q (num (j + 1))) * δ) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨σx + -σy, ZT.derive ?_⟩
    have e1 := ZT.toZ_eq hσx
    have e2 := ZT.toZ_eq hσy
    have e3 := natEq (pw_one (Γ := Γ) q)
    simp only [ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat] at e1 e2 ⊢
    change _ = 𝔞 (pw q one) * _
    linear_combination e1 - e2 - (ZT.toZ Γ σx - ZT.toZ Γ σy) * e3
  | succ j ih =>
    intro hj
    obtain ⟨δ, hδ⟩ := ih (by omega)
    obtain ⟨E, hE⟩ : ∃ E, N = j + 2 + E := ⟨N - (j + 2), by omega⟩
    have hN : Γ ⊢[PRAAx] pw q (num N) ≐ q * pw q (succ (num j)) * pw q (num E) := by
      rw [hE]; exact pw_split q j E
    exact ⟨_, unique_step (K' := num j) hx hy hσy hH hδ hN⟩

open LeanProofs.IPRA.Foundations.HenselIteration (seq wit invariant) in
/-- `cor:filtered-coherence` over `ℤ` (with the identity map): two lifting runs from initial approximations
`a ≡ c (mod q)` with approximate inverses `U`, `U'` give the same root modulo `q^{N+1}`. Different lifts of
the initial approximation or of the inverse give the same root. -/
theorem coherence {a c U' eW eW' w₀ w₀' τ : ZT k} {q : PTm k}
    (hJ : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 1 + -(jac P a * U)) (ZT.ofNat q * eW))
    (hP : Γ ⊢[PRAAx] ZT.eq (ev P (pt a)) (ZT.ofNat q * w₀))
    (hJ' : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 1 + -(jac P c * U')) (ZT.ofNat q * eW'))
    (hP' : Γ ⊢[PRAAx] ZT.eq (ev P (pt c)) (ZT.ofNat q * w₀'))
    (hca : Γ ⊢[PRAAx] ZT.eq (c + -a) (ZT.ofNat q * τ)) (N : ℕ) :
    ∃ δ : ZT k, Γ ⊢[PRAAx] ZT.eq (seq P U a N + -seq P U' c N) (ZT.ofNat (pw q (num (N + 1))) * δ) := by
  have ix := invariant hJ hP N
  have iy := invariant hJ' hP' N
  have hσy : Γ ⊢[PRAAx] ZT.eq (seq P U' c N + -a)
      (ZT.ofNat q * ((wit P U' c eW' w₀' q N).1 + τ)) := by
    refine ZT.derive ?_
    have e1 := ZT.toZ_eq (Prf.andE₁ iy)
    have e2 := ZT.toZ_eq hca
    simp only [ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat] at e1 e2 ⊢
    linear_combination e1 + e2
  have hH : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 1 + -(U * jac P a)) (ZT.ofNat q * eW) := by
    refine ZT.derive ?_
    have e := ZT.toZ_eq hJ
    simp only [ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul] at e ⊢
    linear_combination e
  exact unique_root (Prf.andE₂ ix) (Prf.andE₂ iy) (Prf.andE₁ ix) hσy hH N (Nat.le_refl _)

end LeanProofs.IPRA.Foundations.HenselUniqueness
