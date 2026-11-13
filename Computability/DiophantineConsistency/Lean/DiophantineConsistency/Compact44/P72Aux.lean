import DiophantineConsistency.Compact44.P72Main
import DiophantineConsistency.ArithmeticPellHalfIndex

/-! # P13, section 6: the auxiliary norm

Use the §4 data `f = f0 + j` and `q = 1 + β(3j+1)`. The registers then factor
as `Nf = 3βf`, `Vhat = L·V` and `yhat = L(V+u)`, where `L = β(3β)²` and
`V = f²(Tc − R) − c`. So `Aa = 0` reads

  `(V+u)² − Δ(f²−1)((V+u)² − V²) = 1`.

With `z = |V|`, `y = |V+u|` and `Qa = Δ(f²−1)`, this is the form
`Qa·z² + y² = 1 + Qa·y²` that the signed half-index lemma consumes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace P72Aux
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs ArithmeticPellHalfIndex
open P72Graph P72Root
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ι_absdiff_sq (x y : V) :
    ι (absdiff x y) * ι (absdiff x y) = (ι x - ι y) * (ι x - ι y) :=
  ι_magnitude_sq x y

theorem aux_norm (p : Fin 4 → ℕ) (v : Fin 13 → V) (hv : ∀ j, 0 < v j)
    (hb : 0 < (p 0 : V)) (f j : V) (hf : f = v 3 + j)
    (hq : v 0 + (v 2 + v 1) = 1 + (p 0 : V) * (3 * j + 1))
    (hz : InternalZero (graph (fun j => (p j : ℤ))).Aa v) :
    let q : V := v 0 + (v 2 + v 1)
    let k : V := v 9 + v 10
    let c : V := v 9 + v 7 * k
    let a : V := v 6 * v 7 + v 7
    let Δ : V := (3 + 4 * a) + a * a
    let R : V := ((q - 1) * (q - v 0) + v 1) * (q * q - 1) +
      ((p 2 : V) + (p 3 : V) * q) * (3 * j + 1)
    let Vp : V := f * f * (v 5 * c)
    let Vn : V := f * f * R + c
    let Qa : V := Δ * (f * f - 1)
    Qa * (absdiff Vp Vn * absdiff Vp Vn) + absdiff (Vp + v 11) Vn * absdiff (Vp + v 11) Vn =
      1 + Qa * (absdiff (Vp + v 11) Vn * absdiff (Vp + v 11) Vn) := by
  intro q k c a Δ R Vp Vn Qa
  set w : Fin 13 → DiffRing V := fun j => ι (v j) with hw
  have hq1 : 1 ≤ q := pos_iff_one_le.mp (add_pos_of_pos_of_nonneg (hv 0) (Arithmetic.zero_le _))
  have hqF : v 0 ≤ q := le_add_of_nonneg_right (Arithmetic.zero_le _)
  have hqq1 : 1 ≤ q * q := one_le_mul_of_one_le_of_one_le hq1 hq1
  have hf1 : 1 ≤ f * f := by
    have : 1 ≤ f := by rw [hf]; exact le_trans (pos_iff_one_le.mp (hv 3)) (le_add_of_nonneg_right (Arithmetic.zero_le _))
    exact one_le_mul_of_one_le_of_one_le this this
  have cq : (vals (fun j => (p j : ℤ)) w).q = ι q := by simp only [vals, hw, q, map_add]
  have hqι : ι q = 1 + ι (p 0 : V) * (3 * ι j + 1) := by
    have h : ι q = ι (1 + (p 0 : V) * (3 * j + 1)) := congrArg ι hq
    rw [h]; simp [map_add, map_mul, map_ofNat]
  have cR : (vals (fun j => (p j : ℤ)) w).Rhat = ι (p 0 : V) * ι R := by
    have e1 : ι (q - 1) = ι q - 1 := by simpa using ι_tsub (V := V) hq1
    have e2 : ι (q - v 0) = ι q - ι (v 0) := ι_tsub hqF
    have e3 : ι (q * q - 1) = ι (q * q) - 1 := by simpa using ι_tsub (V := V) hqq1
    have cqm : ι q - 1 = ι (p 0 : V) * (3 * ι j + 1) := by rw [hqι]; ring
    simp only [vals, R, map_add, map_mul, map_one, map_ofNat, e1, e2, e3, cast_port]
    rw [← cq]
    simp only [vals, hw]
    rw [show ι (v 0) + (ι (v 2) + ι (v 1)) - 1 = ι (p 0 : V) * (3 * ι j + 1) from by
      rw [← cqm, ← cq]; simp only [vals, hw]]
    ring
  have cNf : (vals (fun j => (p j : ℤ)) w).Nf = 3 * ι (p 0 : V) * ι f := by
    simp only [vals, hw, cast_port]
    rw [show ι (v 0) + (ι (v 2) + ι (v 1)) = ι q from (cq.symm.trans (by simp only [vals, hw])).symm]
    rw [hqι, hf, map_add]
    ring
  have cc : (vals (fun j => (p j : ℤ)) w).c = ι c := by simp only [vals, hw, c, k, map_add, map_mul]
  have cD : (vals (fun j => (p j : ℤ)) w).Delta = ι Δ := by
    simp only [vals, hw, Δ, a, map_add, map_mul, map_ofNat]
  let Zr : DiffRing V := ι Vp - ι Vn
  have cV : (vals (fun j => (p j : ℤ)) w).Vhat = ι (p 0 : V) * ((3 * ι (p 0 : V)) * (3 * ι (p 0 : V))) * Zr := by
    have hV := show (vals (fun j => (p j : ℤ)) w).Vhat =
        ((vals (fun j => (p j : ℤ)) w).Nf * (vals (fun j => (p j : ℤ)) w).Nf) *
          (w 5 * (ι (p 0 : V) * (vals (fun j => (p j : ℤ)) w).c) - (vals (fun j => (p j : ℤ)) w).Rhat) -
          (ι (p 0 : V) * ((3 * ι (p 0 : V)) * (3 * ι (p 0 : V)))) * (vals (fun j => (p j : ℤ)) w).c
      from by simp only [vals, cast_port]
    rw [hV, cNf, cc, cR]
    simp only [Zr, Vp, Vn, hw, map_add, map_mul]
    ring
  have cY : (vals (fun j => (p j : ℤ)) w).yhat =
      ι (p 0 : V) * ((3 * ι (p 0 : V)) * (3 * ι (p 0 : V))) * (Zr + ι (v 11)) := by
    have hY := show (vals (fun j => (p j : ℤ)) w).yhat =
        (vals (fun j => (p j : ℤ)) w).Vhat + (ι (p 0 : V) * ((3 * ι (p 0 : V)) * (3 * ι (p 0 : V)))) * w 11
      from by simp only [vals, cast_port]
    rw [hY, cV]; simp only [hw]; ring
  rw [internalZero_iff, Aa_eval, cY, cV, cNf, cD, cast_port] at hz
  have hβ : (0 : DiffRing V) < ι (p 0 : V) := by
    have h := (ι_lt_ι (V := V)).mpr hb
    rwa [map_zero] at h
  have hne : (3 * ι (p 0 : V)) * (3 * ι (p 0 : V)) * ((ι (p 0 : V) * ((3 * ι (p 0 : V)) * (3 * ι (p 0 : V)))) *
      (ι (p 0 : V) * ((3 * ι (p 0 : V)) * (3 * ι (p 0 : V))))) ≠ 0 := by positivity
  have hcore : (Zr + ι (v 11)) * (Zr + ι (v 11)) -
      ι Δ * (ι f * ι f - 1) * ((Zr + ι (v 11)) * (Zr + ι (v 11)) - Zr * Zr) = 1 := by
    apply mul_left_cancel₀ hne
    linear_combination hz
  have eQa : ι Qa = ι Δ * (ι f * ι f - 1) := by
    simp only [Qa, map_mul]; rw [ι_tsub hf1]; simp [map_mul]
  apply ι_injective
  simp only [map_add, map_mul, map_one, ι_absdiff_sq, eQa]
  simp only [Zr] at hcore ⊢
  linear_combination hcore

end P72Aux

#print axioms P72Aux.aux_norm
