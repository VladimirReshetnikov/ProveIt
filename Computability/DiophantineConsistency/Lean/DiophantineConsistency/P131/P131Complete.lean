import DiophantineConsistency.P131.P131Value
import DiophantineConsistency.P138.P138Complete

/-! # Completeness of package 131's two-root 810/112 equation

From an internal halt `first (run T) = 0` of machine 215, in every model `V` of `𝗜𝚺₁`, this
module produces an integer zero `x : Fin 11 → DiffRing V` of `P131Value.value portsR`
(`complete`), following `TWO_ROOT_PROOF.md` §7. The front is package 138's, so the canonical
record, the guard Pell pair and the residue step are reused unchanged:

1. the canonical record `Cn` (`P138Canonical.canonical`), fixing `x 0, x 1, x 2, x 3, x 5, x 6,
   x 8`;
2. the guard Pell pair `s, g` (`P138Guard.guard`), so `x 10 = s` and `P = p0²` with `p0 = τ g`
   (package 138 multiplies by the main norm, `p0 = d τ g`; this form does not);
3. the interpolation `r, f` (`interp`): `x 4 = r`, the strong pair `I = ψ_A(n0) = p0 c² r`
   (no factor `A`, since `U = r c²` here), `Df = f²`; for every residue target `a0` a value
   `x 7 = T` with `s r ∣ T − a0`, an auxiliary ordinate `y` and the value `Vv` of the register
   `V`, with `Q Vv² − (Q − 1) y² = 1`;
4. a root `t` of `π(t) = (t² + 3)(t³ − 19)` modulo `s r` (`ZRowsIntersective19.root`), target
   `a0 = t − κ`, exact quotient `e₀` (`P138Complete.shifted_root`), `Ac = S H⁴ e₀`;
5. `x 9 = n = H⁴e₀ + y + p0 f − Vv`. The register `V` does not read `x 9`, and `interp` exports
   its value, so the definition is not circular. Then `Z = S (n + V) − Ac = S (y + p0 f)`;
6. `value_of_roots`: with `Z = S (y + G)`, `P Df = G²` and `Q V² − (Q − 1) y² = 1`, both square
   roots of the two-root norm are taken with the sign `+` and the output vanishes.

The equation of the package has the short index `k = R + 1 + h·4q⁴`; the canonical record has
the native one, `k = R + 1 + hE`. `value_update` transfers the zero by the substitution
`h ↦ h (3w+1)(2v+1)`, a polynomial identity, as `P138Value.valueS_update` does for package 138.

No division is used: `e₀` and `T` are quotients of proved divisibilities in `DiffRing V`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.P131Complete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Value P138Ports P138Canonical ArithmeticPellRecurrence
open ZRowsLinearInterpolation
open P131Value (backK)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

/-! ## Two polynomial identities -/

section Generic
variable {𝔸 : Type*} [CommRing 𝔸]

/-- **The two-root output vanishes at a pair of roots.** If `Z = S (y + G)` with `P·Df = G²`
and the auxiliary norm `Q V² − (Q − 1) y² = 1`, then the output is zero: with
`E = Q V² − (Q − 1) y² − 1` it equals `S⁴ E (E − 4 (Q − 1) G (y + G))`. -/
theorem value_of_roots (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) (κ y G : 𝔸)
    (hZ : (backK p x κ).Z = (regsK p x κ).S * (y + G))
    (hG : (regsK p x κ).P * (backK p x κ).Df = G ^ 2)
    (hy : (backK p x κ).Q * (backK p x κ).V ^ 2 - ((backK p x κ).Q - 1) * y ^ 2 = 1) :
    P131Value.valueK p x κ = 0 := by
  rw [P131Value.value_norm, hZ, hG, P131Value.Cy_eq, P131Value.delta_def]
  linear_combination ((regsK p x κ).S ^ 4 *
    (((backK p x κ).Q * (backK p x κ).V ^ 2 - ((backK p x κ).Q - 1) * y ^ 2 - 1) -
      4 * ((backK p x κ).Q - 1) * G * (y + G))) * hy

/-- **The short value at `h (3w+1)(2v+1)` is the value at the native index**, as a polynomial
identity: `E = 4q⁴ (3w+1)(2v+1)` makes the two `k` equal, and nothing else reads `x 3`. -/
theorem value_update (p : Fin 6 → 𝔸) (x : Fin 11 → 𝔸) :
    P131Value.value p (Function.update x 3 (x 3 * ((3 * x 6 + 1) * (2 * x 5 + 1)))) =
      P131Value.valueK p x (kN p x) := by
  have hk : kS p (Function.update x 3 (x 3 * ((3 * x 6 + 1) * (2 * x 5 + 1)))) = kN p x := by
    rw [kS_eq _ _ 0, regsK_update, Function.update_self, kN_eq p x 0, E_eq_short p x 0]; ring
  show P131Value.valueK p _ (kS p _) = P131Value.valueK p x (kN p x)
  rw [hk, P131Value.valueK_update]

end Generic

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The interpolation at the canonical data -/

/-- **The supported-modulus interpolation for the two-root back end.** At a guard pair `s, g`
(`P = (τ g)²` at every matching point with `x 10 = s`) there are `r, f > 0` such that every
residue target `a0` modulo `s r` is hit by a value `T` of `x 7`, with an auxiliary ordinate `y`
and the common value `Vv` of the register `V`: at every matching point with `x 4 = r`,
`x 7 = T`, `x 10 = s`, `Df = f²`, `V = Vv` and `Q Vv² − (Q − 1) y² = 1`. -/
theorem interp (Cn : Canonical V) (s g : V) (hs : 0 < s) (hg : 0 < g)
    (hP : ∀ x : Fin 11 → DiffRing V, Matches Cn x → x 10 = ι s →
      (regs (portsR (V := V)) x).P = (ι Cn.τ * ι g) ^ 2) :
    ∃ r f : V, 0 < r ∧ ∀ a0 : DiffRing V, ∃ T y Vv : DiffRing V,
      (ι (s * r) : DiffRing V) ∣ T - a0 ∧
      ∀ x : Fin 11 → DiffRing V, Matches Cn x → x 4 = ι r → x 7 = T → x 10 = ι s →
        (backK (portsR (V := V)) x (kN portsR x)).Df = ι f ^ 2 ∧
        (backK (portsR (V := V)) x (kN portsR x)).V = Vv ∧
        (backK (portsR (V := V)) x (kN portsR x)).Q * Vv ^ 2 -
          ((backK (portsR (V := V)) x (kN portsR x)).Q - 1) * y ^ 2 = 1 := by
  have hp0 : 0 < Cn.τ * g := mul_pos (P138Interp.τ_pos Cn) hg
  have hc := P138Interp.c_pos Cn
  have hN : 0 < 4 * s * (Cn.τ * g * Cn.c * Cn.c) :=
    mul_pos (mul_pos (by norm_num) hs) (mul_pos (mul_pos hp0 hc) hc)
  obtain ⟨n0, hn0, hNI, hall⟩ := ZRowsLinearInterpolation.supported_interpolation Cn.a Cn.R
    (4 * s * (Cn.τ * g * Cn.c * Cn.c)) (P138Interp.R_mod_four Cn) hN
    ⟨s * (Cn.τ * g * Cn.c * Cn.c), by ring⟩
  obtain ⟨m, hm⟩ := hNI
  have hI : ycoord n0 Cn.a = Cn.τ * g * Cn.c * Cn.c * (4 * s * m) := by
    rw [hm]; ring
  have hIpos : 0 < ycoord n0 Cn.a := lt_of_lt_of_le hn0 (time_le_y n0 Cn.a)
  have hm0 : 0 < m := by
    rcases (Arithmetic.zero_le m).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero] at hm
      exact (ne_of_gt hIpos) hm
  have hr : 0 < 4 * s * m := mul_pos (mul_pos (by norm_num) hs) hm0
  refine ⟨4 * s * m, xcoord n0 Cn.a, hr, ?_⟩
  intro a0
  have hM : 0 < Cn.τ * g * s * (4 * s * m) := mul_pos (mul_pos hp0 hs) hr
  have hMI : Cn.τ * g * s * (4 * s * m) ∣ ycoord n0 Cn.a * ycoord n0 Cn.a :=
    ⟨Cn.τ * g * Cn.c * Cn.c * Cn.c * Cn.c * (4 * m), by rw [hI]; ring⟩
  obtain ⟨Told, y, hdvd, hnorm⟩ := hall _ hM hMI (ι (Cn.τ * g) * a0)
  -- `T_old = p0·T`
  have hMsplit : (ι (Cn.τ * g * s * (4 * s * m)) : DiffRing V) =
      ι (Cn.τ * g) * ι (s * (4 * s * m)) := by
    simp only [map_mul]; ring
  rw [hMsplit] at hdvd
  have hp0dvd : (ι (Cn.τ * g) : DiffRing V) ∣ Told := by
    have h1 : (ι (Cn.τ * g) : DiffRing V) ∣ Told - ι (Cn.τ * g) * a0 :=
      dvd_trans (dvd_mul_right _ _) hdvd
    have h2 := dvd_add h1 (dvd_mul_right (ι (Cn.τ * g) : DiffRing V) a0)
    rwa [sub_add_cancel] at h2
  obtain ⟨T, hT⟩ := hp0dvd
  have hp0ne : (ι (Cn.τ * g) : DiffRing V) ≠ 0 := by
    have hlt : (0 : DiffRing V) < ι (Cn.τ * g) := by
      rw [← map_zero (ι (V := V))]; exact ι_lt_ι.mpr hp0
    exact ne_of_gt hlt
  refine ⟨T, y, ι (xcoord n0 Cn.a) ^ 2 *
    (ι Cn.c - ι Cn.R + 4 * (ι (4 * s * m) * ι Cn.c ^ 2) * (ι Cn.τ * ι g) ^ 2 * T) - ι Cn.c,
    ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hdvd
    refine ⟨q, ?_⟩
    have key : ι (Cn.τ * g) * (T - a0 - ι (s * (4 * s * m)) * q) = 0 := by
      rw [hT] at hq
      linear_combination hq
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hp0ne
    · exact sub_eq_zero.mp h
  · intro x hx hx4 hx7 hx10
    have hPx := hP x hx hx10
    have eD := reg_Delta Cn hx
    have eR := reg_R Cn hx
    -- the back-end closed forms, over the native registers
    have dfeq : (backK (portsR (V := V)) x (kN portsR x)).Df =
        1 + (regs (portsR (V := V)) x).Delta *
          (backK (portsR (V := V)) x (kN portsR x)).U ^ 2 * (regs (portsR (V := V)) x).P :=
      P131Value.Df_eq _ _ _
    have veq : (backK (portsR (V := V)) x (kN portsR x)).V =
        (backK (portsR (V := V)) x (kN portsR x)).Df *
          (x 8 - (regs (portsR (V := V)) x).R +
            4 * (backK (portsR (V := V)) x (kN portsR x)).U * (regs (portsR (V := V)) x).P * x 7) -
          x 8 :=
      P131Value.V_eq _ _ _
    have qeq : (backK (portsR (V := V)) x (kN portsR x)).Q =
        (regs (portsR (V := V)) x).Delta ^ 2 *
          (backK (portsR (V := V)) x (kN portsR x)).U ^ 2 * (regs (portsR (V := V)) x).P :=
      P131Value.Q_eq _ _ _
    have ueq : (backK (portsR (V := V)) x (kN portsR x)).U = x 4 * x 8 ^ 2 :=
      P131Value.U_eq _ _ _
    -- ring forms of the strong pair
    have HI := congrArg (ι (V := V)) hI
    have Nf := congrArg (ι (V := V)) (norm n0 Cn.a)
    simp only [map_add, map_mul, map_ofNat, map_one] at HI Nf
    unfold delta at Nf
    simp only [map_add, map_mul, map_ofNat, map_one] at Nf
    rw [HI] at Nf
    have hDf : (backK (portsR (V := V)) x (kN portsR x)).Df = ι (xcoord n0 Cn.a) ^ 2 := by
      rw [dfeq, ueq, eD, hPx, hx.x8, hx4]
      simp only [map_mul, map_ofNat]
      linear_combination (-1 : DiffRing V) * Nf
    have hV : (backK (portsR (V := V)) x (kN portsR x)).V = ι (xcoord n0 Cn.a) ^ 2 *
        (ι Cn.c - ι Cn.R + 4 * (ι (4 * s * m) * ι Cn.c ^ 2) * (ι Cn.τ * ι g) ^ 2 * T) -
          ι Cn.c := by
      rw [veq, hDf, ueq, eR, hPx, hx.x8, hx7, hx4]
    refine ⟨hDf, hV, ?_⟩
    rw [qeq, ueq, eD, hPx, hx.x8, hx4]
    rw [hT, HI] at hnorm
    unfold delta at hnorm
    rw [← Cn.c_main] at hnorm
    simp only [map_add, map_mul, map_ofNat, map_one] at hnorm ⊢
    linear_combination hnorm

/-! ## The assembly -/

/-- **Completeness at the native index**: an internal halt of machine 215 gives an integer zero
of the two-root output with the `k` slot `R + 1 + hE`. -/
theorem complete_native (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 11 → DiffRing V, P131Value.valueK portsR x (kN portsR x) = 0 := by
  obtain ⟨Cn⟩ := canonical T hT
  obtain ⟨_Dn, s, g, _hDn, hs, hg, _hgn, _hD4, hguard⟩ := P138Guard.guard Cn
  obtain ⟨r, f, hr, hall⟩ := interp Cn s g hs hg (fun x hx h10 => (hguard x hx h10).1)
  obtain ⟨t, ht⟩ := ZRowsIntersective19.root (s * r) (mul_pos hs hr)
  obtain ⟨u7, y, Vv, hu7, hreg⟩ := hall (t - Cn.κ)
  obtain ⟨e0, he0⟩ := P138Complete.shifted_root ht hu7
  rw [map_mul] at he0
  -- the assembly coordinate `n = H⁴ e₀ + y + p0 f − V`
  obtain ⟨x, hxdef⟩ : ∃ x : Fin 11 → DiffRing V, x =
      ![ι Cn.j, ι Cn.C, ι Cn.z, ι Cn.h, ι r, ι Cn.v, ι Cn.w, u7, ι Cn.c,
        (4 * ι Cn.a + 3) ^ 4 * e0 + y + ι Cn.τ * ι g * ι f - Vv, ι s] := ⟨_, rfl⟩
  have hx : Matches Cn x := by subst hxdef; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hx4 : x 4 = ι r := by subst hxdef; rfl
  have hx7 : x 7 = u7 := by subst hxdef; rfl
  have hx9 : x 9 = (4 * ι Cn.a + 3) ^ 4 * e0 + y + ι Cn.τ * ι g * ι f - Vv := by
    subst hxdef; rfl
  have hx10 : x 10 = ι s := by subst hxdef; rfl
  refine ⟨x, ?_⟩
  obtain ⟨hDf, hV, hnorm⟩ := hreg x hx hx4 hx7 hx10
  have hPx := (hguard x hx hx10).1
  have hS : (regs (portsR (V := V)) x).S = ι s * ι r * (4 * ι Cn.a + 3) := by
    rw [S_eq, hx10, hx4, reg_H Cn hx]
  have hAc : (regs (portsR (V := V)) x).Ac = (4 * ι Cn.a + 3) ^ 5 * (ι s * ι r) * e0 := by
    rw [Ac_eq, zc_eq, reg_K Cn hx, hx7, reg_H Cn hx]
    linear_combination (4 * ι Cn.a + 3) ^ 5 * he0
  have zdef : (backK (portsR (V := V)) x (kN portsR x)).Z =
      (regs (portsR (V := V)) x).S * (x 9 + (backK (portsR (V := V)) x (kN portsR x)).V) -
        (regs (portsR (V := V)) x).Ac :=
    P131Value.Z_def _ _ _
  have hZ : (backK (portsR (V := V)) x (kN portsR x)).Z =
      (regs (portsR (V := V)) x).S * (y + ι Cn.τ * ι g * ι f) := by
    rw [zdef, hx9, hV]
    linear_combination (4 * ι Cn.a + 3) ^ 4 * e0 * hS - hAc
  have hG : (regs (portsR (V := V)) x).P * (backK (portsR (V := V)) x (kN portsR x)).Df =
      (ι Cn.τ * ι g * ι f) ^ 2 := by
    rw [hPx, hDf]; ring
  have hy : (backK (portsR (V := V)) x (kN portsR x)).Q *
      (backK (portsR (V := V)) x (kN portsR x)).V ^ 2 -
        ((backK (portsR (V := V)) x (kN portsR x)).Q - 1) * y ^ 2 = 1 := by
    rw [hV]; exact hnorm
  exact value_of_roots portsR x (kN portsR x) y (ι Cn.τ * ι g * ι f) hZ hG hy

/-- **Completeness.** An internal halt of machine 215 gives an integer zero of the 810/112
polynomial at the six ports: the zero of `complete_native`, with `x 3 = h` replaced by
`h (3w+1)(2v+1)`. -/
theorem complete (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 11 → DiffRing V, P131Value.value portsR x = 0 := by
  obtain ⟨x, hx⟩ := complete_native T hT
  exact ⟨Function.update x 3 (x 3 * ((3 * x 6 + 1) * (2 * x 5 + 1))),
    (value_update portsR x).trans hx⟩

#print axioms value_of_roots
#print axioms value_update
#print axioms interp
#print axioms complete_native
#print axioms complete

end DiophantineConsistency.P131Complete
