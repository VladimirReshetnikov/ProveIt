import DiophantineConsistency.NativeOuterSeedConstruction
import DiophantineConsistency.ThirteenFreshSeed
import DiophantineConsistency.Carrier66Source
import DiophantineConsistency.NativeRankVariation

/-!
# Constructing the positive literal source from calibrated scalar data

The scalar hypotheses are ordinary arithmetic equalities supplied by a
constructed packing and its rank calibration. The two remaining private Pell
norms are constructed freshly. No source solution, polynomial zero, or target
Pell norm is an input. The source high-mask port retains its single beta shift.
-/

namespace DiophantineConsistency.NativePositiveSourceConstruction

open Diophantine Pell NativeOuterSeedConstruction

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Scalar coordinates and the exact bindings needed for the converse map. -/
structure Data (p : Fin 4 → ℤ) (u R : ℕ) where
  J : ℕ
  F : ℕ
  alpha : ℕ
  z : ℕ
  w : ℕ
  C : ℕ
  J_pos : 0 < J
  F_pos : 0 < F
  alpha_pos : 0 < alpha
  z_pos : 0 < z
  w_pos : 0 < w
  C_pos : 0 < C
  q_balance : p 0 * (J : ℤ) + 1 = (2^u : ℕ)
  balance : C+F+alpha = 2^u
  forced_product : w*2^u = 2^R
  transport : (p 1 + (w : ℤ)) * C + ((2^u : ℕ) - (F : ℤ)) -
    (z : ℤ) * ((2^u : ℕ) - (1 : ℤ)) = 1
  rank : NativeRankVariation.windowRank ((2^u : ℕ) : ℤ) C F (p 2) (p 3) J = R

/-- The temporal multiplier need not equal a previously used ordinary shift. -/
theorem forced_product_of_exponent {u R w : ℕ} (huR : u ≤ R)
    (hw : w = 2^(R-u)) : w*2^u = 2^R := by
  rw [hw, ← pow_add, Nat.sub_add_cancel huR]

/-- The literal fifteen parent coordinates; the auxiliary ordinate is positive. -/
def parent {p : Fin 4 → ℤ} {u R : ℕ} (d : Data p u R) (s : Seed u R)
    (f i T y : ℤ) (j : Fin 15) : ℤ :=
  match j.val with
  | 0 => d.J
  | 1 => d.F
  | 2 => d.alpha
  | 3 => d.z
  | 4 => f
  | 5 => s.h
  | 6 => i
  | 7 => T
  | 8 => s.s
  | 9 => d.w
  | 10 => s.tau
  | 11 => s.eta
  | 12 => s.zeta
  | 13 => y
  | _ => s.gamma

theorem parent_pos {p : Fin 4 → ℤ} {u R : ℕ} (d : Data p u R) (s : Seed u R)
    {f i T y : ℤ} (hf : 0 < f) (hi : 0 < i) (hT : 0 < T) (hy : 0 < y) :
    ∀ j, 0 < parent d s f i T y j := by
  intro j
  fin_cases j <;> simp only [parent]
  all_goals first
    | assumption
    | exact_mod_cast d.J_pos
    | exact_mod_cast d.F_pos
    | exact_mod_cast d.alpha_pos
    | exact_mod_cast d.z_pos
    | exact_mod_cast d.w_pos
    | exact_mod_cast s.h_pos
    | exact_mod_cast s.s_pos
    | exact_mod_cast s.tau_pos
    | exact_mod_cast s.eta_pos
    | exact_mod_cast s.zeta_pos
    | exact_mod_cast s.gamma_pos

/-- Every outer block agrees with the constructed seed and calibrated window. -/
theorem parent_blocks {p : Fin 4 → ℤ} {u R : ℕ} (d : Data p u R) (s : Seed u R)
    (f i T y : ℤ) :
    let b := Carrier66.core p (parent d s f i T y)
    b.q = (2^u : ℕ) ∧ b.C = d.C ∧ b.X = (2^R : ℕ) ∧ b.Y = s.Y ∧
    b.k = s.k ∧ b.c = s.c ∧ b.a = s.a ∧ b.delta = (s.a+2 : ℤ)^2-1 ∧
    b.D = s.D ∧ b.rank = R := by
  let v := parent d s f i T y
  let b := Carrier66.core p v
  have hq : b.q = (2^u : ℕ) := d.q_balance
  have hC : b.C = d.C := by
    change b.q - (d.F : ℤ) - d.alpha = d.C
    rw [hq]
    have hh := congrArg (fun n : ℕ => (n : ℤ)) d.balance
    push_cast at hh ⊢
    omega
  have hX : b.X = (2^R : ℕ) := by
    change (d.w : ℤ)*b.q = _
    rw [hq]
    exact_mod_cast d.forced_product
  have hY : b.Y = s.Y := by
    change (s.s : ℤ)*b.q^3 = _
    rw [hq]
    exact_mod_cast s.scale.symm
  have hk : b.k = s.k := by
    change (s.eta : ℤ) + s.zeta = s.k
    exact_mod_cast s.split.symm
  have hc : b.c = s.c := by
    change b.k*b.Y+(s.eta : ℤ) = _
    rw [hk,hY]
    exact_mod_cast s.interval.symm
  have ha : b.a = s.a := by
    change b.X*b.Y+b.Y = _
    rw [hX,hY]
    have hh := congrArg (fun n : ℕ => (n : ℤ)) s.base
    push_cast at hh ⊢
    nlinarith only [hh]
  have hd : b.delta = (s.a+2 : ℤ)^2-1 := by
    change b.a^2+(4*b.a+3) = _
    rw [ha]
    ring
  have hD : b.D = s.D := by
    change b.X+b.a*b.c+(s.gamma : ℤ)*(4*b.a+3) = _
    rw [hX,ha,hc]
    exact_mod_cast s.root.symm
  have hR : b.rank = R := by
    have hh := NativeRankVariation.core_rank p (Carrier66.drop v 1)
    change b.rank = NativeRankVariation.windowRank b.q b.C (d.F : ℤ)
      (p 2) (p 3) d.J at hh
    rw [hh,hq,hC]
    exact d.rank
  exact ⟨hq,hC,hX,hY,hk,hc,ha,hd,hD,hR⟩

/-- A constructed canonical parent, retaining the exact scalar inputs. -/
structure Construction (p : Fin 4 → ℤ) (u R : ℕ) (d : Data p u R) where
  v : Fin 15 → ℤ
  positive : ∀ j, 0 < v j
  canonical : Carrier66.Canonical p v
  scalars : v 0 = d.J ∧ v 1 = d.F ∧ v 2 = d.alpha ∧ v 3 = d.z ∧ v 9 = d.w
  q : (Carrier66.core p v).q = (2^u : ℕ)
  C : (Carrier66.core p v).C = d.C
  rank : (Carrier66.core p v).rank = R

/-- Fresh auxiliary Pell witnesses complete all six canonical factors. -/
theorem exists_construction {p : Fin 4 → ℤ} {u R : ℕ} (d : Data p u R)
    (s : Seed u R) (hR4 : R%4=3) : Nonempty (Construction p u R d) := by
  obtain ⟨f,i,T,V,y,hf,hi,hT,hV,hy,hstrong,hVeq,haux,_,_⟩ :=
    ThirteenFreshSeed.auxiliary_exists (s.a+2) R 1 (by omega) (by decide) hR4
  have hc : (yn (by omega : 1<s.a+2) R : ℤ) = (s.c : ℤ) := by
    exact_mod_cast s.main_index.symm
  simp only [hc,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,one_mul] at hstrong hVeq haux
  let v := parent d s f i T (-y)
  let b := Carrier66.core p v
  obtain ⟨hq,hC,hX,hY,hk,hcc,ha,hd,hD,hR⟩ := parent_blocks d s f i T (-y)
  have hE : b.E = (2^R : ℕ)*(s.Y : ℤ) := by
    change b.X*b.Y = _
    rw [hX,hY]
  have hP : b.P = 1 := by
    rw [Carrier66.first_shape]
    change (s.tau : ℤ)^2 - ((b.E*b.Y)*(b.E*b.Y+1))*b.k^2 = 1
    rw [hE,hY,hk]
    have hh := congrArg (fun n : ℕ => (n : ℤ)) s.first_norm
    push_cast at hh ⊢
    nlinarith only [hh]
  have hQ : b.Q = 1 := by
    change b.D^2-b.delta*b.c^2=1
    rw [hD,hd,hcc]
    have hh := congrArg (fun n : ℕ => (n : ℤ)) s.main_norm
    push_cast [Nat.cast_sub (by nlinarith : 1 ≤ (s.a+2)^2)] at hh
    nlinarith only [hh]
  have hV' : b.V = V := by
    change f^2*(b.c*T-b.rank)-b.c=V
    rw [hcc,hR]
    exact hVeq.symm
  have hU : b.U = 1 := by
    change (i*b.delta*b.c^2)^2*(b.V^2-(-y)^2)+(-y)^2=1
    rw [hd,hcc,hV',neg_sq]
    convert haux using 1; ring
  have hindex : Carrier66.index p v = 1 := by
    change b.k-(s.h : ℤ)*b.E-b.rank=1
    rw [hk,hE,hR]
    have hh := congrArg (fun n : ℕ => (n : ℤ)) s.index
    push_cast at hh ⊢
    nlinarith only [hh]
  have hW : b.W = 1 := by
    change (p 1+(d.w : ℤ))*b.C+(b.q-(d.F : ℤ))-(d.z : ℤ)*(p 0*d.J)=1
    have hb : p 0*(d.J : ℤ) = (2^u : ℕ)-(1 : ℤ) := by linarith [d.q_balance]
    rw [hC,hq,hb]
    exact d.transport
  have hZ : b.Z = b.delta := by
    change b.delta*f^2-(i*b.delta*b.c^2)^2=b.delta
    rw [hd,hcc]
    linear_combination ((s.a+2 : ℤ)^2-1)*hstrong
  have hcanon : Carrier66.Canonical p v :=
    ⟨hP,hQ,hU,hindex,hW,hZ,by rw [hR]; exact_mod_cast (by omega : 0<R)⟩
  exact ⟨⟨v,parent_pos d s hf hi hT (by omega),hcanon,
    ⟨rfl,rfl,rfl,rfl,rfl⟩,hq,hC,hR⟩⟩

/-- The complete seed is derived from rank population; no seed compatibility
or Pell norm is required from the scalar packing. -/
theorem population_constructs {p : Fin 4 → ℤ} {u R : ℕ} (d : Data p u R)
    (hu : 0<u) (hpop : Jones1982.σ 2 R=3*u+2) (hR4 : R%4=3) :
    Nonempty (Construction p u R d) := by
  obtain ⟨s⟩ := exists_outer_seed u R (R/2) hu (by omega) hpop
  exact exists_construction d s hR4

/-- All thirty-one natural coordinates and all literal source residuals follow. -/
theorem exists_positive_source {p : Fin 4 → ℤ} {u R : ℕ} (hb : 0<p 0)
    (d : Data p u R) (s : Seed u R) (hR4 : R%4=3) :
    ∃ x : Fin 31 → ℕ, (∀ j,0<x j) ∧
      (∀ j,SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j=0) ∧
      x 0=d.J ∧ x 1=d.F ∧ x 2=d.alpha ∧ x 3=d.z ∧ x 10=d.w := by
  obtain ⟨b⟩ := exists_construction d s hR4
  refine ⟨Carrier66Source.sourceNat p b.v,
    Carrier66Source.sourceNat_pos p b.v hb b.positive b.canonical,
    Carrier66Source.sourceNat_rows p b.v hb b.positive b.canonical,?_,?_,?_,?_,?_⟩
  all_goals simp [Carrier66Source.sourceNat,Carrier66Source.source,
    b.scalars.1,b.scalars.2.1,b.scalars.2.2.1,b.scalars.2.2.2.1,b.scalars.2.2.2.2,
    Int.toNat_natCast]

/-- The actual fourteen-variable polynomial receives positive coordinates. -/
theorem exists_positive_polynomial_zero {p : Fin 4 → ℤ} {u R : ℕ} (hb : 0<p 0)
    (d : Data p u R) (s : Seed u R) (hR4 : R%4=3) :
    ∃ v : Fin 14 → ℤ, (∀ j,0<v j) ∧
      MvPolynomial.eval v (Carrier65.polynomial p)=0 ∧
      v 0=d.J ∧ v 1=d.F ∧ v 2=d.alpha ∧ v 3=d.z ∧ v 8=d.w := by
  obtain ⟨b⟩ := exists_construction d s hR4
  obtain ⟨n,_,hn,hzero,_⟩ :=
    Carrier66.canonical_drops_to_positive_zero p hb b.v b.positive b.canonical
  refine ⟨Carrier66.drop b.v n,hn,?_,?_⟩
  · rw [Carrier65.eval_polynomial]
    exact hzero
  · exact b.scalars

/-- Rank population and the calibrated scalar equations suffice for the
actual fourteen-variable zero, with every private Pell witness derived. -/
theorem population_positive_polynomial_zero {p : Fin 4 → ℤ} {u R : ℕ}
    (hb : 0<p 0) (d : Data p u R) (hu : 0<u)
    (hpop : Jones1982.σ 2 R=3*u+2) (hR4 : R%4=3) :
    ∃ v : Fin 14 → ℤ, (∀ j,0<v j) ∧
      MvPolynomial.eval v (Carrier65.polynomial p)=0 ∧
      v 0=d.J ∧ v 1=d.F ∧ v 2=d.alpha ∧ v 3=d.z ∧ v 8=d.w := by
  obtain ⟨s⟩ := exists_outer_seed u R (R/2) hu (by omega) hpop
  exact exists_positive_polynomial_zero hb d s hR4

end DiophantineConsistency.NativePositiveSourceConstruction
