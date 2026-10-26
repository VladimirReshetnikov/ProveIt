import DiophantineConsistency.Carrier65Witness

/-!
# The literal fifteen-variable parent and the Carrier65 witness maps

The independent parent coordinates are
`J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma`, in that order.
The four ports remain `beta,K,MC,MF_source`.  The source mask is already
shifted by beta; this file does not shift it again.

The canonical parent interface includes the prescribed six factor values
and positive rank.  We prove equivalence with positive Carrier65 zeros,
not a classification of all parent zeros.  No native completeness or
consistency equivalence is a hypothesis of this algebraic theorem.
-/

namespace DiophantineConsistency.Carrier66

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Drop h and the independent tau, inserting the newly constructed carrier n. -/
def drop (v : Fin 15 → R) (n : R) (j : Fin 14) : R :=
  match j.val with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => v 3
  | 4 => v 4
  | 5 => v 6
  | 6 => v 7
  | 7 => v 8
  | 8 => v 9
  | 9 => n
  | 10 => v 11
  | 11 => v 12
  | 12 => v 13
  | _ => v 14

theorem drop_map (φ : R →+* S) (v : Fin 15 → R) (n : R) (j : Fin 14) :
    φ (drop v n j) = drop (fun i => φ (v i)) (φ n) j := by
  fin_cases j <;> rfl

/-- The parent's actual arithmetic blocks.  The fixed placeholder 1 disappears
from both overwritten fields; it is not another unknown. -/
def core (p : Fin 4 → R) (v : Fin 15 → R) : Carrier65.Core R :=
  let b := Carrier65.core p (drop v 1)
  { b with tau := v 10, P := (v 10) ^ 2 - b.ell * (b.ell + b.k) }

/-- The internal placeholder is provably irrelevant over every commutative ring. -/
theorem placeholder_irrelevant (p : Fin 4 → R) (v : Fin 15 → R) (n : R) :
    core p v =
      { Carrier65.core p (drop v n) with
        tau := v 10
        P := (v 10) ^ 2 - (Carrier65.core p (drop v n)).ell *
          ((Carrier65.core p (drop v n)).ell + (Carrier65.core p (drop v n)).k) } := rfl

/-- The omitted index factor, using the independent positive h coordinate. -/
def index (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  (core p v).k - v 5 * (core p v).E - (core p v).rank

/-- The literal P66 polynomial with exactly fifteen independent coordinates. -/
def value (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  let b := core p v
  b.P * b.Q * b.U * index p v * b.W * b.Z - b.delta

/-- Restore the old independent h and tau from a fourteen-coordinate assignment. -/
def restore (p : Fin 4 → R) (v : Fin 14 → R) (h : R) (j : Fin 15) : R :=
  match j.val with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => v 3
  | 4 => v 4
  | 5 => h
  | 6 => v 5
  | 7 => v 6
  | 8 => v 7
  | 9 => v 8
  | 10 => (Carrier65.core p v).tau
  | 11 => v 10
  | 12 => v 11
  | 13 => v 12
  | _ => v 13

/-- Every surviving arithmetic block and both first-norm inputs are preserved. -/
theorem core_restore (p : Fin 4 → R) (v : Fin 14 → R) (h : R) :
    core p (restore p v h) = Carrier65.core p v := rfl

theorem index_restore (p : Fin 4 → R) (v : Fin 14 → R) (h : R) :
    index p (restore p v h) =
      (Carrier65.core p v).k - h * (Carrier65.core p v).E - (Carrier65.core p v).rank := rfl

/-- This is an identity for the entire polynomial, not only its first norm. -/
theorem value_restore (p : Fin 4 → R) (v : Fin 14 → R) (h : R)
    (hindex : (Carrier65.core p v).k - h * (Carrier65.core p v).E -
      (Carrier65.core p v).rank = 1) :
    value p (restore p v h) = Carrier65.value p v := by
  dsimp only [value, Carrier65.value]
  rw [core_restore, index_restore, hindex, mul_one]

theorem core_drop (p : Fin 4 → R) (v : Fin 15 → R) (n : R) :
    Carrier65.core p (drop v n) =
      { core p v with
        tau := (core p v).E * n + (core p v).k - (core p v).rank
        P := ((core p v).E * n + (core p v).k - (core p v).rank) ^ 2 -
          (core p v).ell * ((core p v).ell + (core p v).k) } := rfl

/-- The converse carrier equation identifies all arithmetic blocks exactly. -/
theorem core_drop_of_carrier (p : Fin 4 → R) (v : Fin 15 → R) (n : R)
    (htau : v 10 = (core p v).E * n + (core p v).k - (core p v).rank) :
    Carrier65.core p (drop v n) = core p v := by
  rw [core_drop, ← htau]
  rfl

/-- Restoring and then deleting the two parent coordinates returns all fourteen inputs. -/
theorem drop_restore (p : Fin 4 → R) (v : Fin 14 → R) (h : R) :
    drop (restore p v h) (v 9) = v := by
  funext j
  fin_cases j <;> rfl

/-- On a proved carrier identity, the converse coordinate map returns the exact parent. -/
theorem restore_drop (p : Fin 4 → R) (v : Fin 15 → R) (n : R)
    (htau : v 10 = (core p v).E * n + (core p v).k - (core p v).rank) :
    restore p (drop v n) (v 5) = v := by
  funext j
  fin_cases j <;> try rfl
  change (Carrier65.core p (drop v n)).tau = v 10
  rw [core_drop_of_carrier p v n htau]
  rfl

theorem first_shape (p : Fin 4 → R) (v : Fin 15 → R) :
    (core p v).P = (v 10) ^ 2 -
      ((core p v).E * (core p v).Y) * ((core p v).E * (core p v).Y + 1) *
        (core p v).k ^ 2 := by
  change (v 10) ^ 2 - ((core p v).E * (core p v).k * (core p v).Y) *
    ((core p v).E * (core p v).k * (core p v).Y + (core p v).k) = _
  ring

theorem value_map (φ : R →+* S) (p : Fin 4 → R) (v : Fin 15 → R) :
    φ (value p v) = value (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value, index, core, Carrier65.core,
    map_add, map_sub, map_mul, map_pow, drop_map, map_one, map_ofNat]

noncomputable def polynomial (p : Fin 4 → ℤ) : MvPolynomial (Fin 15) ℤ :=
  value (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) :
    MvPolynomial.eval v (polynomial p) = value p v := by
  simpa only [polynomial, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

/-- The exact canonical norm and rank interface supplied by the parent native proof. -/
def Canonical (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) : Prop :=
  (core p v).P = 1 ∧ (core p v).Q = 1 ∧ (core p v).U = 1 ∧
    index p v = 1 ∧ (core p v).W = 1 ∧ (core p v).Z = (core p v).delta ∧
      0 < (core p v).rank

theorem canonical_zero (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) (hc : Canonical p v) :
    value p v = 0 := by
  obtain ⟨hP, hQ, hU, hi, hW, hZ, _⟩ := hc
  dsimp only [value]
  rw [hP, hQ, hU, hi, hW, hZ]
  ring

theorem drop_pos (v : Fin 15 → ℤ) (n : ℤ)
    (hv : ∀ j, 0 < v j) (hn : 0 < n) : ∀ j, 0 < drop v n j := by
  intro j
  fin_cases j <;> first
    | exact hn
    | exact hv 0
    | exact hv 1
    | exact hv 2
    | exact hv 3
    | exact hv 4
    | exact hv 6
    | exact hv 7
    | exact hv 8
    | exact hv 9
    | exact hv 11
    | exact hv 12
    | exact hv 13
    | exact hv 14

theorem restore_pos (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (h : ℤ)
    (hv : ∀ j, 0 < v j) (hh : 0 < h) (ht : 0 < (Carrier65.core p v).tau) :
    ∀ j, 0 < restore p v h j := by
  intro j
  fin_cases j <;> first
    | exact hh
    | exact ht
    | exact hv 0
    | exact hv 1
    | exact hv 2
    | exact hv 3
    | exact hv 4
    | exact hv 5
    | exact hv 6
    | exact hv 7
    | exact hv 8
    | exact hv 10
    | exact hv 11
    | exact hv 12
    | exact hv 13

/-- Every positive actual Carrier65 zero restores a canonical positive parent. -/
theorem positive_zero_restores_canonical (p : Fin 4 → ℤ)
    (hp : Carrier65Witness.PortBounds p) (v : Fin 14 → ℤ)
    (hv : ∀ j, 0 < v j) (hz : Carrier65.value p v = 0) :
    ∃ h : ℤ, 0 < h ∧ (∀ j, 0 < restore p v h j) ∧ Canonical p (restore p v h) := by
  have hb : 0 < p 0 := by have := hp.beta_min; omega
  obtain ⟨ht, h, ⟨hh, hi⟩, _⟩ := Carrier65Witness.positive_zero_restores_index p hp v hv hz
  obtain ⟨_, hR, _⟩ := Carrier65Witness.positive_zero_rank_window p hp v hv hz
  obtain ⟨hP, hQ, hU, _, hW⟩ := (Carrier65.value_zero_iff_norms p v hb hv).mp hz
  have hZ := Carrier65.scaled_strong_eq_delta p v hb hv hz
  refine ⟨h, hh, restore_pos p v h hv hh ht, ?_⟩
  dsimp only [Canonical]
  rw [core_restore, index_restore]
  exact ⟨hP, hQ, hU, hi, hW, hZ, by omega⟩

/-- A canonical positive parent supplies the integer n and preserves every factor. -/
theorem canonical_drops_to_positive_zero (p : Fin 4 → ℤ) (hbeta : 0 < p 0)
    (v : Fin 15 → ℤ) (hv : ∀ j, 0 < v j) (hc : Canonical p v) :
    ∃ n : ℤ, 0 < n ∧ (∀ j, 0 < drop v n j) ∧
      Carrier65.value p (drop v n) = 0 ∧
      v 10 = (core p v).E * n + (core p v).k - (core p v).rank := by
  have hpos := Carrier65.scales_pos p (drop v 1) hbeta (drop_pos v 1 hv (by norm_num))
  have hE : 0 < (core p v).E := hpos.2.2.1
  have hY : 0 < (core p v).Y := hpos.2.1
  have hk : 0 < (core p v).k := add_pos (hv 11) (hv 12)
  obtain ⟨hP, hQ, hU, hi, hW, hZ, hR⟩ := hc
  rw [first_shape] at hP
  obtain ⟨n, hn, htau⟩ := FirstPellCarrier.restore_carrier hE hY hk (hv 10) hR hi hP
  refine ⟨n, hn, drop_pos v n hv hn, ?_, htau⟩
  have hblocks := core_drop_of_carrier p v n htau
  dsimp only [Carrier65.value]
  rw [hblocks]
  have hfirst : (core p v).P = 1 := by rw [first_shape]; exact hP
  rw [hfirst, hQ, hU, hW, hZ]
  ring

/-- The complete zero-existence equivalence is purely arithmetic and explicit. -/
theorem exists_positive_zero_iff_canonical (p : Fin 4 → ℤ)
    (hp : Carrier65Witness.PortBounds p) :
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧ Carrier65.value p v = 0) ↔
      ∃ v : Fin 15 → ℤ, (∀ j, 0 < v j) ∧ Canonical p v := by
  constructor
  · rintro ⟨v, hv, hz⟩
    obtain ⟨h, _, hpos, hc⟩ := positive_zero_restores_canonical p hp v hv hz
    exact ⟨restore p v h, hpos, hc⟩
  · rintro ⟨v, hv, hc⟩
    have hb : 0 < p 0 := by have := hp.beta_min; omega
    obtain ⟨n, _, hn, hz, _⟩ := canonical_drops_to_positive_zero p hb v hv hc
    exact ⟨drop v n, hn, hz⟩

theorem exists_positive_polynomial_zero_iff_canonical (p : Fin 4 → ℤ)
    (hp : Carrier65Witness.PortBounds p) :
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      MvPolynomial.eval v (Carrier65.polynomial p) = 0) ↔
      ∃ v : Fin 15 → ℤ, (∀ j, 0 < v j) ∧ Canonical p v := by
  simp only [Carrier65.eval_polynomial]
  exact exists_positive_zero_iff_canonical p hp

/-- An endpoint mentioning both literal polynomials, with the parent's canonical
conditions explicit rather than a premise classifying arbitrary parent zeros. -/
theorem exists_positive_polynomial_zero_iff_canonical_parent_zero (p : Fin 4 → ℤ)
    (hp : Carrier65Witness.PortBounds p) :
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      MvPolynomial.eval v (Carrier65.polynomial p) = 0) ↔
      ∃ v : Fin 15 → ℤ, (∀ j, 0 < v j) ∧ Canonical p v ∧
        MvPolynomial.eval v (polynomial p) = 0 := by
  rw [exists_positive_polynomial_zero_iff_canonical p hp]
  constructor
  · rintro ⟨v, hv, hc⟩
    exact ⟨v, hv, hc, by rw [eval_polynomial]; exact canonical_zero p v hc⟩
  · rintro ⟨v, hv, hc, _⟩
    exact ⟨v, hv, hc⟩

#print axioms exists_positive_polynomial_zero_iff_canonical

end DiophantineConsistency.Carrier66
