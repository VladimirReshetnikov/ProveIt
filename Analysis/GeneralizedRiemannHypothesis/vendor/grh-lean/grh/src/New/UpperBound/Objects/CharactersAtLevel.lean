import New.UpperBound.Divisibility.MarkedPrimes
import New.UpperBound.Objects.Rows

/-!
# Characters of the lifts of the chain above the level N

This file shows that the characters of the lifts of the chain are unramified above the level `N`.
It identifies the character given by `New.rankTwist` and `New.AutChar.spaceChar` with a base
change. It also moves scalings at the primes dividing π, which lie above `N`, through chains of
lifts. A chain whose data at one lift are fixed by such a scaling annihilates the forms `ψ - z ψ`.

## Main definitions and results

* `New.Data.spaceChar_rankTwist`: `New.rankTwist` followed by `New.AutChar.spaceChar` gives the base
  change of the character of a lift.
* `New.Data.tensorChainLift_eq_zero_of_ramified`: for the chosen scaling `z_w` at a prime `w`
  dividing `π` and a tensor `t` of the data of the first `m` lifts, take `j < m` such that
  `ω(1, z_w)` on the factor of the lift from stage `j` to stage `j + 1` fixes `t`. Then the chain
  with the data `t` vanishes on the ramified source forms (`New.Data.ramifiedSourceForms`).

Notions from other files:
* `New.Data.N`: The level: a chosen prime N ≡ 1 mod q₂² with log N ∈ [λ, λ + √(log b)], where
  λ = `New.Data.logLevelTarget`.
* `New.Data.liftKernel`: The theta kernel of the lift from forms on X_j (`New.Data.FormX`) to forms
  on X_{j+1}. The finite unitary groups of X_j and X_{j+1} act on its data by ω.
* `New.chain`, `New.doubleLiftChain`, `New.TensorChain.lift`: The chain of theta lifts with data
  Φ_0, Φ_1, …, the same chain taken in pairs with data in S_{2i} ⊗ S_{2i+1}, and the chain with a
  tensor of data.

## Relation to the literature

See `New.UpperBound.Divisibility.ValuationAtLevel` for related work.
-/

namespace New.Data

variable {P : Parameters} (D : Data P) (ϑ : D.TameChar) (j : ℕ)

/-- Let `ν_j = D.chainChar ϑ j` be the character of `U(1)(𝔸)` used, for `j ≥ 1`, by the lift from
`X_{j-1}` to `X_j`. At a place `w` of `E` above the level `N`, the twist `rankTwist ν_j n`
(`ν_j` times `upsilonU1 ^ ⌊#n / 2⌋`) has a base change whose finite part is trivial on the local
units at `w`. -/
lemma charUnramifiedAt_rankTwist_of_N_mem (n : Type*) [Fintype n] (w : FinPlace D.E)
    (hw_N : ↑D.N ∈ w.asIdeal) :
    CharUnramifiedAt (rankTwist (D.chainChar ϑ j) n).baseChange.finPart w := by
  -- The tame part `D.liftTamePart` is trivial at `w` and `star w`, as places above `N` are neither
  -- chosen places (`not_isChosen_of_N_mem`) nor in `ϑ.Q`.
  have hQ (v : FinPlace D.E) (hv : ↑D.N ∈ v.asIdeal) : v ∉ ϑ.Q := fun hvQ ↦
    (D.normQ_mem_and_notMem_of_mem_Q ϑ (.inl hvQ)).right.right hv
  apply D.hasWeight_liftChar.hasWeight_rankTwist.charUnramifiedAt <;>
    simp [liftTamePart, not_isChosen_of_N_mem, ϑ.tamePart_eq_one, hQ, hw_N, TameChar.pow]

/-- Let ν = `D.chainChar ϑ i` be the character of U(1)(𝔸) used, for i ≥ 1, by the lift from X_{i-1}
to X_i with the twist ϑ. Applying `New.rankTwist` for X_j and then `New.AutChar.spaceChar` in rank
|X_j| to ν gives the Hecke character x ↦ ν(x/x̄), as |X_j| is even. -/
lemma spaceChar_rankTwist (i : ℕ) :
    (rankTwist (D.chainChar ϑ i) (D.X j)).spaceChar (Fintype.card (D.X j)) =
      (D.chainChar ϑ i).baseChange := by
  have h_even : Even (Fintype.card (D.X j)) := by grind [card_X, n]
  exact Exchange.spaceChar_rankTwist h_even.two_dvd

section Scalings

open TensorProduct

variable (w : D.piNPlaces)

/-- The finite adelic unitary groups of the definite spaces `X_j` and `X_{j+1}` act by the twisted
Weil action `ω` on the data of the theta lift `D.liftKernel ϑ j` from forms on `X_j` to forms on
`X_{j+1}`, twisted by the tame character `ϑ`. Let `w` be a prime dividing `π = D.piN`, the integer
of `E` with `π π̄ = N` for the level `N = D.N`, and `z` a scaling at `w`. Then the pair of scalars
`(z, z)` acts trivially. -/
lemma liftKernel_omega_scaling {z : unitary (𝔸f D.E)} (hz : D.IsScalingAt w z) :
    (D.liftKernel ϑ j).ω (scalarFin (D.X j) z, scalarFin (D.X (j + 1)) z) = 1 := by
  -- The pair fixes every linear map from `X_j` to `X_{j+1}`, and the characters of the lift are
  -- unramified above `N`.
  have h_split : star w.val ≠ w.val :=
    (ne_of_mem_of_not_mem w.property (D.isSplitLevel_piNPlaces.star_notMem _ w.property)).symm
  have hN_mem : ↑D.N ∈ w.val.asIdeal := D.isSplitLevel_piNPlaces.natCast_level_mem _ w.property
  have h_det (n m : Type) [Fintype n] [Fintype m] [DecidableEq m] (s : m → ℤˣ) :
      (rankTwist (D.chainChar ϑ (j + 1)) n).val (detFin s (scalarFin m z)) = 1 :=
    (D.charUnramifiedAt_rankTwist_of_N_mem ϑ (j + 1) n w hN_mem).det_maxCompactAt_eq_one h_split
      (D.scalarFin_mem_maxCompactAt_of_isScalingAt w m hz)
  simp [liftKernel_ω, Seesaw.pairWeilFinite_scalarFin, Prod.mk_one_one, h_det]

/-- Each lift of the chain commutes with the scalings at a prime `w` dividing `π`: for a scaling `z`
at `w`, a datum `Φ` of the lift from stage `j` to stage `j + 1` and a form `φ` of stage `j`, the
lift of the translate of `φ` by `z` is the translate by `z` of the lift of `φ`. -/
theorem liftKernel_lift_scaling {z : unitary (𝔸f D.E)} (hz : D.IsScalingAt w z)
    (Φ : (D.homX j).finitePart) (φ : D.FormX j) :
    (D.liftKernel ϑ j).lift Φ (algFormRep D.columnCount (D.lastEntry j) (scalarFin (D.X j) z) φ) =
      algFormRep D.columnCount (D.lastEntry (j + 1)) (scalarFin (D.X (j + 1)) z)
        ((D.liftKernel ϑ j).lift Φ φ) := by
  rw [← (D.liftKernel ϑ j).lift_equivariant (scalarFin (D.X j) z),
    D.liftKernel_omega_scaling ϑ j w hz, Module.End.one_apply]

/-- The lift from stage `j` to stage `j + 1` takes forms `ψ - z ψ`, for a scaling `z` at a prime
`w` dividing `π`, to forms of the same kind: the lift of `ψ - z ψ` is `χ - z χ` for the lift `χ`
of `ψ`. -/
theorem liftKernel_lift_sub_scaling {z : unitary (𝔸f D.E)} (hz : D.IsScalingAt w z)
    (Φ : (D.homX j).finitePart) (ψ : D.FormX j) :
    (D.liftKernel ϑ j).lift Φ (ψ - algFormRep D.columnCount (D.lastEntry j) (scalarFin (D.X j) z) ψ)
      =
      (D.liftKernel ϑ j).lift Φ ψ -
        algFormRep D.columnCount (D.lastEntry (j + 1)) (scalarFin (D.X (j + 1)) z)
          ((D.liftKernel ϑ j).lift Φ ψ) := by
  rw [map_sub, D.liftKernel_lift_scaling ϑ j w hz]

/-- Let `z` be a scaling at a prime `w` dividing `π`, and let `Φ` be a datum fixed by `ω(1, z)`.
Then the lift from stage `j` to stage `j + 1` with datum `Φ` sends `ψ - z ψ` to `0` for every form
`ψ` of stage `j`, where `z ψ` is the right translate of `ψ` by `z`. -/
theorem liftKernel_lift_sub_scaling_eq_zero {z : unitary (𝔸f D.E)} (hz : D.IsScalingAt w z)
    {Φ : (D.homX j).finitePart}
    (h_fix : (D.liftKernel ϑ j).ω (1, scalarFin (D.X (j + 1)) z) Φ = Φ) (ψ : D.FormX j) :
    (D.liftKernel ϑ j).lift Φ (ψ - algFormRep D.columnCount (D.lastEntry j) (scalarFin (D.X j) z) ψ)
      =
      0 := by
  -- `ω(1, z)` on the datum translates the lift by `z`; as it fixes `Φ`, `z` fixes the lift of `ψ`.
  have h_lift_fixed : (D.liftKernel ϑ j).lift Φ ψ = algFormRep D.columnCount (D.lastEntry (j + 1))
      (scalarFin (D.X (j + 1)) z) ((D.liftKernel ϑ j).lift Φ ψ) := by
    simpa [h_fix] using (D.liftKernel ϑ j).lift_equivariant 1 (scalarFin (D.X (j + 1)) z) Φ ψ
  rw [D.liftKernel_lift_sub_scaling ϑ j w hz, ← h_lift_fixed, sub_self]

/-- Let `t` be a tensor of data of the first `m` lifts, so that `TensorChain.lift` is the composite
of these lifts, extended linearly in `t`. Let `z` be a scaling at a prime `w` dividing `π = D.piN`,
the integer of `E` with `π π̄ = N` for the level `N = D.N`, and let `j < m`. If `ω(1, z)`, acting on
factor `j` alone, fixes `t`, then the chain with data `t` sends `ψ - z ψ` to `0` for every algebraic
form `ψ` on `X_0`. -/
theorem tensorChainLift_sub_scaling_eq_zero {m j : ℕ} (hj : j < m)
    (t : TensorChain (fun i : ℕ ↦ (D.homX i).finitePart) m) {z : unitary (𝔸f D.E)}
    (hz : D.IsScalingAt w z)
    (h_fix : TensorChain.map (fun i : ℕ ↦
      if i = j then (D.liftKernel ϑ i).ω (1, scalarFin (D.X (i + 1)) z) else 1) m t = t)
    (ψ : D.FormX 0) :
    TensorChain.lift (fun i : ℕ ↦ (D.liftKernel ϑ i).lift)
      (ψ - algFormRep D.columnCount (D.lastEntry 0) (scalarFin (D.X 0) z) ψ) m t = 0 := by
  -- `ω(1, z)` on factor `j` inserts `z` after lift `j`; move it to the source.
  have h_moved : TensorChain.lift (fun i : ℕ ↦ (D.liftKernel ϑ i).lift)
        (algFormRep D.columnCount (D.lastEntry 0) (scalarFin (D.X 0) z) ψ) m t =
      TensorChain.lift (fun i : ℕ ↦ (D.liftKernel ϑ i).lift) ψ m t :=
    TensorChain.lift_algFormRep_of_map_eq (D.liftKernel ϑ)
      (z := fun i : ℕ ↦ scalarFin (D.X i) z) (fun i ↦ D.liftKernel_omega_scaling ϑ i w hz) hj h_fix
        ψ
  rw [TensorChain.lift_sub, h_moved, sub_self]

/-- Let `w` be a prime dividing `π = D.piN`, the integer of `E` with `π π̄ = N` for the level
`N = D.N`, let `t` be a tensor of data of the first `m` lifts, and let `j < m`. If `ω(1, z_w)`,
acting on factor `j` alone, fixes `t`, then the chain of lifts with data `t` annihilates the
ramified source forms: the forms on `X_0` of level `D.levelX 0` whose translates by `z_v ^ k`,
`0 ≤ k < N - 1`, have sum `0` for each prime `v` dividing `π`, where `z_v = D.scalingGenerator v` is
the chosen scaling at `v` (integral, `1` off `v` and `v̄`, of order `N - 1` modulo `v`). -/
theorem tensorChainLift_eq_zero_of_ramified {m j : ℕ} (hj : j < m)
    (t : TensorChain (fun i : ℕ ↦ (D.homX i).finitePart) m)
    (h_fix : TensorChain.map (fun i : ℕ ↦ if i = j then
      (D.liftKernel ϑ i).ω (1, scalarFin (D.X (i + 1)) (D.scalingGenerator w)) else 1) m t = t)
    {φ : D.SourceForm} (hφ : φ ∈ D.ramifiedSourceForms) :
    TensorChain.lift (fun i : ℕ ↦ (D.liftKernel ϑ i).lift) φ.val m t = 0 := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : D.SourceForm, φ.val =
      ψ.val - algFormRep D.columnCount (D.lastEntry 0) (scalarFin (D.X 0) (D.scalingGenerator w))
        ψ.val :=
    D.exists_eq_sub_scalingGenerator w hφ
  rw [hψ]
  exact D.tensorChainLift_sub_scaling_eq_zero ϑ w hj t (D.isScalingAt_scalingGenerator w) h_fix ψ

/-- For each `l`, the finite adelic unitary groups of the definite spaces `X_l` and `X_{l+1}` act
by the twisted Weil action `ω` on the data (Schwartz functions in `(D.homX l).finitePart`) of the
theta lift `D.liftKernel ϑ l` from forms on `X_l` to forms on `X_{l+1}`, twisted by the tame
character `ϑ`.
Let `τ i` lie in the tensor product of the data for `l = 2 i` and `l = 2 i + 1`, so that it gives a
map from forms on `X_{2i}` to forms on `X_{2i+2}`; `doubleLiftChain` is the composite of the first
`p` of these maps. Let `w` be a prime dividing `π = D.piN`, the integer of `E` with `π π̄ = N` for
the level `N = D.N`. If for some `i < p` the operator `ω(1, z_w)` on the second tensor factor fixes
`τ i`, then the composite annihilates the ramified source forms: the forms on `X_0` of level
`D.levelX 0` whose translates by `z_v ^ k`, `0 ≤ k < N - 1`, have sum `0` for each prime `v`
dividing `π`, where `z_v = D.scalingGenerator v` is the chosen scaling at `v` (integral, `1` off
`v` and `v̄`, of order `N - 1` modulo `v`). -/
theorem doubleLiftChain_eq_zero_of_ramified
    {τ : ∀ i : ℕ, (D.homX (2 * i)).finitePart ⊗[ℂ] (D.homX (2 * i + 1)).finitePart} {i p : ℕ}
    (hi : i < p)
    (h_fix : map LinearMap.id ((D.liftKernel ϑ (2 * i + 1)).ω
      (1, scalarFin (D.X (2 * i + 1 + 1)) (D.scalingGenerator w))) (τ i) = τ i)
    {φ : D.SourceForm} (hφ : φ ∈ D.ramifiedSourceForms) :
    doubleLiftChain (D.liftKernel ϑ) τ p φ.val = 0 := by
  -- Regroup the data into `2 * p` single factors; `ω(1, z_w)` on factor `2 * i + 1` fixes them.
  have h_regrouped : TensorChain.map (fun l : ℕ ↦ if l = 2 * i + 1 then
        (D.liftKernel ϑ l).ω (1, scalarFin (D.X (l + 1)) (D.scalingGenerator w)) else 1) (2 * p)
      (TensorChain.ofPairs τ p) = TensorChain.ofPairs τ p := by
    rw [TensorChain.map_ofPairs]
    congr! with l
    obtain rfl | h_ne := eq_or_ne l i
    · rw [ite_eq_right (by omega), ite_eq_left rfl]
      exact h_fix
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), TensorProduct.map_one,
        Module.End.one_apply]
  rw [doubleLiftChain, ← TensorChain.lift_ofPairs]
  exact D.tensorChainLift_eq_zero_of_ramified ϑ w (by omega) _ h_regrouped hφ

end Scalings

end New.Data
