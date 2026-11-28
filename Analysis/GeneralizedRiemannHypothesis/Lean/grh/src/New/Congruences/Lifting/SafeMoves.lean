import New.Congruences.Lifting.SidePoints

/-!
# Safe moves and the walk for pairings of sides of a Kummer chart

This file concerns two sides of a Kummer chart with a pairing `P` modulo `p ^ m`. From numerical
conditions on orders it derives safe moves. It then walks along Frobenius orbits to derive the
condition `New.Lift.Pairing.IsScaledCupCoboundary`. It shows that at plain cuts deep enough standard
points are stops, and it sorts jumps in the windows into sides that are down or up.

## Main definitions and results

* `New.Lift.KummerChart.PairingSide.SidePairing.isSafe_of_orders`: for `w`, `y` over `0`, the
  pairs `(z τ w, y)` and `(w, z τ y)` are safe (`New.Lift.Pairing.IsSafe`) if the orders of `w`, `y`
  and a point of the Tate dual side `New.Lift.Pairing.tateDualSide` add up to a positive number.
* `New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveFst_of_killsCokernel`,
  `New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveSnd_of_killsCokernel`: the rule. A move is
  safe if a power of `p` times a power of `E` kills the cokernel of the Tate dual side and the
  orders of the move and the depth of the point at rest add up to at least `ruleBound`.
* `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_stops`: the walk. Standard
  points at the cuts are carried along by Frobenius; at each cut one side moves to a stop, rests
  there while the other side moves, and goes on to its own point.
* `New.Lift.KummerChart.PairingSide.SidePairing.exists_mem_stopPoints_isSafeMoveSnd`,
  `New.Lift.KummerChart.PairingSide.SidePairing.exists_mem_stopPoints_isSafeMoveFst`: at a plain
  cut, where one side is down and the other is up, a deep enough standard point is a stop.

Notions from other files:
* `New.Lift.KummerChart.PairingSide`: lattices Y and C with an O-linear map `cocycleMap` from C to
  the crystalline cocycles of Y, and for each letter a finite set of jumps that contains 0.
* `New.Lift.Pairing`: a pairing of Y and L modulo p^m, that is, an O-linear ψ: Y ⊗ L → O(1) with
  gψ − ψ = p^m c(g) for a crystalline cocycle c, and a Z_p-linear f: O → Z_p.
* `New.Lift.KummerChart.PairingSide.pointsOver`: points of the extension over `p ^ e c`, with
  exponents and a depth.
* `New.Lift.KummerChart.PairingSide.stopPoints`: the points over `p ^ e c` with the exponents
  `stopOrders η l` of a stop, where one side rests while the other side moves.
* `New.Lift.KummerChart.PairingSide.ruleBound`: the least sum of the orders of a move and the depth
  of the point at rest that the rule for `l` allows.

## Relation to the literature

Explicit powers of p and of the Eisenstein polynomial kill cokernels of Kisin modules on crystalline
extensions, and Galois operators buy divisibility at known cost. A walk along Frobenius orbits makes
cup products of crystalline classes vanish up to powers of p, and these tools bound the loss above p
in the Selmer bound. Zero cokernel for weights of one sign, cup products via Ext and torsion bounds
by Sen operators are known in the literature. Related work: Čoupek–Gazaki–Marmora, Exactness
property of Breuil–Kisin functors and Bloch–Kato Selmer groups, 2026; Gao–Liu, Integral Sen theory
and integral Hodge filtration, 2024; Chang–Diamond, Extensions of rank one (φ,Γ)-modules and
crystalline representations, 2011.

The file `New.Congruences.Lifting.CutExponentBounds` applies the walk to two choices of cuts.
-/

noncomputable section

namespace New.Lift.KummerChart

open Period Submodule FrobGroup Module Finset JumpLattice Pairing Equiv Fintype LinearMap Algebra

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ} {O : k.Coeffs}

namespace PairingSide

variable {S S' : PairingSide O} {c : S.paramLattice} {i : k.Letter}

section Points

variable {c' : S'.paramLattice} {l κ s e e' : ℕ} {o o' o₁ o₂ o₃ : ℕ → ℤ → ℤ}
  {x w : S.extensionLattice.Ambient} {y : S'.extensionLattice.Ambient} {P : S.SidePairing S'}

/-! ### Safe pairs and the walk -/

/-- The constant `1` of the Tate dual side of `P` at the letter `i` acts on `S.Ambient` as the
projector to the letter `i`, and the pairing of `n` with `w ⊗ y` by `P.extensionForm`, reduced
modulo `p ^ P.exponent` through `P.toZp`, is the pairing of the product of the projection of `n` and
`w` with `y`. -/
lemma wittPairing_constantAt_and_extensionForm (i : k.Letter) :
    letI B := JumpLattice.wittPairing (C := S.kerLattice) (.lsmul O S.Carrier)
    (∀ w : S.Ambient, B (P.tateDualSide.constantAt i 1) w = S.letterProj i w) ∧
    ∀ (n : P.tateDualSide.extensionLattice.Ambient) (w : S.Ambient) (y : S'.Ambient),
      DiagTensor.map (mkQ (Ideal.span {(p : ℤ_[p]) ^ P.exponent}) ∘ₗ P.toZp)
          (JumpLattice.wittPairing (C := tateLattice O) P.extensionForm n
            (JumpLattice.wittPairing (C := S.tensorLattice S')
              (TensorProduct.mk O S.Carrier S'.Carrier) w y)) =
        P.wittPairing (B (P.tateDualSide.projTrivial.wittMap n) w) y :=
  ⟨wittPairing_constantAt_one i, map_wittPairing_extensionForm⟩

/-- If the orders `o` are antitone in the jump at every level, so is `shiftedOrders l n o`, which is
`n` at the levels below `l` and `o` shifted up by `l` levels from there on. -/
lemma antitone_shiftedOrders (h_anti : ∀ a : ℕ, Antitone (o a)) (l : ℕ) (n : ℤ) (a : ℕ) :
    Antitone (shiftedOrders l n o a) := fun u v huv ↦ by
  unfold shiftedOrders
  split_ifs
  exacts [le_rfl, h_anti (a - l) huv]

/-- The coordinate `k.z` of the chart, a Teichmüller lift that is not a unit, lies in the ideal
`W(𝔪^♭)` of `Ainf`. -/
lemma z_mem_wittOfMaxIdeal : k.z.1 ∈ wittOfMaxIdeal := by
  rw [k.z_eq_teichmuller]
  refine teichmuller_mem_wittOfMaxIdeal fun h ↦ k.chart.not_isUnit_z ?_
  rw [k.seriesMap_X]
  exact h.map _

/-- Reduced modulo `p ^ P.exponent` through `P.toZp` and multiplied by `k.z`, the `Ainf`-span of
`O(1)` falls into the image `smallPart P.exponent` of `W(𝔪^♭)`. -/
lemma z_smul_map_mem_smallPart {ξ : (tateLattice O).Ambient}
    (hξ : ξ ∈ (tateLattice O).ainfLattice) :
    k.z.1 • DiagTensor.map (mkQ (Ideal.span {(p : ℤ_[p]) ^ P.exponent}) ∘ₗ P.toZp) ξ ∈ smallPart
      P.exponent := by
  let red := k.z.1 • (DiagTensor.map (mkQ (Ideal.span {(p : ℤ_[p]) ^ P.exponent}) ∘ₗ P.toZp) :
    (tateLattice O).Ambient →ₗ[WittCFlat] DiagTensor (.of (charRep _ χ))).restrictScalars Ainf
  refine (span_le (p := (smallPart P.exponent).comap red)).2 (Set.forall_mem_range.2 fun t ↦ ?_) hξ
  refine ⟨_, smul_of_tower_mem _ (P.toZp t) (z_mem_wittOfMaxIdeal (k := k)), ?_⟩
  simp [red, mul_smul, ← map_smul, smul_def', smul_comm]

/-- Let `ν` be a point of the Tate dual side `P.tateDualSide` of the pairing `P` over `p ^ κ` at the
letter `i.stepBack l`, `l` steps before `i`, with orders `νOrders`, antitone in the jump, and any
depth (`pointsOver`). Let `w` and `y` be vectors of the two extensions that lie over `0` with orders
`wOrders` and `yOrders` at `i` (`kerWithOrders`). Suppose that at every level `a` and all jumps
`u ∈ S.jumpSet`, `u' ∈ S'.jumpSet` at the letter `a` steps before `i` the order of `φ ^ l • ν` at
`-u - u' - 1` plus `wOrders a u + yOrders a u'` is positive. Then `(z τ w, y)` and `(w, z τ y)` are
safe for `κ`: `p ^ κ` times the pairing of their components in `Y`, `Y'` lies in the image of
`W(𝔪^♭)`, the Witt vectors of the maximal ideal of the tilt. Here `z τ = k.zTauUnit`, for the
coordinate `z` of the chart and `τ = [ε^{1/p}] - 1`. -/
lemma SidePairing.isSafe_of_orders {l κ : ℕ} {wOrders yOrders νOrders νDepth : ℕ → ℤ → ℤ}
    {w : S.extensionLattice.Ambient} {y : S'.extensionLattice.Ambient} {P : S.SidePairing S'}
    {ν : P.tateDualSide.extensionLattice.Ambient}
    (hν : ν ∈ P.tateDualSide.pointsOver 1 (i.stepBack l) κ νOrders νDepth)
    (h_anti : ∀ a : ℕ, Antitone (νOrders a))
    (hw : w ∈ S.kerWithOrders i wOrders) (hy : y ∈ S'.kerWithOrders i yOrders)
    (h_pos : ∀ a : ℕ, ∀ u ∈ S.jumpSet (i.stepBack a), ∀ u' ∈ S'.jumpSet (i.stepBack a),
      0 < shiftedOrders l 0 νOrders a (-u - u' - 1) + wOrders a u + yOrders a u') :
    P.IsSafe κ (k.zTauUnit • w) y ∧ P.IsSafe κ w (k.zTauUnit • y) := by
  -- Pair `w ⊗ y` with the point `φ ^ l • ν` of the Tate dual side by `extensionForm`. Orders add,
  -- so the value `ξ` in `O(1)` has standard orders and `tau • ξ` is integral; a further factor
  -- `k.z` makes its image modulo `p ^ P.exponent` small. That image is `p ^ κ` times the pairing of
  -- `w` and `y`.
  obtain ⟨w, w_exp, rfl, -⟩ := exists_inclKer_eq_of_kerWithOrders hw
  obtain ⟨y, y_exp, rfl, -⟩ := exists_inclKer_eq_of_kerWithOrders hy
  obtain ⟨-, ν_over, ν_exp, -⟩ := phi_pow_smul_mem_pointsOver hν
  let wy : (S.tensorLattice S').Ambient := JumpLattice.wittPairing (C := S.tensorLattice S')
    (TensorProduct.mk O S.Carrier S'.Carrier) w y
  -- orders add under pairing, and the orders of `φ ^ l • ν` decrease in the jump
  have wy_exp : wy ∈ (S.tensorLattice S').withOrders i
      fun a v ↦ 1 - shiftedOrders l 0 νOrders a (-v - 1) := by
    refine wittPairing_mem_withOrders (fun g s t ↦ by simp) w_exp y_exp
      fun a u hu u' hu' v _ h_le ↦ ?_
    have h_jump : -v - 1 ≤ -u - u' - 1 := by omega
    linarith [h_pos a u hu u' hu', antitone_shiftedOrders h_anti l 0 a h_jump]
  let ξ : (tateLattice O).Ambient :=
    JumpLattice.wittPairing (C := tateLattice O) P.extensionForm (φ ^ l • ν) wy
  have ξ_std : ξ ∈ (tateLattice O).withOrders i (stdOrders 0) := by
    refine wittPairing_mem_withOrders (fun g s t ↦ P.extensionForm_equivariant g s t) ν_exp
      wy_exp fun a u _ u' _ v hv h_le ↦ ?_
    obtain rfl : v = -1 := by simpa using hv
    have h_std : stdOrders 0 a (-1) = 1 := by simp [stdOrders]
    have h_jump : u ≤ -u' - 1 := by omega
    linarith [antitone_shiftedOrders h_anti l 0 a h_jump]
  have τξ_int : tau ^ 1 • ξ ∈ (tateLattice O).ainfLattice :=
    (tateLattice O).tau_pow_smul_mem_ainfLattice_of_eq_chi_pow_smul 1 ξ_std (by simp)
  obtain ⟨⟨-, w_mem_letter⟩, -⟩ := w_exp
  have w_letter : S.letterProj i w = w := mem_letterPart_iff_letterProj.1 w_mem_letter
  have h_ξ : DiagTensor.map (mkQ (Ideal.span {(p : ℤ_[p]) ^ P.exponent}) ∘ₗ P.toZp) ξ =
      p ^ κ • P.wittPairing w y := by
    simp [ξ, wy, w_letter, wittPairing_constantAt_and_extensionForm i, ν_over, -nsmul_eq_mul]
  -- multiplied by `tau` and `k.z`, whose product is `k.zTau`, this value becomes small
  have h_small : k.zTau • p ^ κ • P.wittPairing w y ∈ smallPart P.exponent := by
    simpa [zTau, mul_comm tau, mul_smul, map_smul_of_tower, h_ξ, -nsmul_eq_mul] using
      z_smul_map_mem_smallPart (P := P) τξ_int
  -- both claims say that `z τ p ^ κ` times the pairing of `w` and `y` is small
  simpa [IsSafe, zTauUnit_smul, smul_comm _ k.zTau, -nsmul_eq_mul] using h_small

/-- Let `ν` be a point of the Tate dual side `Hom(Y ⊗ Y', O(1))` of the pairing `P`, over `p ^ κ` at
the letter `l` steps before `i`, with orders `νOrders`, antitone in the jump. Let `w` lie over `0`
with orders `wOrders` at `i`, and let `y` be a point of the second side over `p ^ e' c'` at `i`,
with any orders, fixed by `Γ'` modulo orders `yDepth`. If at all jumps `u`, `u'` the order of
`φ ^ l • ν` at `-u - u' - 1` plus `wOrders a u + yDepth a u'` is positive, the move by `w` is safe
with `y` at rest: for all `g` in `Γ'`, `p ^ κ` times the pairing of `w` with `g • y - y` lies in the
image of `W(𝔪^♭)`. -/
lemma SidePairing.isSafeMoveFst_of_orders {c' : S'.paramLattice} {l κ e' : ℕ}
    {wOrders yDepth yOrders νOrders νDepth : ℕ → ℤ → ℤ}
    {w : S.extensionLattice.Ambient} {y : S'.extensionLattice.Ambient} {P : S.SidePairing S'}
    {ν : P.tateDualSide.extensionLattice.Ambient}
    (hν : ν ∈ P.tateDualSide.pointsOver 1 (i.stepBack l) κ νOrders νDepth)
    (h_anti : ∀ a : ℕ, Antitone (νOrders a))
    (hw : w ∈ S.kerWithOrders i wOrders) (hy : y ∈ S'.pointsOver c' i e' yOrders yDepth)
    (h_pos : ∀ a : ℕ, ∀ u ∈ S.jumpSet (i.stepBack a), ∀ u' ∈ S'.jumpSet (i.stepBack a),
      0 < shiftedOrders l 0 νOrders a (-u - u' - 1) + wOrders a u + yDepth a u') :
    P.IsSafeMoveFst κ w y := by
  intro g
  have safe : P.IsSafe κ w (k.zTauUnit • k.zTauUnit⁻¹ • (g • y - y)) :=
    (P.isSafe_of_orders hν h_anti hw (zTauUnit_inv_smul_sub_mem_kerWithOrders hy g) h_pos).right
  rwa [smul_inv_smul] at safe

/-- Let `ν` be a point of the Tate dual side `Hom(Y ⊗ Y', O(1))` of the pairing `P`, over `p ^ κ` at
the letter `l` steps before `i`, with orders `νOrders`, antitone in the jump. Let `x` be a point of
the first side over `p ^ e c` at `i`, with any orders, fixed by `Γ'` modulo orders `xDepth`, and let
`y` lie over `0` with orders `yOrders`. If at all jumps `u`, `u'` the order of `φ ^ l • ν` at
`-u - u' - 1` plus `xDepth a u + yOrders a u'` is positive, the move by `y` is safe with `x` at
rest: for all `g` in `Γ'`, `p ^ κ` times the pairing of `g • x - x` with `g • y` lies in the image
of `W(𝔪^♭)`. -/
lemma SidePairing.isSafeMoveSnd_of_orders {l κ e : ℕ}
    {xDepth yOrders xOrders νOrders νDepth : ℕ → ℤ → ℤ}
    {x : S.extensionLattice.Ambient} {y : S'.extensionLattice.Ambient} {P : S.SidePairing S'}
    {ν : P.tateDualSide.extensionLattice.Ambient}
    (hν : ν ∈ P.tateDualSide.pointsOver 1 (i.stepBack l) κ νOrders νDepth)
    (h_anti : ∀ a : ℕ, Antitone (νOrders a))
    (hx : x ∈ S.pointsOver c i e xOrders xDepth) (hy : y ∈ S'.kerWithOrders i yOrders)
    (h_pos : ∀ a : ℕ, ∀ u ∈ S.jumpSet (i.stepBack a), ∀ u' ∈ S'.jumpSet (i.stepBack a),
      0 < shiftedOrders l 0 νOrders a (-u - u' - 1) + xDepth a u + yOrders a u') :
    P.IsSafeMoveSnd κ x y := by
  intro g
  have ⟨y_exp, (y_zero : S'.projTrivial.wittMap y = 0)⟩ := hy
  have cocycle_mem : g • y - y ∈ S'.kerWithOrders i yOrders :=
    ⟨smul_sub_mem_withOrders y_exp g, by simp [k.galMonoid.smul_def, y_zero]⟩
  have gy_mem : g • y ∈ S'.kerWithOrders i yOrders := (sub_mem_iff_left _ hy).1 cocycle_mem
  have safe : P.IsSafe κ (k.zTauUnit • k.zTauUnit⁻¹ • (g • x - x)) (g • y) :=
    (P.isSafe_of_orders hν h_anti (zTauUnit_inv_smul_sub_mem_kerWithOrders hx g) gy_mem
      h_pos).left
  simpa using safe

lemma mem_letterPart_of_mem_pointsOver (hx : x ∈ S.pointsOver c i e o o') :
    x ∈ S.extensionLattice.letterPart i := by
  obtain ⟨-, -, ⟨⟨-, x_letter⟩, -⟩, -⟩ := hx
  exact x_letter

open scoped Classical in
/-- If `l i` is the distance back from each letter `i` to the nearest cut strictly before it, then
`l i` is `1` if the letter one step before `i` is a cut, and one more than the distance from that
letter otherwise. -/
lemma eq_ite_add_one_of_isLeast_cut {cut : k.Letter → Prop} {l : k.Letter → ℕ}
    (h_least : ∀ i : k.Letter, IsLeast {a : ℕ | 0 < a ∧ cut (i.stepBack a)} (l i))
    (i : k.Letter) : l i = (if cut (i.stepBack 1) then 0 else l (i.stepBack 1)) + 1 := by
  have stepBack_succ (a : ℕ) : (i.stepBack 1).stepBack a = i.stepBack (a + 1) := rfl
  obtain ⟨⟨l_pos, l_cut⟩, l_min⟩ := h_least i
  obtain ⟨⟨-, prev_cut⟩, prev_min⟩ := h_least (i.stepBack 1)
  split_ifs with h_cut
  · exact le_antisymm (l_min ⟨one_pos, h_cut⟩) l_pos
  refine le_antisymm (l_min ⟨Nat.succ_pos _, by rwa [← stepBack_succ]⟩) ?_
  obtain ⟨m, hm⟩ : ∃ m : ℕ, l i = m + 1 := Nat.exists_eq_add_one.2 l_pos
  rw [hm] at l_cut ⊢
  have m_pos : 0 < m := by grind
  exact Nat.succ_le_succ (prev_min ⟨m_pos, by rwa [stepBack_succ]⟩)

end Points


/-- A point of the side `S` over `p ^ e c` at the letter `i` satisfies `LiesOver`: it is in the
part at `i` and projects to `p ^ e` times the constant of `c`. -/
lemma liesOver_of_mem_pointsOver {e : ℕ} {o d : ℕ → ℤ → ℤ} {x : S.extensionLattice.Ambient}
    (hx : x ∈ S.pointsOver c i e o d) : S.LiesOver c i e x :=
  have ⟨_, x_over, _⟩ := hx
  ⟨mem_letterPart_of_mem_pointsOver hx, x_over⟩

/-- `φ ^ l` carries a point over `p ^ e c` at the letter `l` steps before `i` to a vector at `i`
over `p ^ e c`. -/
lemma liesOver_phi_pow_smul {e l : ℕ} {o d : ℕ → ℤ → ℤ} {x : S.extensionLattice.Ambient}
    (hx : x ∈ S.pointsOver c (i.stepBack l) e o d) : S.LiesOver c i e (φ ^ l • x) :=
  liesOver_of_mem_pointsOver (phi_pow_smul_mem_pointsOver hx)

/-- If each `x i` lies at the letter `i` over `p ^ e` times the constant of `c` at `i`, then
`S.projTrivial.wittMap` sends `∑ i, x i` to `p ^ e • DiagTensor.mk 1 c`, as the letter projectors
sum to `1`. -/
lemma projTrivial_sum_of_liesOver {e : ℕ} {x : k.Letter → S.extensionLattice.Ambient}
    (hx : ∀ i : k.Letter, S.LiesOver c i e (x i)) :
    S.projTrivial.wittMap (∑ i : k.Letter, x i) = p ^ e • DiagTensor.mk 1 c := by
  simp [fun i ↦ (hx i).projTrivial_eq, ← smul_sum, constantAt, sum_letterProj]

/-- A point over `p ^ e c` with orders `o₁` and depth `d₁` has also the orders `o₂` and the depth
`d₂` if, at all jumps, `o₂` is at most `o₁` and `d₂` is at most `d₁`. -/
lemma mem_pointsOver_of_le {e : ℕ} {o₁ o₂ d₁ d₂ : ℕ → ℤ → ℤ} {x : S.extensionLattice.Ambient}
    (hx : x ∈ S.pointsOver c i e o₁ d₁)
    (h_exponent : ∀ a : ℕ, ∀ u ∈ S.jumpSet (i.stepBack a), o₂ a u ≤ o₁ a u)
    (h_depth : ∀ a : ℕ, ∀ u ∈ S.jumpSet (i.stepBack a), d₂ a u ≤ d₁ a u) :
    x ∈ S.pointsOver c i e o₂ d₂ := by
  obtain ⟨x_mem, x_over, x_exp, x_deep⟩ := hx
  exact ⟨x_mem, x_over, mem_withOrders_of_le x_exp h_exponent,
    fun g ↦ mem_withOrders_of_le (x_deep g) h_depth⟩

/-- A point over `p ^ e c` with orders `o₁` and depth `d` has also the orders `o₂`, with the same
depth, if `o₂` is at most `o₁` at all jumps. -/
lemma mem_pointsOver_of_exponent_le {e : ℕ} {o₁ o₂ d : ℕ → ℤ → ℤ} {x : S.extensionLattice.Ambient}
    (hx : x ∈ S.pointsOver c i e o₁ d)
    (h_exponent : ∀ a : ℕ, ∀ u ∈ S.jumpSet (i.stepBack a), o₂ a u ≤ o₁ a u) :
    x ∈ S.pointsOver c i e o₂ d :=
  mem_pointsOver_of_le hx h_exponent fun a u _ ↦ le_refl (d a u)

/-- Let `x` lie in `S.pointsOver c i e o d`: a point over `p ^ e` times the constant of `c` at the
letter `i`, with orders `o` and depth `d`. Suppose that at all jumps `u` in `S.jumpSet` at the
letters `a` steps before `i`, `o` is at least `raisedOrdersAtZero (-t)`, and `d` is at least
`raisedOrdersAtZero 0`. The first bound means a pole of order at most `t` at `E`, the Eisenstein
polynomial of the chart: `-u`, lowered by `t` at `a = 0`. If `0 ≤ h₀` and no jump at `i` lies in
`[-t, -h₀)`, then `x` has orders `raisedOrdersAtZero (-h₀)`, a pole of order at most `h₀` at `E`,
with the same depth. -/
lemma mem_pointsOver_raisedOrdersAtZero_of_gap {e : ℕ} {t h₀ : ℤ} {o d : ℕ → ℤ → ℤ}
    {x : S.extensionLattice.Ambient} (hx : x ∈ S.pointsOver c i e o d) (h₀_nonneg : 0 ≤ h₀)
    (h_gap : ∀ u ∈ S.jumpSet i, -t ≤ u → -h₀ ≤ u)
    (h_pole : ∀ a : ℕ, ∀ u ∈ S.jumpSet (i.stepBack a), raisedOrdersAtZero (-t) a u ≤ o a u)
    (h_depth : ∀ a : ℕ, ∀ u ∈ S.jumpSet (i.stepBack a), raisedOrdersAtZero 0 a u ≤ d a u) :
    x ∈ S.pointsOver c i e (raisedOrdersAtZero (-h₀)) d := by
  obtain ⟨-, -, x_pole, x_deep⟩ : x ∈ S.pointsOver c i e (raisedOrdersAtZero (-t))
    (raisedOrdersAtZero 0) :=
    mem_pointsOver_of_le hx h_pole h_depth
  obtain ⟨x_mem, x_over, -, x_depth⟩ := hx
  exact ⟨x_mem, x_over, mem_withOrders_raisedOrdersAtZero_of_gap h₀_nonneg h_gap x_pole x_deep,
    x_depth⟩

/-- A point over `p ^ e c` whose exponents are at least the exponents `stopOrders η l` of a stop
lies in `stopPoints`, the set of the points with these exponents, whatever its depth. -/
lemma mem_stopPoints_of_le {e η l : ℕ} {o d : ℕ → ℤ → ℤ} {q : S.extensionLattice.Ambient}
    (hq : q ∈ S.pointsOver c i e o d)
    (h_exponent : ∀ a : ℕ, ∀ u ∈ S.jumpSet (i.stepBack a), stopOrders η l a u ≤ o a u) :
    q ∈ S.stopPoints c i e η l := by
  obtain ⟨q_mem, q_over, q_exp, -⟩ := hq
  have q_stop : q ∈ S.extensionLattice.withOrders i (stopOrders η l) :=
    mem_withOrders_of_le q_exp h_exponent
  exact ⟨q_mem, q_over, q_stop, smul_sub_mem_withOrders q_stop⟩

/-- A point over `p ^ e c` with the exponents `stopOrders η l` of a stop lies in
`stopPoints`, whatever its depth. -/
lemma mem_stopPoints_of_mem_pointsOver {e η l : ℕ} {d : ℕ → ℤ → ℤ} {q : S.extensionLattice.Ambient}
    (hq : q ∈ S.pointsOver c i e (stopOrders η l) d) : q ∈ S.stopPoints c i e η l :=
  mem_stopPoints_of_le hq fun a u _ ↦ le_refl (stopOrders η l a u)

/-- The orders of `φ ^ l` of a point of the Tate dual side with a pole of order `t`, on the line of
jump `-u - u' - 1`, and `ruleBound l t` add up to `1`. With `s = u + u'`, at the levels `a` below,
at and above `l` the first term is `0`, `s + 1 - t`, `s + 1` (`shiftedOrders l 0 o` is `0` below `l`
and `o` shifted up by `l` levels from there on) and the second is `1`, `t - s`, `-s`. -/
lemma shiftedOrders_raisedOrdersAtZero_add_ruleBound (l t a : ℕ) (u u' : ℤ) :
    shiftedOrders l 0 (raisedOrdersAtZero (-t)) a (-u - u' - 1) + ruleBound l t a (u + u') = 1 := by
  simp only [shiftedOrders, raisedOrdersAtZero, ruleBound]
  split_ifs <;> omega

lemma raisedOrdersAtZero_mono {t t' : ℤ} (h_le : t ≤ t') (a : ℕ) (u : ℤ) :
    raisedOrdersAtZero t a u ≤ raisedOrdersAtZero t' a u := by
  grind

/-- The orders `raisedOrdersAtZero t a u`, which are `t - u` at the level `0` and `-u` above it,
decrease in the jump `u`. -/
lemma antitone_raisedOrdersAtZero (t : ℤ) (a : ℕ) : Antitone (raisedOrdersAtZero t a) :=
  fun _ _ h_le ↦ sub_le_sub_left h_le (if a = 0 then t else 0)

/-- Let `p ^ κ * E ^ t` kill the cokernel of the Tate dual side `Hom(Y ⊗ Y', O(1))` of the pairing
`P` of the sides `S`, `S'` at the letter `l` steps before `i`, `E` being the Eisenstein polynomial
of the chart. Let `y` be a vector over `0` with orders `o` at `i` (`kerWithOrders`) and `x'` a point
of the second side over `p ^ e' c'`, fixed by `Γ'` modulo orders `d'` (its depth). If at all jumps
`u`, `u'` these add up to at least `ruleBound l t`, then the move by `y` is safe with `x'` at rest:
`p ^ κ` times the pairing of `y` and `g • x' - x'` lies in the image of `W(𝔪^♭)` for all `g` in
`Γ'`. -/
lemma SidePairing.isSafeMoveFst_of_killsCokernel {c' : S'.paramLattice} {P : S.SidePairing S'}
    {κ e' l t : ℕ} {o o' d' : ℕ → ℤ → ℤ}
    {y : S.extensionLattice.Ambient} {x' : S'.extensionLattice.Ambient}
    (h_kill : P.tateDualSide.KillsCokernel (i.stepBack l) κ t) (hy : y ∈ S.kerWithOrders i o)
    (hx' : x' ∈ S'.pointsOver c' i e' o' d')
    (h_sum : ∀ a : ℕ, ∀ u ∈ S.jumpSet (i.stepBack a), ∀ u' ∈ S'.jumpSet (i.stepBack a),
      ruleBound l t a (u + u') ≤ o a u + d' a u') :
    P.IsSafeMoveFst κ y x' := by
  obtain ⟨n, hn⟩ := pointsOver_nonempty_of_killsCokernel h_kill 1
  refine P.isSafeMoveFst_of_orders hn (antitone_raisedOrdersAtZero (-t)) hy hx' fun a u hu u' hu' ↦
    ?_
  linarith [shiftedOrders_raisedOrdersAtZero_add_ruleBound l t a u u', h_sum a u hu u' hu']

/-- Let `p ^ κ * E ^ t` kill the cokernel of the Tate dual side `Hom(Y ⊗ Y', O(1))` of the pairing
`P` of the sides `S`, `S'` at the letter `l` steps before `i`, `E` being the Eisenstein polynomial
of the chart. Let `y'` be a vector over `0` with orders `o'` at `i` (`kerWithOrders`) and `x` a
point of the first side over `p ^ e c`, fixed by `Γ'` modulo orders `d` (its depth). If at all jumps
`u`, `u'` these add up to at least `ruleBound l t`, then the move by `y'` is safe with `x` at rest:
`p ^ κ` times the pairing of `g • x - x` and `g • y'` lies in the image of `W(𝔪^♭)` for all `g` in
`Γ'`. -/
lemma SidePairing.isSafeMoveSnd_of_killsCokernel {P : S.SidePairing S'}
    {κ e l t : ℕ} {o o' d : ℕ → ℤ → ℤ}
    {x : S.extensionLattice.Ambient} {y' : S'.extensionLattice.Ambient}
    (h_kill : P.tateDualSide.KillsCokernel (i.stepBack l) κ t) (hy' : y' ∈ S'.kerWithOrders i o')
    (hx : x ∈ S.pointsOver c i e o d)
    (h_sum : ∀ a : ℕ, ∀ u' ∈ S'.jumpSet (i.stepBack a), ∀ u ∈ S.jumpSet (i.stepBack a),
      ruleBound l t a (u' + u) ≤ o' a u' + d a u) :
    P.IsSafeMoveSnd κ x y' := by
  obtain ⟨n, hn⟩ := pointsOver_nonempty_of_killsCokernel h_kill 1
  refine P.isSafeMoveSnd_of_orders hn (antitone_raisedOrdersAtZero (-t)) hx hy' fun a u hu u' hu' ↦
    ?_
  have h_bound : ruleBound l t a (u + u') ≤ o' a u' + d a u := by
    simpa only [add_comm u'] using h_sum a u' hu' u hu
  linarith [shiftedOrders_raisedOrdersAtZero_add_ruleBound l t a u u']

/-- The first move of the walk satisfies the rule for `l`: the orders of the move from `φ ^ l` of a
standard point at the cut before to a stop, and the depth of `φ ^ l` of a standard point at rest,
add up to at least `ruleBound l t₀`, on every pair of jumps `u`, `v`. A standard point at the cut
before has depth `standardDepth t₀ η l₀`, and `shiftedOrders l n o` is `n` at the levels below `l`
and `o` shifted up by `l` levels from there on. -/
lemma ruleBound_le_inf_add_shiftedOrders {l l₀ : ℕ} (hl₀ : 0 < l₀) (t₀ η a : ℕ) (u v : ℤ) :
    ruleBound l t₀ a (u + v) ≤
      (stopOrders η l ⊓ shiftedOrders l 0 (raisedOrdersAtZero (-η))) a u +
        shiftedOrders l 1 (standardDepth t₀ η l₀) a v := by
  simp only [Pi.inf_apply, ruleBound, stopOrders, stdOrders, shiftedOrders, raisedOrdersAtZero,
    standardDepth]
  split_ifs <;> omega

/-- The third move of the walk satisfies the rule for `0`: the orders of the move from a stop to a
standard point, and the depth of a standard point at rest, add up to at least `ruleBound 0 t`, on
every pair of jumps `u`, `v`. -/
lemma ruleBound_zero_le_inf_add_standardDepth {l : ℕ} (hl : 0 < l) (t η a : ℕ) (u v : ℤ) :
    ruleBound 0 t a (u + v) ≤
      (raisedOrdersAtZero (-η) ⊓ stopOrders η l) a u + standardDepth t η l a v := by
  simp only [Pi.inf_apply, ruleBound, stopOrders, stdOrders, raisedOrdersAtZero, standardDepth]
  split_ifs <;> omega

/-- The moves at a cut (a marked letter) `i` whose predecessor among the cuts is `l` steps back, at
`i.stepBack l`; the cut before that is `l₀` steps further back. Let `x₀`, `x₀'` and `x`, `x'` be
standard points at the two cuts, and let `p ^ κ * E ^ t₀`, `p ^ κ * E ^ t` kill the cokernels of the
Tate dual side there. If one side has a stop at which it can rest while the other moves safely, then
for some `w`, `w'` over the same constants (`LiesOver`) four safe moves, of one side with the other
at rest, lead from `(φ ^ l x₀, φ ^ l x₀')` by `(w, φ ^ l x₀')` and `(w, w')` and `(x, w')` to
`(x, x')` (`IsSafePath`). -/
lemma SidePairing.exists_isSafePath_of_stop {c' : S'.paramLattice} {P : S.SidePairing S'}
    {κ e e' η l l₀ t t₀ : ℕ}
    {x₀ x : S.extensionLattice.Ambient} {x₀' x' : S'.extensionLattice.Ambient}
    (hl : 0 < l) (hl₀ : 0 < l₀) (h_kill : P.tateDualSide.KillsCokernel i κ t)
    (h_kill₀ : P.tateDualSide.KillsCokernel (i.stepBack l) κ t₀)
    (hx : x ∈ S.standardPoints c i e t η l) (hx' : x' ∈ S'.standardPoints c' i e' t η l)
    (hx₀ : x₀ ∈ S.standardPoints c (i.stepBack l) e t₀ η l₀)
    (hx₀' : x₀' ∈ S'.standardPoints c' (i.stepBack l) e' t₀ η l₀)
    (h_stop : (∃ q ∈ S.stopPoints c i e η l, P.IsSafeMoveSnd κ q (φ ^ l • x₀' - x')) ∨
      ∃ q' ∈ S'.stopPoints c' i e' η l, P.IsSafeMoveFst κ (φ ^ l • x₀ - x) q') :
    ∃ (w : S.extensionLattice.Ambient) (w' : S'.extensionLattice.Ambient),
      S.LiesOver c i e w ∧ S'.LiesOver c' i e' w' ∧
      P.IsSafePath κ (φ ^ l • x₀) w x (φ ^ l • x₀') w' x' := by
  -- The moves from `φ ^ l x₀` and `φ ^ l x₀'` to a stop satisfy the rule for `l`, those from a stop
  -- to `x` and `x'` the rule for `0`; the remaining move is zero.
  have hy : φ ^ l • x₀ ∈ S.pointsOver c i e (shiftedOrders l 0 (raisedOrdersAtZero (-η)))
      (shiftedOrders l 1 (standardDepth t₀ η l₀)) := phi_pow_smul_mem_pointsOver hx₀
  have hy' : φ ^ l • x₀' ∈ S'.pointsOver c' i e' (shiftedOrders l 0 (raisedOrdersAtZero (-η)))
      (shiftedOrders l 1 (standardDepth t₀ η l₀)) := phi_pow_smul_mem_pointsOver hx₀'
  obtain ⟨q, hq, h_rest⟩ | ⟨q', hq', h_rest⟩ := h_stop
  · -- The first side leads: it moves to `q`, rests there, and goes on to `x`.
    have h_first : P.IsSafeMoveFst κ (φ ^ l • x₀ - q) (φ ^ l • x₀') :=
      P.isSafeMoveFst_of_killsCokernel h_kill₀ (sub_mem_kerWithOrders_of_pointsOver hq hy) hy'
        fun a u _ v _ ↦ ruleBound_le_inf_add_shiftedOrders hl₀ t₀ η a u v
    have h_third : P.IsSafeMoveFst κ (q - x) x' :=
      P.isSafeMoveFst_of_killsCokernel (l := 0) h_kill
        (sub_mem_kerWithOrders_of_pointsOver hx hq) hx'
        fun a u _ v _ ↦ ruleBound_zero_le_inf_add_standardDepth hl t η a u v
    exact ⟨q, x', liesOver_of_mem_pointsOver hq, liesOver_of_mem_pointsOver hx',
      h_first, h_rest, h_third, fun g ↦ by simp [IsSafe]⟩
  · -- The second side leads: it moves to `q'`, rests there, and goes on to `x'`.
    have h_second : P.IsSafeMoveSnd κ (φ ^ l • x₀) (φ ^ l • x₀' - q') :=
      P.isSafeMoveSnd_of_killsCokernel h_kill₀ (sub_mem_kerWithOrders_of_pointsOver hq' hy') hy
        fun a u _ v _ ↦ ruleBound_le_inf_add_shiftedOrders hl₀ t₀ η a u v
    have h_fourth : P.IsSafeMoveSnd κ x (q' - x') :=
      P.isSafeMoveSnd_of_killsCokernel (l := 0) h_kill
        (sub_mem_kerWithOrders_of_pointsOver hx' hq') hx
        fun a u _ v _ ↦ ruleBound_zero_le_inf_add_standardDepth hl t η a u v
    exact ⟨φ ^ l • x₀, q', liesOver_of_mem_pointsOver hy, liesOver_of_mem_pointsOver hq',
      fun g ↦ by simp [IsSafe], h_second, h_rest, h_fourth⟩

/-- Let `P` be a pairing of the sides `S`, `S'`, and let `0 < l`. Let `x`, `x'` be standard points
(`standardPoints`) of `S`, `S'` over `p ^ e c`, `p ^ e' c'` at the letter `d` steps before `i`.
Their orders are `-u` on the line of jump `u`, lowered by `η` at the level `0`, and their depth is
`standardDepth t η l`. Let `p ^ κ * E ^ t` kill the cokernel of the Tate dual side `P.tateDualSide`
there (`KillsCokernel`), and let `φ` be the Frobenius. Then for every `g` in `k.galMonoid`,
`P.IsSafeMoveSnd κ` holds: the move of the second side by `g φ ^ d x' - φ ^ d x'` is safe while
`φ ^ d x` is at rest. -/
lemma SidePairing.isSafeMoveSnd_cocycle {c' : S'.paramLattice} {P : S.SidePairing S'}
    {κ e e' η d l t : ℕ}
    {x : S.extensionLattice.Ambient} {x' : S'.extensionLattice.Ambient} (hl : 0 < l)
    (h_kill : P.tateDualSide.KillsCokernel (i.stepBack d) κ t)
    (hx : x ∈ S.standardPoints c (i.stepBack d) e t η l)
    (hx' : x' ∈ S'.standardPoints c' (i.stepBack d) e' t η l) (g : k.galMonoid) :
    P.IsSafeMoveSnd κ (φ ^ d • x) (g • φ ^ d • x' - φ ^ d • x') := by
  -- The depth of `x'` bounds the exponents of its cocycle; use the rule for `d`.
  have hy' := phi_pow_smul_mem_pointsOver hx'
  have ⟨_, _, _, h_deep⟩ := hy'
  have h_cocycle : g • φ ^ d • x' - φ ^ d • x' ∈
      S'.kerWithOrders i (shiftedOrders d 1 (standardDepth t η l)) :=
    ⟨h_deep g, by simpa [inv_smul_eq_iff] using (zTauUnit_inv_smul_sub_mem_kerWithOrders hy' g).2⟩
  refine P.isSafeMoveSnd_of_killsCokernel h_kill h_cocycle (phi_pow_smul_mem_pointsOver hx)
    fun a u _ v _ ↦ ?_
  simp only [ruleBound, shiftedOrders, standardDepth]
  split_ifs <;> omega

/-- The path that stays at `(x, x')` is safe: its four moves are zero. -/
lemma isSafePath_refl {P : S.SidePairing S'} {κ : ℕ} (x : S.extensionLattice.Ambient)
    (x' : S'.extensionLattice.Ambient) : P.IsSafePath κ x x x x' x' x' := by
  constructor <;> intro g <;> simp [IsSafe]

lemma smul_sub_mem_letterPart {x : S.extensionLattice.Ambient} (g : k.galMonoid)
    (hx : x ∈ S.extensionLattice.letterPart i) : g • x - x ∈ S.extensionLattice.letterPart i :=
  sub_mem ((gal_smul_mem_letterPart g).2 hx) hx

/-- Let `y i` and `x' i` lie in the parts of the letter `i`. If each move of the first side by `y i`
is safe with `x' i` at rest, then so is the move by their sum with the sum of the `x' i` at rest. -/
lemma isSafeMoveFst_sum {P : S.SidePairing S'} {κ : ℕ} {y : k.Letter → S.extensionLattice.Ambient}
    {x' : k.Letter → S'.extensionLattice.Ambient}
    (hy : ∀ i : k.Letter, y i ∈ S.extensionLattice.letterPart i)
    (hx' : ∀ i : k.Letter, x' i ∈ S'.extensionLattice.letterPart i)
    (h_safe : ∀ i : k.Letter, P.IsSafeMoveFst κ (y i) (x' i)) :
    P.IsSafeMoveFst κ (∑ i : k.Letter, y i) (∑ i : k.Letter, x' i) := by
  intro g
  rw [smul_sum, ← sum_sub_distrib]
  exact isSafe_sum (fun i ↦ ⟨hy i, smul_sub_mem_letterPart g (hx' i)⟩) fun i ↦ h_safe i g

/-- For a pairing `P` of the sides `S`, `S'`, let `x i` and `y' i` lie in `letterPart i`, the parts
of the letter `i`. Suppose each move of the second side by `y' i` is safe with `x i` at rest
(`P.IsSafeMoveSnd κ`). Then the move by the sum of the `y' i` is safe with the sum of the `x i` at
rest. -/
lemma isSafeMoveSnd_sum {P : S.SidePairing S'} {κ : ℕ} {x : k.Letter → S.extensionLattice.Ambient}
    {y' : k.Letter → S'.extensionLattice.Ambient}
    (hx : ∀ i : k.Letter, x i ∈ S.extensionLattice.letterPart i)
    (hy' : ∀ i : k.Letter, y' i ∈ S'.extensionLattice.letterPart i)
    (h_safe : ∀ i : k.Letter, P.IsSafeMoveSnd κ (x i) (y' i)) :
    P.IsSafeMoveSnd κ (∑ i : k.Letter, x i) (∑ i : k.Letter, y' i) := by
  intro g
  rw [smul_sum, smul_sum, ← sum_sub_distrib]
  exact isSafe_sum (fun i ↦ ⟨smul_sub_mem_letterPart g (hx i),
    (gal_smul_mem_letterPart g).2 (hy' i)⟩) fun i ↦ h_safe i g

/-- Safety is checked letter by letter. Let `S`, `S'` be sides of the chart `k` with pairing `P`. At
each letter `i` let `y i`, `w i`, `x i` lie over `p ^ e` times the constant of `c` at `i`
(`LiesOver`), likewise `y' i`, `w' i`, `x' i` over `p ^ e' c'`, and let `φ` map `∑ x i` and
`∑ x' i` to `∑ y i` and `∑ y' i`. A pair is safe if `p ^ κ` times its pairing lies in the image of
`W(𝔪^♭)`; a move of the first side by `v` with `q'` at rest is safe if the pairs of `v` and
`g • q' - q'` are safe, and one of the second side by `v'` with `q` at rest if those of `g • q - q`
and `g • v'` are. Let the cocycles of `x i` and `x' i` pair safely, and let four safe moves lead
from `(y i, y' i)` by `(w i, y' i)`, `(w i, w' i)` and `(x i, w' i)` to `(x i, x' i)`
(`IsSafePath`). Then the cup product of the cocycles of `c` and `p ^ N c'` is a coboundary
(`IsScaledCupCoboundary`) for `N ≥ e + e' + κ`. -/
lemma SidePairing.isScaledCupCoboundary_of_isSafePath {c' : S'.paramLattice} {P : S.SidePairing S'}
    {κ e e' N : ℕ} {y w x : k.Letter → S.extensionLattice.Ambient}
    {y' w' x' : k.Letter → S'.extensionLattice.Ambient}
    (hy : ∀ i : k.Letter, S.LiesOver c i e (y i)) (hy' : ∀ i : k.Letter, S'.LiesOver c' i e' (y' i))
    (hw : ∀ i : k.Letter, S.LiesOver c i e (w i)) (hw' : ∀ i : k.Letter, S'.LiesOver c' i e' (w' i))
    (hx : ∀ i : k.Letter, S.LiesOver c i e (x i)) (hx' : ∀ i : k.Letter, S'.LiesOver c' i e' (x' i))
    (h_phi : φ • ∑ i : k.Letter, x i = ∑ i : k.Letter, y i)
    (h_phi' : φ • ∑ i : k.Letter, x' i = ∑ i : k.Letter, y' i)
    (h_cocycles : ∀ (i : k.Letter) (g : k.galMonoid), P.IsSafeMoveSnd κ (x i) (g • x' i - x' i))
    (h_path : ∀ i : k.Letter, P.IsSafePath κ (y i) (w i) (x i) (y' i) (w' i) (x' i))
    (hN : e + e' + κ ≤ N) : P.IsScaledCupCoboundary N c c' := by
  -- Sum the cocycles and each of the four moves over the letters, then apply the pairing lemma.
  have h_cocycle_sum (g : k.galMonoid) :
      P.IsSafeMoveSnd κ (∑ i, x i) (g • ∑ i, x' i - ∑ i, x' i) := by
    rw [smul_sum, ← sum_sub_distrib]
    exact isSafeMoveSnd_sum (fun i ↦ (hx i).mem_letterPart)
      (fun i ↦ smul_sub_mem_letterPart g (hx' i).mem_letterPart) fun i ↦ h_cocycles i g
  have h_path_sum :
      P.IsSafePath κ (∑ i, y i) (∑ i, w i) (∑ i, x i) (∑ i, y' i) (∑ i, w' i) (∑ i, x' i) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← sum_sub_distrib]
    · exact isSafeMoveFst_sum (fun i ↦ sub_mem (hy i).mem_letterPart (hw i).mem_letterPart)
        (fun i ↦ (hy' i).mem_letterPart) fun i ↦ (h_path i).isSafeMoveFst_start
    · exact isSafeMoveSnd_sum (fun i ↦ (hw i).mem_letterPart)
        (fun i ↦ sub_mem (hy' i).mem_letterPart (hw' i).mem_letterPart) fun i ↦
          (h_path i).isSafeMoveSnd_start
    · exact isSafeMoveFst_sum (fun i ↦ sub_mem (hw i).mem_letterPart (hx i).mem_letterPart)
        (fun i ↦ (hw' i).mem_letterPart) fun i ↦ (h_path i).isSafeMoveFst_end
    · exact isSafeMoveSnd_sum (fun i ↦ (hx i).mem_letterPart)
        (fun i ↦ sub_mem (hw' i).mem_letterPart (hx' i).mem_letterPart) fun i ↦
          (h_path i).isSafeMoveSnd_end
  rw [← h_phi, ← h_phi'] at h_path_sum
  exact .of_isSafePath P (∑ i, x i) (∑ i, w i) (∑ i, x' i) (∑ i, w' i) hN
    (projTrivial_sum_of_liesOver hx) (projTrivial_sum_of_liesOver hw)
    (projTrivial_sum_of_liesOver hx') (projTrivial_sum_of_liesOver hw')
    h_cocycle_sum h_path_sum

/-- The walk. Let `S` and `S'` be sides of the Kummer chart `k` over the coefficient ring `O`
(lattices `Y`, `Y'` with crystalline cocycles `S.cocycleMap c`, `S'.cocycleMap c'` indexed by
lattices `C`, `C'`), and let `P` pair `Y` and `Y'` modulo `p ^ P.exponent`. Letters are elements of
`k.Letter`. Some letters are cuts (`cut`); `i.stepBack a` is the letter `a` steps before `i`, `φ` is
the Frobenius and `E` is the Eisenstein polynomial of the chart. Assume:
* `hl_least`: the last cut before each letter `i` lies `l i` steps back.
* `h_kill`: at each cut `i`, `p ^ κ * E ^ t i` kills the cokernel of the Tate dual side
  `P.tateDualSide`, which is `Hom(Y ⊗ Y', O(1))` with the cocycle of `P`: it multiplies the
  constants at `i` into the image of the vectors of the extension with the standard orders of level
  `0`.
* `hx`, `hx'`: at each cut `i`, `x i` and `x' i` are standard points. They lie in the localized
  Kisin modules of the extensions of `C` by `Y` and of `C'` by `Y'`, over `p ^ e c` and `p ^ e' c'`.
  On the line of jump `u` their order is `-u`, lowered by `η` at the level `0`, and their depth is
  `-u`, raised by `t i` at the level `0` and by `η` at the levels below `l i`.
* `h_stop`: at each cut `i` one side has a stop, a point over the same constant with orders
  `stopOrders η (l i)`, which are `max 0 (-u - η)` at the levels below `l i` and `-u` from there on.
  While it rests there, the other side moves safely from `φ ^ l i` of its point at the cut before to
  its point at `i`.

Then for `N ≥ e + e' + κ` the cup product of `S.cocycleMap c` and `p ^ N • S'.cocycleMap c'` under
`P` is the coboundary of a continuous cochain. -/
lemma SidePairing.isScaledCupCoboundary_of_stops {S S' : PairingSide O} {c : S.paramLattice}
    {c' : S'.paramLattice} {P : S.SidePairing S'}
    {κ e e' η N : ℕ} (cut : k.Letter → Prop) (l t : k.Letter → ℕ)
    (x : k.Letter → S.extensionLattice.Ambient) (x' : k.Letter → S'.extensionLattice.Ambient)
    (hl_least : ∀ i : k.Letter, IsLeast {a : ℕ | 0 < a ∧ cut (i.stepBack a)} (l i))
    (h_kill : ∀ i : k.Letter, cut i → P.tateDualSide.KillsCokernel i κ (t i))
    (hx : ∀ i : k.Letter, cut i → x i ∈ S.standardPoints c i e (t i) η (l i))
    (hx' : ∀ i : k.Letter, cut i → x' i ∈ S'.standardPoints c' i e' (t i) η (l i))
    (h_stop : ∀ i : k.Letter, cut i →
      (∃ q ∈ S.stopPoints c i e η (l i),
        P.IsSafeMoveSnd κ q (φ ^ l i • x' (i.stepBack (l i)) - x' i)) ∨
      ∃ q' ∈ S'.stopPoints c' i e' η (l i),
        P.IsSafeMoveFst κ (φ ^ l i • x (i.stepBack (l i)) - x i) q')
    (hN : e + e' + κ ≤ N) : P.IsScaledCupCoboundary N c c' := by
  -- At a letter `i` take the points of the last cut up to `i`, `d i` steps back, and carry them to
  -- `i` by `φ ^ d i`. Applying `φ` to their sum gives the same sum with the last cut strictly
  -- before `i`. So off the cuts nothing moves, and at a cut there are the three moves.
  classical
  let d (i : k.Letter) : ℕ := if cut i then 0 else l i
  obtain ⟨hl_pos, hl_cut⟩ : (∀ i : k.Letter, 0 < l i) ∧ ∀ i : k.Letter, cut (i.stepBack (l i)) :=
    forall_and.1 fun i ↦ (hl_least i).1
  have hd_cut (i : k.Letter) : cut (i.stepBack (d i)) := by
    by_cases hi : cut i
    · simpa only [d, ite_eq_left hi, stepBack_zero] using hi
    · simpa only [d, ite_eq_right hi] using hl_cut i
  have h_phi {L : JumpLattice O} (z : k.Letter → L.Ambient) :
      φ • ∑ i, φ ^ d i • z (i.stepBack (d i)) = ∑ i, φ ^ l i • z (i.stepBack (l i)) := by
    rw [smul_sum, ← sum_comp k.letterFrob⁻¹]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h_frob : k.letterFrob⁻¹ i = i.stepBack 1 := by simp
    have h_stepBack (a : ℕ) : (i.stepBack 1).stepBack a = i.stepBack (a + 1) := rfl
    have hl_succ : l i = d (i.stepBack 1) + 1 := eq_ite_add_one_of_isLeast_cut hl_least i
    rw [h_frob, h_stepBack, hl_succ, pow_succ' φ, mul_smul]
  have h_over {i : k.Letter} {a : ℕ} (ha : cut (i.stepBack a)) :
      S.LiesOver c i e (φ ^ a • x (i.stepBack a)) := liesOver_phi_pow_smul (hx _ ha)
  have h_over' {i : k.Letter} {a : ℕ} (ha : cut (i.stepBack a)) :
      S'.LiesOver c' i e' (φ ^ a • x' (i.stepBack a)) := liesOver_phi_pow_smul (hx' _ ha)
  have exists_path (i : k.Letter) :
      ∃ (w : S.extensionLattice.Ambient) (w' : S'.extensionLattice.Ambient),
      S.LiesOver c i e w ∧ S'.LiesOver c' i e' w' ∧
      P.IsSafePath κ (φ ^ l i • x (i.stepBack (l i))) w (φ ^ d i • x (i.stepBack (d i)))
        (φ ^ l i • x' (i.stepBack (l i))) w' (φ ^ d i • x' (i.stepBack (d i))) := by
    by_cases hi : cut i
    · simp only [d, ite_eq_left hi, pow_zero, one_smul, stepBack_zero]
      exact P.exists_isSafePath_of_stop (hl_pos i) (hl_pos _) (h_kill i hi) (h_kill _ (hl_cut i))
        (hx i hi) (hx' i hi) (hx _ (hl_cut i)) (hx' _ (hl_cut i)) (h_stop i hi)
    · simp only [d, ite_eq_right hi]
      exact ⟨φ ^ l i • x (i.stepBack (l i)), φ ^ l i • x' (i.stepBack (l i)),
        h_over (hl_cut i), h_over' (hl_cut i), isSafePath_refl _ _⟩
  choose w w' hw hw' h_path using exists_path
  have h_cocycles (i : k.Letter) (g : k.galMonoid) : P.IsSafeMoveSnd κ
      (φ ^ d i • x (i.stepBack (d i)))
      (g • φ ^ d i • x' (i.stepBack (d i)) - φ ^ d i • x' (i.stepBack (d i))) :=
    P.isSafeMoveSnd_cocycle (hl_pos _) (h_kill _ (hd_cut i)) (hx _ (hd_cut i)) (hx' _ (hd_cut i)) g
  exact P.isScaledCupCoboundary_of_isSafePath (fun i ↦ h_over (hl_cut i))
    (fun i ↦ h_over' (hl_cut i))
    hw hw' (fun i ↦ h_over (hd_cut i)) (fun i ↦ h_over' (hd_cut i)) (h_phi x) (h_phi x')
    h_cocycles h_path hN

/-- The walk `isScaledCupCoboundary_of_stops` with a cut at every letter and the same shift `t` at
all of them, for a pairing `P` of the sides `S` and `S'`. At every letter `i`, let `p ^ κ * E ^ t`
kill the cokernel of the Tate dual side, and let `x i`, `x' i` be standard points over `p ^ e c`,
`p ^ e' c'`: their orders on the line of jump `u` are `-u`, lowered by the margin `η` at the level
`0`, and they are fixed by `Γ'` modulo orders `-u`, raised by `t + η` at the level `0`. Let one side
have a stop at `i`, a point over the same constant with orders `stopOrders η 1`, such that, while it
rests there, the other side moves safely to its point at `i` from `φ` of its point at the letter
`i.stepBack 1` before. Then for `N ≥ e + e' + κ` the cup product of `S.cocycleMap c` and
`p ^ N • S'.cocycleMap c'` is the coboundary of a continuous cochain. -/
lemma SidePairing.isScaledCupCoboundary_of_stops_at_all_letters {c' : S'.paramLattice}
    {P : S.SidePairing S'} {κ e e' t η N : ℕ}
    (x : k.Letter → S.extensionLattice.Ambient) (x' : k.Letter → S'.extensionLattice.Ambient)
    (h_kill : ∀ i : k.Letter, P.tateDualSide.KillsCokernel i κ t)
    (hx : ∀ i : k.Letter, x i ∈ S.standardPoints c i e t η 1)
    (hx' : ∀ i : k.Letter, x' i ∈ S'.standardPoints c' i e' t η 1)
    (h_stop : ∀ i : k.Letter,
      (∃ q ∈ S.stopPoints c i e η 1, P.IsSafeMoveSnd κ q (φ ^ 1 • x' (i.stepBack 1) - x' i)) ∨
      ∃ q' ∈ S'.stopPoints c' i e' η 1, P.IsSafeMoveFst κ (φ ^ 1 • x (i.stepBack 1) - x i) q')
    (hN : e + e' + κ ≤ N) : P.IsScaledCupCoboundary N c c' := by
  have h_least : IsLeast {a : ℕ | 0 < a ∧ True} 1 := ⟨⟨one_pos, trivial⟩, fun _ ⟨ha, _⟩ ↦ ha⟩
  exact P.isScaledCupCoboundary_of_stops (fun _ ↦ True) (fun _ ↦ 1) (fun _ ↦ t) x x'
    (fun _ ↦ h_least)
    (fun i _ ↦ h_kill i) (fun i _ ↦ hx i) (fun i _ ↦ hx' i) (fun i _ ↦ h_stop i) hN

/-- If `Q` holds at the jumps at the letter `i`, it holds at the jumps at `i.stepBack a` for all
`a < 1`, that is, for `a = 0`. -/
lemma forall_mem_U_stepBack_of_lt_one {Q : ℤ → Prop} (hQ : ∀ u ∈ S.jumpSet i, Q u) :
    ∀ a : ℕ, a < 1 → ∀ u ∈ S.jumpSet (i.stepBack a), Q u := by
  simpa only [Nat.lt_one_iff, forall_eq, stepBack_zero] using hQ

/-- The case where the side `S` is down. Let `x` be a standard point over `p ^ e c` at the letter
`i`: it has orders `raisedOrdersAtZero (-η)` (`-u` on the line of jump `u`, lowered by `η` at the
level `0`) and depth `standardDepth t η l` (`-u`, raised by `t` at `0` and by `η` below `l`).
Suppose `0 < l` and all jumps of `S` (`S.jumpSet`) at the `l` letters up to `i` are at most `η`.
Then `x` lies in `stopPoints`: it has the orders `stopOrders η l`, which are `max 0 (-u - η)` below
`l` and `-u` from there on. -/
lemma mem_stopPoints_of_down {e t η l : ℕ} {x : S.extensionLattice.Ambient} (hl : 0 < l)
    (h_down : ∀ a : ℕ, a < l → ∀ u ∈ S.jumpSet (i.stepBack a), u ≤ η)
    (hx : x ∈ S.standardPoints c i e t η l) : x ∈ S.stopPoints c i e η l := by
  -- At the levels below `l` the depth is at least `η - u ≥ 0`, so the exponent is at least `0`.
  obtain ⟨x_mem, x_over, x_exp, x_deep⟩ := hx
  have x_improved : x ∈ S.pointsOver c i e
      (improvedOrders (raisedOrdersAtZero (-η)) (standardDepth t η l)) (standardDepth t η l) :=
    ⟨x_mem, x_over, mem_withOrders_improvedOrders x_exp x_deep, x_deep⟩
  refine mem_stopPoints_of_le x_improved fun a u hu ↦ ?_
  have h_le : a < l → u ≤ η := (h_down a · u hu)
  simp only [stopOrders, stdOrders, improvedOrders, raisedOrdersAtZero, standardDepth]
  split_ifs <;> omega

/-- The second move at a plain cut satisfies the rule for `0`: at a jump `u` of the side that is up
(`u ≥ -η` below the level `l`) and any jump `v`, the orders of the move and the depth
`plainDepth t η l η₀` at rest add up to at least `ruleBound 0 t`. -/
lemma ruleBound_zero_le_inf_add_plainDepth {η l a : ℕ} {u : ℤ} (hl : 0 < l) (h_up : a < l → -η ≤ u)
    (t η₀ : ℕ) (v : ℤ) :
    ruleBound 0 t a (u + v) ≤
      (raisedOrdersAtZero (-η) ⊓ shiftedOrders l 0 (raisedOrdersAtZero (-η₀))) a u + plainDepth t η
        l η₀ a v := by
  simp only [Pi.inf_apply, ruleBound, shiftedOrders, raisedOrdersAtZero, plainDepth, standardDepth]
  split_ifs <;> omega

/-- Plain cuts, the first side moves. Let `0 < l` and let the jumps of `S` at `i.stepBack a`,
`a < l`, be at least `-η`. Let `x₀` at `i.stepBack l` and `x` at `i` lie in `S.pointsOver` over
`p ^ e` times the constant of `c`. Let them have orders `raisedOrdersAtZero (-η₀)` and
`raisedOrdersAtZero (-η)`: `-u` on the line of jump `u`, lowered by `η₀`, `η` at level `0`. Let
`p ^ κ * E ^ t` kill the cokernel of `P.tateDualSide` at `i` (`KillsCokernel`). Let `q'` in
`S'.pointsOver c' i e'` have any orders `qOrders` and depth `plainDepth t η l η₀`. This means it is
fixed by the subgroup `Γ'` of `k` modulo orders `-u`, raised by `t` at level `0`, by `η` below `l`,
by `η₀` at `l`. Then `P.IsSafeMoveFst κ (φ ^ l • x₀ - x) q'` holds: for all `g` in `Γ'`, `p ^ κ`
times the pairing of this vector with `g • q' - q'` lies in the image of `W(𝔪^♭)`. -/
lemma SidePairing.isSafeMoveFst_of_neg_le_jumps {c' : S'.paramLattice} {P : S.SidePairing S'}
    {κ e e' t η l η₀ : ℕ} {d d₀ qOrders : ℕ → ℤ → ℤ} {x₀ x : S.extensionLattice.Ambient}
    {q' : S'.extensionLattice.Ambient} (hl : 0 < l) (h_kill : P.tateDualSide.KillsCokernel i κ t)
    (h_jumps_ge : ∀ a : ℕ, a < l → ∀ u ∈ S.jumpSet (i.stepBack a), -η ≤ u)
    (hx : x ∈ S.pointsOver c i e (raisedOrdersAtZero (-η)) d)
    (hx₀ : x₀ ∈ S.pointsOver c (i.stepBack l) e (raisedOrdersAtZero (-η₀)) d₀)
    (hq' : q' ∈ S'.pointsOver c' i e' qOrders (plainDepth t η l η₀)) :
    P.IsSafeMoveFst κ (φ ^ l • x₀ - x) q' := by
  have h_move : φ ^ l • x₀ - x ∈ S.kerWithOrders i
      (raisedOrdersAtZero (-η) ⊓ shiftedOrders l 0 (raisedOrdersAtZero (-η₀))) :=
    sub_mem_kerWithOrders_of_pointsOver hx (phi_pow_smul_mem_pointsOver hx₀)
  exact P.isSafeMoveFst_of_killsCokernel (l := 0) h_kill h_move hq'
    fun a u hu v _ ↦ ruleBound_zero_le_inf_add_plainDepth hl (fun ha ↦ h_jumps_ge a ha u hu) t η₀ v

/-- Plain cuts, the second side moves: the statement with the sides exchanged. Let `0 < l` and let
the jumps of `S'` at `i.stepBack a`, `a < l`, be at least `-η`. Let `x₀'` at `i.stepBack l` and `x'`
at `i` lie in `S'.pointsOver` over `p ^ e'` times the constant of `c'`. Let them have orders
`raisedOrdersAtZero (-η₀)`, `raisedOrdersAtZero (-η)`, with any depths `d₀'`, `d'`. Let
`p ^ κ * E ^ t` kill the cokernel of `P.tateDualSide` at `i` (`KillsCokernel`). Let `q` in
`S.pointsOver c i e` have any orders `qOrders` and depth `plainDepth t η l η₀`. This means it is
fixed by the subgroup `Γ'` of `k` modulo orders `-u`, raised by `t` at level `0`, by `η` below `l`,
by `η₀` at `l`. Then `P.IsSafeMoveSnd κ q (φ ^ l • x₀' - x')` holds: for all `g` in `Γ'`, `p ^ κ`
times the pairing of `g • q - q` with `g` applied to this vector lies in the image of `W(𝔪^♭)`. -/
lemma SidePairing.isSafeMoveSnd_of_up {c' : S'.paramLattice} {P : S.SidePairing S'}
    {κ e e' t η l η₀ : ℕ} {d' d₀' qOrders : ℕ → ℤ → ℤ} {x₀' x' : S'.extensionLattice.Ambient}
    {q : S.extensionLattice.Ambient} (hl : 0 < l) (h_kill : P.tateDualSide.KillsCokernel i κ t)
    (h_jumps_ge : ∀ a : ℕ, a < l → ∀ u ∈ S'.jumpSet (i.stepBack a), -η ≤ u)
    (hx' : x' ∈ S'.pointsOver c' i e' (raisedOrdersAtZero (-η)) d')
    (hx₀' : x₀' ∈ S'.pointsOver c' (i.stepBack l) e' (raisedOrdersAtZero (-η₀)) d₀')
    (hq : q ∈ S.pointsOver c i e qOrders (plainDepth t η l η₀)) :
    P.IsSafeMoveSnd κ q (φ ^ l • x₀' - x') := by
  have h_move : φ ^ l • x₀' - x' ∈ S'.kerWithOrders i
      (raisedOrdersAtZero (-η) ⊓ shiftedOrders l 0 (raisedOrdersAtZero (-η₀))) :=
    sub_mem_kerWithOrders_of_pointsOver hx' (phi_pow_smul_mem_pointsOver hx₀')
  exact P.isSafeMoveSnd_of_killsCokernel (l := 0) h_kill h_move hq
    fun a u hu v _ ↦ ruleBound_zero_le_inf_add_plainDepth hl (fun ha ↦ h_jumps_ge a ha u hu) t η₀ v

/-- A point with a pole of order at most `η` and the depth `plainDepth t η l η₀` asked at a plain
cut is standard, as this depth is at least `standardDepth t η l`. -/
lemma mem_standardPoints_of_plainDepth {e t η l η₀ : ℕ} {x : S.extensionLattice.Ambient}
    (hx : x ∈ S.pointsOver c i e (raisedOrdersAtZero (-η)) (plainDepth t η l η₀)) :
    x ∈ S.standardPoints c i e t η l :=
  mem_pointsOver_of_le hx (fun _ _ _ ↦ le_rfl) fun _ _ _ ↦ le_add_of_nonneg_right (by positivity)

/-- A plain cut: at the `l` letters up to `i` the jumps of the first side are at most `η` (it is
down) and those of the second at least `-η` (it is up). Let `p ^ κ * E ^ t` kill the cokernel of the
Tate dual side at `i` (`E` the Eisenstein polynomial), let `x₀'`, `x'` have poles of order at most
`η₀`, `η` at `E`, and let `x` have a pole of order at most `η` and be fixed by `Γ'` modulo orders
`plainDepth t η l η₀`. Then some stop `q` of the first side can rest while the move by
`φ ^ l x₀' - x'` is safe, `φ` being the Frobenius; `x` is one. -/
lemma SidePairing.exists_mem_stopPoints_isSafeMoveSnd {c' : S'.paramLattice} {P : S.SidePairing S'}
    {κ e e' t η l η₀ : ℕ} {d' d₀' : ℕ → ℤ → ℤ} {x : S.extensionLattice.Ambient}
    {x₀' x' : S'.extensionLattice.Ambient} (hl : 0 < l)
      (h_kill : P.tateDualSide.KillsCokernel i κ t)
    (h_down : ∀ a : ℕ, a < l → ∀ u ∈ S.jumpSet (i.stepBack a), u ≤ η)
    (h_up : ∀ a : ℕ, a < l → ∀ u ∈ S'.jumpSet (i.stepBack a), -η ≤ u)
    (hx : x ∈ S.pointsOver c i e (raisedOrdersAtZero (-η)) (plainDepth t η l η₀))
    (hx' : x' ∈ S'.pointsOver c' i e' (raisedOrdersAtZero (-η)) d')
    (hx₀' : x₀' ∈ S'.pointsOver c' (i.stepBack l) e' (raisedOrdersAtZero (-η₀)) d₀') :
    ∃ q ∈ S.stopPoints c i e η l, P.IsSafeMoveSnd κ q (φ ^ l • x₀' - x') :=
  ⟨x, mem_stopPoints_of_down hl h_down (mem_standardPoints_of_plainDepth hx),
    P.isSafeMoveSnd_of_up hl h_kill h_up hx' hx₀' hx⟩

/-- A plain cut: at the `l` letters up to `i` the jumps of the second side are at most `η` (it is
down) and those of the first at least `-η` (it is up). Let `p ^ κ * E ^ t` kill the cokernel of the
Tate dual side at `i` (`E` the Eisenstein polynomial), let `x₀`, `x` have poles of order at most
`η₀`, `η` at `E`, and let `x'` have a pole of order at most `η` and be fixed by `Γ'` modulo orders
`plainDepth t η l η₀`. Then some stop `q'` of the second side can rest while the move by
`φ ^ l x₀ - x` is safe, `φ` being the Frobenius; `x'` is one. -/
lemma SidePairing.exists_mem_stopPoints_isSafeMoveFst {c' : S'.paramLattice} {P : S.SidePairing S'}
    {κ e e' t η l η₀ : ℕ} {d d₀ : ℕ → ℤ → ℤ} {x₀ x : S.extensionLattice.Ambient}
    {x' : S'.extensionLattice.Ambient} (hl : 0 < l) (h_kill : P.tateDualSide.KillsCokernel i κ t)
    (h_down : ∀ a : ℕ, a < l → ∀ u ∈ S'.jumpSet (i.stepBack a), u ≤ η)
    (h_up : ∀ a : ℕ, a < l → ∀ u ∈ S.jumpSet (i.stepBack a), -η ≤ u)
    (hx' : x' ∈ S'.pointsOver c' i e' (raisedOrdersAtZero (-η)) (plainDepth t η l η₀))
    (hx : x ∈ S.pointsOver c i e (raisedOrdersAtZero (-η)) d)
    (hx₀ : x₀ ∈ S.pointsOver c (i.stepBack l) e (raisedOrdersAtZero (-η₀)) d₀) :
    ∃ q' ∈ S'.stopPoints c' i e' η l, P.IsSafeMoveFst κ (φ ^ l • x₀ - x) q' :=
  ⟨x', mem_stopPoints_of_down hl h_down (mem_standardPoints_of_plainDepth hx'),
    P.isSafeMoveFst_of_neg_le_jumps hl h_kill h_up hx hx₀ hx'⟩

/-- A jump `u` of `U` in the windows (`FitsWindows η σ β V`: the low window `[-η, η]` or the far
window `σ [β, β + V]`) is low, or `u` lies in `[β, β + V]`, or `-u` does. -/
lemma low_or_far_of_fitsWindows {η β V : ℕ} {σ : ℤˣ} {U : Finset ℤ} {u : ℤ}
    (hU : FitsWindows η σ β V U) (hu : u ∈ U) :
    -η ≤ u ∧ u ≤ η ∨ β ≤ u ∧ u ≤ β + V ∨ β ≤ -u ∧ -u ≤ β + V :=
  (hU u hu).imp_right (Or.imp And.right And.right)

/-- A side is down, that is, its jumps are at most `η`, at a letter where they lie in the windows
`[-η, η]` and `σ [β, β + V]` and the far window is negative or ends at or below `η`. -/
lemma jump_le_of_fitsWindows {η β V : ℕ} {σ : ℤˣ} (hU : FitsWindows η σ β V (S.jumpSet i))
    (h_sign : σ = -1 ∨ β + V ≤ η) : ∀ u ∈ S.jumpSet i, u ≤ η := by
  intro u hu
  obtain h_low | ⟨h_pos, h_far⟩ | ⟨-, h_far⟩ := hU u hu
  · omega
  · obtain rfl | h_small := h_sign
    · exact absurd h_pos (by decide)
    · omega
  · omega

/-- A side is up, that is, its jumps are at least `-η`, at a letter where they lie in the windows
`[-η, η]` and `σ [β, β + V]` and the far window is positive or ends at or below `η` in modulus. -/
lemma neg_le_jump_of_fitsWindows {η β V : ℕ} {σ : ℤˣ} (hU : FitsWindows η σ β V (S.jumpSet i))
    (h_sign : σ = 1 ∨ β + V ≤ η) : ∀ u ∈ S.jumpSet i, -η ≤ u := by
  intro u hu
  obtain h_low | ⟨-, h_far⟩ | ⟨h_neg, h_far⟩ := hU u hu
  · omega
  · omega
  · obtain rfl | h_small := h_sign
    · exact absurd h_neg (by decide)
    · omega

end PairingSide

end New.Lift.KummerChart

end
