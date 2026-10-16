import GowersSzemeredi.Proofs16WithUnion
import GowersSzemeredi.Proofs16Interpolation

/-! Pointwise sums of multiply multilinear relations.

In dimension `k+1 ≥ 3` the remainder of Gowers's identity
`φ(x₀+h, x) = (-1)^k φ′(h, x) + φ″(h, x)` is a signed sum of the `2^k - 1`
other translated vertices. Each vertex is covered through a
lower-dimensional face. The remainder relation then lies in the
*pointwise sum* of the vertex relations. This module covers such sums.

* `relationSum Γ₁ Γ₂ = {(x, y₁ + y₂) : (x, y₁) ∈ Γ₁, (x, y₂) ∈ Γ₂}`.
* `MultiplyLinearWith.relationSum` covers the first relation at loss `λs`,
  then each of its cells for the second at loss `(1-λ)s`, as
  `MultiplyLinearWith.union` does. It then adds the two maps of every pair.
  Counts and width exponents both multiply.
* `MultiplyLinearWith.relationNeg`, and `relationScale` for multiplication
  by a constant (in particular the signs `(-1)^j`), keep the controls.

For a fixed number `2^k - 1` of summands the controls stay polynomial. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The pointwise sum of two relations. -/
def relationSum {N k : Nat} [NeZero N] (Gamma1 Gamma2 : Finset (Point N k × ZMod N)) :
    Finset (Point N k × ZMod N) := by
  classical
  exact ((Gamma1 ×ˢ Gamma2).filter (fun p => p.1.1 = p.2.1)).image
    (fun p => (p.1.1, p.1.2 + p.2.2))

theorem mem_relationSum {N k : Nat} [NeZero N] {Gamma1 Gamma2 : Finset (Point N k × ZMod N)}
    {x : Point N k} {y : ZMod N} (h : (x, y) ∈ relationSum Gamma1 Gamma2) :
    ∃ y1 y2, (x, y1) ∈ Gamma1 ∧ (x, y2) ∈ Gamma2 ∧ y = y1 + y2 := by
  unfold relationSum at h
  obtain ⟨⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩, hp, heq⟩ := Finset.mem_image.mp h
  obtain ⟨hp, hx⟩ := Finset.mem_filter.mp hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  dsimp only at hx
  subst hx
  exact ⟨y1, y2, h1, h2, rfl⟩

theorem relationSum_mono {N k : Nat} [NeZero N] {G1 G2 G1' G2' : Finset (Point N k × ZMod N)}
    (h1 : G1 ⊆ G1') (h2 : G2 ⊆ G2') : relationSum G1 G2 ⊆ relationSum G1' G2' := by
  intro z hz
  obtain ⟨x, y⟩ := z
  obtain ⟨y1, y2, hy1, hy2, rfl⟩ := mem_relationSum hz
  unfold relationSum
  exact Finset.mem_image.mpr ⟨((x, y1), (x, y2)),
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1 hy1, h2 hy2⟩, rfl⟩, rfl⟩

/-- The pairwise sums of two families of maps. -/
def sumMultilinearFamily {N k p q : Nat} (nu : Fin p → Point N k → ZMod N)
    (mu : Fin q → Point N k → ZMod N) (i : Fin (p * q)) : Point N k → ZMod N :=
  fun x => nu (finProdFinEquiv.symm i).1 x + mu (finProdFinEquiv.symm i).2 x

theorem sumMultilinearFamily_isMultilinear {N k p q : Nat}
    (nu : Fin p → Point N k → ZMod N) (mu : Fin q → Point N k → ZMod N)
    (hnu : ∀ i, IsMultilinear (nu i)) (hmu : ∀ i, IsMultilinear (mu i))
    (i : Fin (p * q)) : IsMultilinear (sumMultilinearFamily nu mu i) :=
  (hnu _).add (hmu _)

theorem sumMultilinearFamily_pair {N k p q : Nat}
    (nu : Fin p → Point N k → ZMod N) (mu : Fin q → Point N k → ZMod N) (a : Fin p) (b : Fin q)
    (x : Point N k) :
    sumMultilinearFamily nu mu (finProdFinEquiv (a, b)) x = nu a x + mu b x := by
  unfold sumMultilinearFamily
  rw [Equiv.symm_apply_apply]

/-- **The pointwise sum of two relations.** Counts and width exponents
multiply. -/
theorem MultiplyLinearWith.relationSum {N k : Nat} [NeZero N]
    {Q1 E1 Q2 E2 : Real → Real} {Gamma1 Gamma2 : Finset (Point N k × ZMod N)}
    (h1 : MultiplyLinearWith Q1 E1 Gamma1) (h2 : MultiplyLinearWith Q2 E2 Gamma2)
    {lam : Real} (hl : 0 < lam) (hl1 : lam < 1)
    (hQ2 : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Q2 s)
    (hE2 : ∀ s, 0 < s → s ≤ 1 → 0 ≤ E2 s) :
    MultiplyLinearWith (fun s => Q1 (lam * s) * Q2 ((1 - lam) * s))
      (fun s => E1 (lam * s) * E2 ((1 - lam) * s)) (relationSum Gamma1 Gamma2) := by
  intro s hs hs1 P hP
  have ha : 0 < lam * s := mul_pos hl hs
  have ha1 : lam * s ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hl1.le hs.le]
  have hb : 0 < (1 - lam) * s := mul_pos (by linarith) hs
  have hb1 : (1 - lam) * s ≤ 1 := by nlinarith [mul_pos hl hs]
  obtain ⟨M1, q1, H1, B, nu, hH1sub, hH1mass, hBpart, hBproper, hq1, hBwidth, hnu, hcov1⟩ :=
    h1 (lam * s) ha ha1 P hP
  obtain ⟨q2, G, L, R, mu, hq2, hGsub, hGmass, hRpart, hRproper, hRwidth, hmu, hcov2⟩ :=
    h2.on_partition ((1 - lam) * s) hb hb1 (hQ2 _ hb hb1) P B hBpart hBproper
  let e := section5NatFlattenEquiv L
  refine ⟨∑ j, L j, q1 * q2, H1 ∩ G, boxFlatten L R,
    fun j => sumMultilinearFamily (nu (e.symm j).1) (mu (e.symm j).1 (e.symm j).2),
    ?_, ?_, boxFlatten_partition P B L R hBpart hRpart, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.inter_subset_left.trans hH1sub
  · have hsub : H1 ∪ G ⊆ P.carrier := Finset.union_subset hH1sub hGsub
    have hcu : ((H1 ∪ G).card : Real) ≤ P.carrier.card := by
      exact_mod_cast Finset.card_le_card hsub
    have hui : ((H1 ∪ G).card : Real) + (H1 ∩ G).card = H1.card + G.card := by
      exact_mod_cast Finset.card_union_add_card_inter H1 G
    have key : (1 - s) * (P.carrier.card : Real) =
        (1 - lam * s) * P.carrier.card + (1 - (1 - lam) * s) * P.carrier.card -
          P.carrier.card := by ring
    rw [key]
    linarith
  · intro j
    exact hRproper (e.symm j).1 (e.symm j).2
  · show ((q1 * q2 : Nat) : Real) ≤ Q1 (lam * s) * Q2 ((1 - lam) * s)
    push_cast
    exact mul_le_mul hq1 hq2 (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hq1)
  · intro j
    show (P.width : Real) ^ (E1 (lam * s) * E2 ((1 - lam) * s)) ≤
      ((R (e.symm j).1 (e.symm j).2).width : Real)
    rw [Real.rpow_mul (Nat.cast_nonneg _)]
    exact (Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hBwidth _)
      (hE2 _ hb hb1)).trans (hRwidth _ _)
  · intro j i
    exact sumMultilinearFamily_isMultilinear _ _ (hnu _) (hmu _ _) i
  · intro j x hx hxH y hxy
    have hxR : x ∈ (R (e.symm j).1 (e.symm j).2).carrier := hx
    have hxB : x ∈ (B (e.symm j).1).carrier := IsPartition.cell_subset (hRpart _) _ hxR
    obtain ⟨y1, y2, hy1, hy2, rfl⟩ := mem_relationSum hxy
    obtain ⟨a, ha⟩ := hcov1 _ x hxB (Finset.mem_inter.mp hxH).1 y1 hy1
    obtain ⟨b, hb⟩ := hcov2 _ _ x hxR (Finset.mem_inter.mp hxH).2 y2 hy2
    refine ⟨finProdFinEquiv (a, b), ?_⟩
    show y1 + y2 = sumMultilinearFamily (nu (e.symm j).1) (mu (e.symm j).1 (e.symm j).2)
      (finProdFinEquiv (a, b)) x
    rw [sumMultilinearFamily_pair, ← ha, ← hb]

/-- Multiplying the values by a constant keeps the controls. -/
def relationScale {N k : Nat} [NeZero N] (c : ZMod N) (Gamma : Finset (Point N k × ZMod N)) :
    Finset (Point N k × ZMod N) :=
  Gamma.image fun z => (z.1, c * z.2)

theorem MultiplyLinearWith.relationScale {N k : Nat} [NeZero N] {Q E : Real → Real}
    {Gamma : Finset (Point N k × ZMod N)} (h : MultiplyLinearWith Q E Gamma) (c : ZMod N) :
    MultiplyLinearWith Q E (relationScale c Gamma) := by
  intro s hs hs1 P hP
  obtain ⟨M, q, H, R, mu, hH, hmass, hpart, hproper, hq, hwidth, hmu, hcover⟩ :=
    h s hs hs1 P hP
  refine ⟨M, q, H, R, fun j i x => c * mu j i x, hH, hmass, hpart, hproper, hq, hwidth,
    fun j i => (hmu j i).const_mul c, ?_⟩
  intro j x hx hxH y hxy
  obtain ⟨⟨x', y'⟩, hz, heq⟩ := Finset.mem_image.mp hxy
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  obtain ⟨i, hi⟩ := hcover j x' hx hxH y' hz
  exact ⟨i, by rw [hi]⟩

end LeanProofs.GowersSzemeredi
