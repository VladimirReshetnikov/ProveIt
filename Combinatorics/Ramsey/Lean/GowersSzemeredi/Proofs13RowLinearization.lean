import GowersSzemeredi.Proofs13CommonRows

/-!
# The domain and affine-row steps in Lemma 13.7

The set in the printed construction consists of upper endpoints of selected
vertical edges with a common lower height. Its containment in the original
domain follows from the edge condition. Adding the affine base row to the
affine vertical difference proves the required linearity of each upper row.
The progression selection and quantitative averaging remain separate.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace LeanProofs.GowersSzemeredi

/-- The selected upper endpoints above a fixed base row. -/
def stage137UpperEndpoints {N : Nat} (S I : Finset (ZMod N))
    (Y : ZMod N → Finset (Pair N)) (y : ZMod N) : Finset (Pair N) :=
  (S.product (translateFinset I y)).filter fun z ↦ (z.1, y) ∈ Y (z.2 - y)

/-- Membership on an indexed upper row reduces to the chosen vertical edge. -/
theorem mem_stage137UpperEndpoints {N : Nat} (S I : Finset (ZMod N))
    (Y : ZMod N → Finset (Pair N)) (y x h : ZMod N) :
    (x, y + h) ∈ stage137UpperEndpoints S I Y y ↔
      x ∈ S ∧ h ∈ I ∧ (x, y) ∈ Y h := by
  classical
  constructor
  · intro hz
    obtain ⟨hprod, hY⟩ := Finset.mem_filter.mp hz
    obtain ⟨hx, ht⟩ := Finset.mem_product.mp hprod
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp ht
    have hth : t = h := add_left_cancel heq
    exact ⟨hx, hth ▸ ht, by simpa only [add_sub_cancel_left] using hY⟩
  · rintro ⟨hx, hh, hY⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨hx, Finset.mem_image.mpr ⟨h, hh, rfl⟩⟩,
      by simpa only [add_sub_cancel_left] using hY⟩

/-- The edge-domain condition gives precisely the containment missing from
 the earlier Stage 13.7 encoding. -/
theorem stage137UpperEndpoints_subset_domain {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (S I : Finset (ZMod N))
    (Y : ZMod N → Finset (Pair N)) (y : ZMod N)
    (hY : ∀ h ∈ I, Y h ⊆ verticalEdgeDomain A h) :
    stage137UpperEndpoints S I Y y ⊆ A := by
  classical
  intro z hz
  obtain ⟨hzprod, hzY⟩ := Finset.mem_filter.mp hz
  obtain ⟨h, hh, heq⟩ := Finset.mem_image.mp (Finset.mem_product.mp hzprod).2
  have hsub : z.2 - y = h := by rw [← heq]; simp
  rw [hsub] at hzY
  have he := (Finset.mem_filter.mp (hY h hh hzY)).2.2
  simpa only [heq, Prod.mk.eta] using he

/-- Adding a linear base row and a linear vertical difference makes each
selected upper row linear. -/
theorem stage137UpperEndpoints_rows_linear {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (phi : Pair N → ZMod N)
    (R S I : Finset (ZMod N)) (Y : ZMod N → Finset (Pair N))
    (y : ZMod N) (hSR : S ⊆ R)
    (hY : ∀ h ∈ I, Y h ⊆ verticalEdgeDomain A h)
    (hbase : LinearOn (S.filter fun x ↦ (x, y) ∈ A) (fun x ↦ phi (x, y)))
    (hdiff : ∀ h ∈ I, LinearOnDomain ((Y h).filter fun z ↦ z.1 ∈ R)
      (fun z ↦ z.1) (verticalPhiDifference phi h)) :
    ∀ h ∈ I, LinearOn
      (translatedRow S (stage137UpperEndpoints S I Y y) y h)
      (fun x ↦ phi (x, y + h)) := by
  classical
  obtain ⟨a, b, hbase⟩ := hbase
  intro h hh
  obtain ⟨c, d, hdiff⟩ := hdiff h hh
  refine ⟨a + c, b + d, ?_⟩
  intro x hx
  obtain ⟨hxS, _, hxY⟩ := (mem_stage137UpperEndpoints S I Y y x h).mp
    (Finset.mem_filter.mp hx).2
  have hxA : (x, y) ∈ A := (Finset.mem_filter.mp (hY h hh hxY)).2.1
  have hb := hbase x (Finset.mem_filter.mpr ⟨hxS, hxA⟩)
  have hd := hdiff (x, y) (Finset.mem_filter.mpr ⟨hxY, hSR hxS⟩)
  dsimp only [verticalPhiDifference] at hd
  linear_combination hb + hd

end LeanProofs.GowersSzemeredi
