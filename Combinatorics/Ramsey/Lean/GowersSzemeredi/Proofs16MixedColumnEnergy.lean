import GowersSzemeredi.Proofs16MatchingKeys

/-! Four different column maps can be compared through mixed pair keys.
Two Cauchy--Schwarz steps recover the energy of any one map. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def mixedPairKey {N : Nat} (f g : ZMod N → ZMod N) (p : ZMod N × ZMod N) :=
  (p.1-p.2,f p.1-g p.2)

def mixedColumnEnergy {N : Nat} (A B C D : Finset (ZMod N))
    (f g h l : ZMod N → ZMod N) : Nat :=
  keyMatchingCount (A ×ˢ B) (C ×ˢ D) (mixedPairKey f g) (mixedPairKey h l)

/-- Regroup a self-comparison of two maps into a comparison of their
ordinary difference keys. -/
theorem mixedColumnEnergy_self_regroup {N : Nat}
    (A B : Finset (ZMod N)) (f g : ZMod N → ZMod N) :
    mixedColumnEnergy A B A B f g f g =
      keyMatchingCount (A ×ˢ A) (B ×ˢ B) (pairKey f) (pairKey g) := by
  unfold mixedColumnEnergy keyMatchingCount
  apply Finset.card_bij (fun p _ => ((p.1.1,p.2.1),(p.1.2,p.2.2)))
  · intro p hp
    obtain ⟨hp,hkey⟩ := Finset.mem_filter.mp hp
    obtain ⟨⟨ha,hb⟩,hc,hd⟩ := (by simpa only [Finset.mem_product] using hp)
    have he : p.1.1-p.1.2 = p.2.1-p.2.2 ∧ f p.1.1-g p.1.2 = f p.2.1-g p.2.2 :=
      Prod.mk.inj hkey
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨ha,hc⟩,Finset.mem_product.mpr ⟨hb,hd⟩⟩,?_⟩
    apply Prod.ext
    · change p.1.1-p.2.1 = p.1.2-p.2.2
      linear_combination he.1
    · change f p.1.1-f p.2.1 = g p.1.2-g p.2.2
      linear_combination he.2
  · intro p _ q _ he
    simp only [Prod.mk.injEq] at he
    exact Prod.ext (Prod.ext he.1.1 he.2.1) (Prod.ext he.1.2 he.2.2)
  · intro p hp
    obtain ⟨hp,hkey⟩ := Finset.mem_filter.mp hp
    obtain ⟨⟨ha,hc⟩,hb,hd⟩ := (by simpa only [Finset.mem_product] using hp)
    have he : p.1.1-p.1.2 = p.2.1-p.2.2 ∧ f p.1.1-f p.1.2 = g p.2.1-g p.2.2 :=
      Prod.mk.inj hkey
    refine ⟨((p.1.1,p.2.1),(p.1.2,p.2.2)),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨ha,hb⟩,Finset.mem_product.mpr ⟨hc,hd⟩⟩,?_⟩,rfl⟩
    apply Prod.ext
    · change p.1.1-p.2.1 = p.1.2-p.2.2
      linear_combination he.1
    · change f p.1.1-g p.2.1 = f p.1.2-g p.2.2
      linear_combination he.2

theorem mixedColumnEnergy_self_sq_le {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (f g : ZMod N → ZMod N) :
    (mixedColumnEnergy A B A B f g f g)^2 ≤ phiAdditiveCount A f * phiAdditiveCount B g := by
  rw [mixedColumnEnergy_self_regroup]
  have h := keyMatchingCount_sq_le (A ×ˢ A) (B ×ˢ B) (pairKey f) (pairKey g)
  change _ ≤ pairEnergy (A ×ˢ A) (A ×ˢ A) f * pairEnergy (B ×ˢ B) (B ×ˢ B) g at h
  simpa only [pairEnergy_self_eq_phiAdditiveCount] using h

/-- A four-map comparison is controlled by the product of the four
individual respected-quadruple counts. -/
theorem mixedColumnEnergy_fourth_le {N : Nat} [NeZero N]
    (A B C D : Finset (ZMod N)) (f g h l : ZMod N → ZMod N) :
    (mixedColumnEnergy A B C D f g h l)^4 ≤
      (phiAdditiveCount A f * phiAdditiveCount B g) * (phiAdditiveCount C h * phiAdditiveCount D l) := by
  have hcs := keyMatchingCount_sq_le (A ×ˢ B) (C ×ˢ D) (mixedPairKey f g) (mixedPairKey h l)
  have hpow := Nat.pow_le_pow_left hcs 2
  calc _ = ((mixedColumnEnergy A B C D f g h l)^2)^2 := by ring
    _ ≤ (mixedColumnEnergy A B A B f g f g * mixedColumnEnergy C D C D h l h l)^2 := hpow
    _ = (mixedColumnEnergy A B A B f g f g)^2 * (mixedColumnEnergy C D C D h l h l)^2 := by ring
    _ ≤ _ := Nat.mul_le_mul (mixedColumnEnergy_self_sq_le A B f g) (mixedColumnEnergy_self_sq_le C D h l)

/-- When three maps have unrestricted domains, the fourth power of the
mixed count forces energy on the first map's specified domain. -/
theorem mixedColumnEnergy_coordinate_bound {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (f g h l : ZMod N → ZMod N) :
    (mixedColumnEnergy A Finset.univ Finset.univ Finset.univ f g h l)^4 ≤
      phiAdditiveCount A f * N^9 := by
  have hub (u : ZMod N → ZMod N) : phiAdditiveCount Finset.univ u ≤ N^3 := by
    rw [← pairEnergy_self_eq_phiAdditiveCount,Finset.univ_product_univ]
    exact pairEnergy_univ_le u
  calc _ ≤ _ := mixedColumnEnergy_fourth_le A Finset.univ Finset.univ Finset.univ f g h l
    _ ≤ (phiAdditiveCount A f * N^3) * (N^3 * N^3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (hub g)) (Nat.mul_le_mul (hub h) (hub l))
    _ = _ := by ring

end LeanProofs.GowersSzemeredi
