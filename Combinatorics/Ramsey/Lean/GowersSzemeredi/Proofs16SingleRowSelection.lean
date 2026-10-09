import GowersSzemeredi.Proofs16UnifiedRowBohrDomains

/-! Choose one of four local maps at each point. A common Freiman-frequency
Bohr domain allows the chosen maps to form one coherent family. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def labeledRowSupport {N : Nat} [NeZero N] (Q : Finset (Fin 4 → ZMod N))
    (color : ZMod N → Fin 4) : Finset (ZMod N) :=
  Finset.univ.filter fun x => x ∈ anchorRowSupport Q (color x)

theorem labeledRowSupport_witness {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (color : ZMod N → Fin 4)
    {x : ZMod N} (hx : x ∈ labeledRowSupport Q color) :
    ∃ b ∈ Q, b (color x) = x := Finset.mem_image.mp (Finset.mem_filter.mp hx).2

theorem coherent_four_rows_to_single {N m : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (P : Finset (ZMod N))
    (J : Fin 4 → Finset (Fin m)) (c : Fin 4 → Fin m → ZMod N)
    (psi : Fin 4 → Fin m → ZMod N → ZMod N) (F : Fin 4 → ZMod N → ZMod N → ZMod N)
    (sigma : Real) {kappa : Real}
    (hadd : ∀ b ∈ Q, b 0+b 1 = b 2+b 3) (hP : ∀ b ∈ Q, ∀ j, b j ∈ P)
    (hmass : kappa*(N : Real)^3 ≤ Q.card) (hN : 8 ≤ kappa*(N : Real))
    (hlocal : ∀ b ∈ Q, ∀ j,
      IsFreimanLinearOn (affineRowBohrDomain J c psi sigma j (b j)) (F j (b j)) ∧ F j (b j) 0 = 0)
    (hcoherent : ∀ b ∈ Q, ∀ z,
      (∀ j, z ∈ affineRowBohrDomain J c psi sigma j (b j)) →
        F 0 (b 0) z+F 1 (b 1) z = F 2 (b 2) z+F 3 (b 3) z) :
    ∃ (color : ZMod N → Fin 4) (R : Finset (Fin 4 → ZMod N)),
      R ⊆ Q ∧ (kappa/512)*(N : Real)^3 ≤ R.card ∧
      labeledRowSupport Q color ⊆ P ∧
      (kappa/512)*N ≤ ((labeledRowSupport Q color).card : Real) ∧
      (∀ x ∈ labeledRowSupport Q color,
        IsFreimanLinearOn (unifiedRowBohrDomain J c psi sigma x) (F (color x) x) ∧
          F (color x) x 0 = 0) ∧
      ∀ b ∈ R, b 0+b 1 = b 2+b 3 ∧ Function.Injective b ∧
        (∀ j, b j ∈ labeledRowSupport Q color ∧ color (b j) = j) ∧
        ∀ z, (∀ j, z ∈ unifiedRowBohrDomain J c psi sigma (b j)) →
          F (color (b 0)) (b 0) z+F (color (b 1)) (b 1) z =
            F (color (b 2)) (b 2) z+F (color (b 3)) (b 3) z := by
  obtain ⟨color,R,hRQ,hR,hlabels⟩ := exists_dense_quadruple_row_labels Q hadd hmass hN
  have hmem (b : Fin 4 → ZMod N) (hb : b ∈ R) (j : Fin 4) :
      b j ∈ labeledRowSupport Q color := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rw [(hlabels b hb).2 j]
    exact Finset.mem_image.mpr ⟨b,hRQ hb,rfl⟩
  refine ⟨color,R,hRQ,hR,?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨b,hb,he⟩ := labeledRowSupport_witness Q color hx
    exact he ▸ hP b hb (color x)
  · have hrow := additive_quadruples_row_density R (fun b hb => hadd b (hRQ hb)) hR 0
    have hsub : anchorRowSupport R 0 ⊆ labeledRowSupport Q color := by
      intro x hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
      exact hmem b hb 0
    exact hrow.trans (by exact_mod_cast Finset.card_le_card hsub)
  · intro x hx
    obtain ⟨b,hb,he⟩ := labeledRowSupport_witness Q color hx
    have h := hlocal b hb (color x)
    rw [he] at h
    exact ⟨h.1.mono (unifiedRowBohrDomain_subset J c psi sigma (color x) x),h.2⟩
  · intro b hb
    refine ⟨hadd b (hRQ hb),(hlabels b hb).1,fun j => ⟨hmem b hb j,(hlabels b hb).2 j⟩,?_⟩
    intro z hz
    simp only [(hlabels b hb).2] 
    exact hcoherent b (hRQ hb) z (fun j => unifiedRowBohrDomain_subset J c psi sigma j (b j) (hz j))

end LeanProofs.GowersSzemeredi
