import DiophantineConsistency.FieldMarkerHigh
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FieldMarkerColumns
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry CompactSymbolicPorts CompactPartialBand
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem vertical (N C k : V) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N))) (hp : k%8807=(1022:V))
    (hslots : ∀ x<8807*N, 0<x → NoCarry (dig 67 C x) (dig 67 (lowNat:V) (x%8807))) :
    RawParityBands.selectorsAt (8807*N) C k 4393=0 ∧
    RawParityBands.selectorsAt (8807*N) C k 5495=0 ∧
    RawColumnBands.bareColumn (8807*N) C k=dig 67 (rot 67 (8807*N) C (30%(8807*N))) k := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  have hs1 (j : Fin 943) : selectorDigit (8807*N) C k 4393 j=0 := by
    have h := FieldExactZero.rotated_zero N C k 1022 (4393-j.val) hN hk hC hp
      (VerticalMarkerGeometry.selectors j.val j.isLt).1 hslots
    rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn] at h
    exact h
  have hs2 (j : Fin 943) : selectorDigit (8807*N) C k 5495 j=0 := by
    have h := FieldExactZero.rotated_zero N C k 1022 (5495-j.val) hN hk hC hp
      (VerticalMarkerGeometry.selectors j.val j.isLt).2 hslots
    rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn] at h
    exact h
  have hb (j : Fin 5) (hj : j≠⟨0,by decide⟩) :
      dig 67 (rot 67 (8807*N) C (TwoBand.bareOffset j%(8807*N))) k=0 := by
    apply FieldExactZero.rotated_zero N C k 1022 (![30,62,1100,2201,8849] j) hN hk hC hp
      (VerticalMarkerGeometry.bare j hj) hslots
  refine ⟨?_,?_,?_⟩
  · simp only [RawParityBands.selectorsAt,hs1,Finset.sum_const_zero]
  · simp only [RawParityBands.selectorsAt,hs2,Finset.sum_const_zero]
  · unfold RawColumnBands.bareColumn
    rw [Finset.sum_eq_single ⟨0,by decide⟩]
    · simp [TwoBand.bareOffset]
    · intro j _ hj; exact hb j hj
    · intro h; exact (h (Finset.mem_univ _)).elim

theorem horizontal (N C k : V) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N))) (hp : k%8807=(1073:V))
    (hslots : ∀ x<8807*N, 0<x → NoCarry (dig 67 C x) (dig 67 (lowNat:V) (x%8807))) :
    RawParityBands.selectorsAt (8807*N) C k 4393=0 ∧
    RawParityBands.selectorsAt (8807*N) C k 5495=0 ∧
    RawColumnBands.bareColumn (8807*N) C k=
      dig 67 (rot 67 (8807*N) C (62%(8807*N))) k+
      dig 67 (rot 67 (8807*N) C (8849%(8807*N))) k := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  have hs1 (j : Fin 943) : selectorDigit (8807*N) C k 4393 j=0 := by
    have h := FieldExactZero.rotated_zero N C k 1073 (4393-j.val) hN hk hC hp
      (HorizontalMarkerGeometry.selectors j.val j.isLt).1 hslots
    rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn] at h
    exact h
  have hs2 (j : Fin 943) : selectorDigit (8807*N) C k 5495 j=0 := by
    have h := FieldExactZero.rotated_zero N C k 1073 (5495-j.val) hN hk hC hp
      (HorizontalMarkerGeometry.selectors j.val j.isLt).2 hslots
    rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn] at h
    exact h
  have hb (j : Fin 5) (h1 : j≠⟨1,by decide⟩) (h4 : j≠⟨4,by decide⟩) :
      dig 67 (rot 67 (8807*N) C (TwoBand.bareOffset j%(8807*N))) k=0 := by
    apply FieldExactZero.rotated_zero N C k 1073 (![30,62,1100,2201,8849] j) hN hk hC hp
      (HorizontalMarkerGeometry.bare j h1 h4) hslots
  have hsum (f : Fin 5→V) (h0 : f ⟨0,by decide⟩=0) (h2 : f ⟨2,by decide⟩=0) (h3 : f ⟨3,by decide⟩=0) :
      (∑ j,f j)=f ⟨1,by decide⟩+f ⟨4,by decide⟩ := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
    change f ⟨0,by decide⟩+(f ⟨1,by decide⟩+(f ⟨2,by decide⟩+(f ⟨3,by decide⟩+(f ⟨4,by decide⟩+0)))) = _
    rw [h0,h2,h3]
    simp
  refine ⟨?_,?_,?_⟩
  · simp only [RawParityBands.selectorsAt,hs1,Finset.sum_const_zero]
  · simp only [RawParityBands.selectorsAt,hs2,Finset.sum_const_zero]
  · unfold RawColumnBands.bareColumn
    have h := hsum (fun j => dig 67 (rot 67 (8807*N) C (TwoBand.bareOffset j%(8807*N))) k)
      (hb ⟨0,by decide⟩ (by decide) (by decide)) (hb ⟨2,by decide⟩ (by decide) (by decide))
      (hb ⟨3,by decide⟩ (by decide) (by decide))
    simpa [TwoBand.bareOffset] using h
#print axioms FieldMarkerColumns.vertical
#print axioms FieldMarkerColumns.horizontal
end FieldMarkerColumns
