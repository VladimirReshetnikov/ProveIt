import GowersSzemeredi.Proofs16FreimanTranslateCover

/-! A dense translated overlap covers the mixed difference graph by
few translates of a single fourfold graph difference set. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem common_graph_difference_cover {N : Nat} [NeZero N]
    (A B S : Finset (ZMod N)) (f g : ZMod N → ZMod N) (a c : ZMod N)
    (hSB : S ⊆ B) (hagree : ∀ s ∈ S, s+a ∈ A ∧ f (s+a) = g s+c)
    (hf : IsFreimanLinearOn A f) (hg : IsFreimanLinearOn B g)
    {mu : Real} (hmu : 0 < mu) (hS : mu*N ≤ (S.card : Real)) :
    ∃ J ⊆ A, ∃ K ⊆ B,
      (J.card : Real)*mu ≤ 1 ∧ (K.card : Real)*mu ≤ 1 ∧
      (J.card : Real)*K.card*mu^2 ≤ 1 ∧
      ∀ x ∈ A, ∀ y ∈ B, ∃ j ∈ J, ∃ k ∈ K,
        ∃ u ∈ S, ∃ v ∈ S, ∃ w ∈ S, ∃ z ∈ S,
          x-y = (j-k)+(u-v)-(w-z) ∧
          f x-g y = (f j-g k)+(g u-g v)-(g w-g z) := by
  let C := S.image fun s => s+a
  have hCA : C ⊆ A := by
    intro t ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
    exact (hagree s hs).1
  have hC : mu*N ≤ (C.card : Real) := by
    simpa only [C,Finset.card_image_of_injective _ (add_left_injective a)] using hS
  obtain ⟨J,hJA,hJ,hcoverA⟩ := freiman_graph_translate_cover A C f hCA hf hmu hC
  obtain ⟨K,hKB,hK,hcoverB⟩ := freiman_graph_translate_cover B S g hSB hg hmu hS
  refine ⟨J,hJA,K,hKB,hJ,hK,?_,?_⟩
  · have h := mul_le_mul hJ hK (mul_nonneg (Nat.cast_nonneg _) hmu.le) (by norm_num)
    nlinarith [h]
  · intro x hx y hy
    obtain ⟨j,hj,u,hu,v,hv,hx,hfx⟩ := hcoverA x hx
    obtain ⟨u,huS,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v,hvS,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨k,hk,w,hw,z,hz,hy,hgy⟩ := hcoverB y hy
    refine ⟨j,hj,k,hk,u,huS,v,hvS,w,hw,z,hz,?_,?_⟩
    · linear_combination hx-hy
    · rw [(hagree u huS).2,(hagree v hvS).2] at hfx
      linear_combination hfx-hgy

/-- Dense mixed configurations supply the overlap used by the cover;
none of the original configurations is discarded in this conclusion. -/
theorem mixed_configurations_common_graph_cover {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (f : Fin 4 → ZMod N → ZMod N)
    (Q : Finset (Fin 4 → ZMod N))
    (hQ : Q ⊆ mixedColumnQuadruples Finset.univ f)
    (hA : ∀ q ∈ Q, q 0 ∈ A) (hB : ∀ q ∈ Q, q 1 ∈ B)
    (hf : IsFreimanLinearOn A (f 0)) (hg : IsFreimanLinearOn B (f 1))
    {delta : Real} (hdelta : 0 < delta) (hcount : delta*(N : Real)^3 ≤ Q.card) :
    ∃ S ⊆ B, delta*N ≤ (S.card : Real) ∧
      ∃ J ⊆ A, ∃ K ⊆ B, (J.card : Real)*K.card*delta^2 ≤ 1 ∧
      ∀ q ∈ Q, ∃ j ∈ J, ∃ k ∈ K,
        ∃ u ∈ S, ∃ v ∈ S, ∃ w ∈ S, ∃ z ∈ S,
          q 0-q 1 = (j-k)+(u-v)-(w-z) ∧
          f 0 (q 0)-f 1 (q 1) = (f 0 j-f 1 k)+(f 1 u-f 1 v)-(f 1 w-f 1 z) := by
  obtain ⟨a,c,S,hSB,hS,hagree⟩ := mixed_configurations_dense_overlap A B f Q hQ hA hB hcount
  obtain ⟨J,hJA,K,hKB,_,_,hJK,hcover⟩ :=
    common_graph_difference_cover A B S (f 0) (f 1) a c hSB hagree hf hg hdelta hS
  exact ⟨S,hSB,hS,J,hJA,K,hKB,hJK,fun q hq => hcover (q 0) (hA q hq) (q 1) (hB q hq)⟩

end LeanProofs.GowersSzemeredi
