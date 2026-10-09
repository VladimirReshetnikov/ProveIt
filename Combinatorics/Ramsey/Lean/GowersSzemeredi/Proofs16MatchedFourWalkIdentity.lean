import GowersSzemeredi.Proofs16FourStepIdentity
import GowersSzemeredi.Proofs16FourWalkDifferences

/-! Walks with matching edge differences transport coherent local
column identities to their endpoints. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem matched_four_walk_relation {N d : Nat} [NeZero N] [Fact N.Prime]
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (E : Finset (ZMod N × ZMod N))
    {rho r : Real} (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hzero : ∀ x ∈ X, L x 0 = 0) (hEX : E ⊆ X ×ˢ X)
    (hcoh : ∀ p ∈ E, ∀ q ∈ E, p.1-p.2 = q.1-q.2 → ColumnPairIdentity T L r p q)
    {u v u' v' : ZMod N} {t t' : ZMod N × ZMod N × ZMod N}
    (ht : t ∈ graphFourWalks (fun a b => (a,b) ∈ E) u v)
    (ht' : t' ∈ graphFourWalks (fun a b => (a,b) ∈ E) u' v')
    (hd : fourWalkSteps u v t = fourWalkSteps u' v' t')
    (hN : refinementKernelCap (4*d) (6*d) rho r < N) :
    ColumnPairRelated X T L (refinementKernelRadius (4*d) (6*d) rho r) (u,u') (v,v') := by
  have he : (u,t.1) ∈ E ∧ (t.1,t.2.1) ∈ E ∧ (t.2.1,t.2.2) ∈ E ∧ (t.2.2,v) ∈ E := by
    simpa only [graphFourWalks, Finset.mem_filter, Finset.mem_univ, true_and] using ht
  have he' : (u',t'.1) ∈ E ∧ (t'.1,t'.2.1) ∈ E ∧ (t'.2.1,t'.2.2) ∈ E ∧ (t'.2.2,v') ∈ E := by
    simpa only [graphFourWalks, Finset.mem_filter, Finset.mem_univ, true_and] using ht'
  have hx0 := Finset.mem_product.mp (hEX he.1)
  have hx1 := Finset.mem_product.mp (hEX he.2.1)
  have hx2 := Finset.mem_product.mp (hEX he.2.2.1)
  have hx3 := Finset.mem_product.mp (hEX he.2.2.2)
  have hx0' := Finset.mem_product.mp (hEX he'.1)
  have hx1' := Finset.mem_product.mp (hEX he'.2.1)
  have hx2' := Finset.mem_product.mp (hEX he'.2.2.1)
  have hx3' := Finset.mem_product.mp (hEX he'.2.2.2)
  refine ⟨⟨hx0.1,hx0'.1⟩, ⟨hx3.2,hx3'.2⟩,
    ((fourWalkSteps_equal_iff u v u' v' t t').mp hd).2.2.2, ?_⟩
  let p : Fin 5 → ZMod N × ZMod N := ![(u,u'),(t.1,t'.1),(t.2.1,t'.2.1),(t.2.2,t'.2.2),(v,v')]
  have hp : ∀ i, (p i).1 ∈ X ∧ (p i).2 ∈ X := by
    intro i; fin_cases i
    · exact ⟨hx0.1,hx0'.1⟩
    · exact ⟨hx0.2,hx0'.2⟩
    · exact ⟨hx1.2,hx1'.2⟩
    · exact ⟨hx2.2,hx2'.2⟩
    · exact ⟨hx3.2,hx3'.2⟩
  exact ColumnPairIdentity.four_step_shrink X T L hrho hr hrle hT hL hzero p hp
    (hcoh _ he.1 _ he'.1 (congrFun hd 0)).cross
    (hcoh _ he.2.1 _ he'.2.1 (congrFun hd 1)).cross
    (hcoh _ he.2.2.1 _ he'.2.2.1 (congrFun hd 2)).cross
    (hcoh _ he.2.2.2 _ he'.2.2.2 (congrFun hd 3)).cross hN

end LeanProofs.GowersSzemeredi
