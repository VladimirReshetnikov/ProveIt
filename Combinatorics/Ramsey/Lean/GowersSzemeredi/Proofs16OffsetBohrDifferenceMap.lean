import GowersSzemeredi.Proofs16OffsetGraphOverlap
import GowersSzemeredi.Proofs16IndexedGraphCoverRetention
import GowersSzemeredi.Proofs16DenseFourfoldBohrCluster

/-! A dense indexed offset equation between Freiman maps is represented
on a retained original subfamily by one normalized map on a Bohr set. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def offsetDifferenceBohrDensity (delta : Real) : Real :=
  (commonDifferenceClusterDensity (delta^2))^2*delta

theorem offsetDifferenceBohrDensity_pos {delta : Real} (hd : 0 < delta) :
    0 < offsetDifferenceBohrDensity delta :=
  mul_pos (pow_pos (commonDifferenceClusterDensity_pos (pow_pos hd 2)) 2) hd

theorem offset_equation_common_bohr_map {N : Nat} [NeZero N] {I : Type*}
    [Fintype I] [DecidableEq I] (Q : Finset (I × ZMod N)) (a v : I → ZMod N)
    (A B : Finset (ZMod N)) (f g : ZMod N → ZMod N) (M : Nat)
    (hM : 0 < M) (ha : ∀ z, (Finset.univ.filter fun i => a i = z).card ≤ M)
    (hA : ∀ p ∈ Q, p.2+a p.1 ∈ A) (hB : ∀ p ∈ Q, p.2 ∈ B)
    (hval : ∀ p ∈ Q, f (p.2+a p.1)-g p.2 = v p.1)
    (hf : IsFreimanLinearOn A f) (hg : FreimanHom 8 B g)
    {delta : Real} (hd : 0 < delta) (hQ : delta*M*(N : Real)^2 ≤ Q.card) :
    ∃ (Gamma : Finset (ZMod N)) (psi : ZMod N → ZMod N)
      (b c : ZMod N) (R : Finset (I × ZMod N)),
      (Gamma.card : Real) ≤ 16*(delta^2)^(-(2 : Real)) ∧
      FreimanHom 2 (bohr Gamma (commonDifferenceRadius (delta^2))) psi ∧ psi 0 = 0 ∧
      R ⊆ Q ∧ offsetDifferenceBohrDensity delta*M*(N : Real)^2 ≤ R.card ∧
      ∀ p ∈ R, a p.1-b ∈ bohr Gamma (commonDifferenceRadius (delta^2)/2) ∧
        f (p.2+a p.1)-g p.2 = c+psi (a p.1-b) := by
  obtain ⟨b,c,S,hSB,hS,hagree⟩ := offset_equation_dense_overlap Q a v A B f g M hM ha hA hB hval hd.le hQ
  have hgS : FreimanHom 8 S g := IsAddFreimanHom.subset hSB hg (Set.mapsTo_univ _ _)
  obtain ⟨Gamma,C,psi,hGamma,hCS,hC,hpsi,hzero,hrepr⟩ :=
    dense_freiman_fourfold_bohr_cluster S g (pow_pos hd 2) hS hgS
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hm : (0 : Real) < M := by exact_mod_cast hM
  obtain ⟨b',c',R,hRQ,hR,hvalue⟩ := indexed_common_graph_cover_retained_fibre A B C f g Q
    (fun p => p.2+a p.1) Prod.snd b c (hCS.trans hSB)
    (fun s hs => hagree s (hCS hs)) hA hB hf (hg.isFreimanLinearOn (by decide))
    (commonDifferenceClusterDensity_pos (pow_pos hd 2)) hC (by positivity) hQ psi
    (fun p hp => (hrepr p hp).2)
  refine ⟨Gamma,psi,b',c',R,hGamma,hpsi,hzero,hRQ,?_,?_⟩
  · simpa only [offsetDifferenceBohrDensity,mul_assoc] using hR
  · intro p hp
    obtain ⟨hindex,hval⟩ := hvalue p hp
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp hindex
    have hq' : ∀ j, q j ∈ C := by simpa only [Fintype.mem_piFinset] using hq
    have h := And.intro (he ▸ (hrepr q hq').1) hval
    simpa only [add_sub_cancel_left] using h

end LeanProofs.GowersSzemeredi
