import GowersSzemeredi.Proofs16FourWalkCollisionFibres
import GowersSzemeredi.Proofs16CoherentFourWalkCompression

/-! Matched edge differences turn two walks into a single walk in a
coherent difference relation. Popular endpoint fibres can then be compressed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem matched_coherent_four_walk {N ell j : Nat} [NeZero N]
    (X B : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (F : ZMod N → ZMod N → ZMod N) (sigma : Real)
    (E : Finset (ZMod N × ZMod N))
    (hcoh : ∀ p ∈ E, ∀ q ∈ E, p.1-p.2 = q.1-q.2 →
      CoherentRelationLevel X B theta F sigma j p q)
    {u v u' v' : ZMod N} {t t' : ZMod N × ZMod N × ZMod N}
    (ht : t ∈ graphFourWalks (fun a b => (a,b) ∈ E) u v)
    (ht' : t' ∈ graphFourWalks (fun a b => (a,b) ∈ E) u' v')
    (hd : fourWalkSteps u v t = fourWalkSteps u' v' t') :
    t' ∈ graphFourWalks (fun x y =>
      CoherentRelationLevel X B theta F sigma j (x+(u-u'),x) (y+(u-u'),y)) u' v' := by
  have he : (u,t.1) ∈ E ∧ (t.1,t.2.1) ∈ E ∧ (t.2.1,t.2.2) ∈ E ∧ (t.2.2,v) ∈ E := by
    simpa only [graphFourWalks,Finset.mem_filter,Finset.mem_univ,true_and] using ht
  have he' : (u',t'.1) ∈ E ∧ (t'.1,t'.2.1) ∈ E ∧ (t'.2.1,t'.2.2) ∈ E ∧ (t'.2.2,v') ∈ E := by
    simpa only [graphFourWalks,Finset.mem_filter,Finset.mem_univ,true_and] using ht'
  obtain ⟨h₀,h₁,h₂,h₃⟩ := (fourWalkSteps_equal_iff u v u' v' t t').mp hd
  have hu : u = u'+(u-u') := by ring
  have ha : t.1 = t'.1+(u-u') := by linear_combination -h₀
  have hb : t.2.1 = t'.2.1+(u-u') := by linear_combination -h₁
  have hc : t.2.2 = t'.2.2+(u-u') := by linear_combination -h₂
  have hv : v = v'+(u-u') := by linear_combination -h₃
  have h0 := (hcoh _ he.1 _ he'.1 (congrFun hd 0)).cross
  have h1 := (hcoh _ he.2.1 _ he'.2.1 (congrFun hd 1)).cross
  have h2 := (hcoh _ he.2.2.1 _ he'.2.2.1 (congrFun hd 2)).cross
  have h3 := (hcoh _ he.2.2.2 _ he'.2.2.2 (congrFun hd 3)).cross
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    by simpa only [←hu,←ha] using h0,
    by simpa only [←ha,←hb] using h1,
    by simpa only [←hb,←hc] using h2,
    by simpa only [←hc,←hv] using h3⟩

theorem coherent_collision_fibre_le_walks {N ell j : Nat} [NeZero N]
    (X B : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (F : ZMod N → ZMod N → ZMod N) (sigma : Real)
    (E : Finset (ZMod N × ZMod N)) (U V : Finset (ZMod N))
    (hcoh : ∀ p ∈ E, ∀ q ∈ E, p.1-p.2 = q.1-q.2 →
      CoherentRelationLevel X B theta F sigma j p q)
    (k : ZMod N × ZMod N × ZMod N) :
    (fourWalkCollisionFibre (fourWalkFamily E U V) k).card ≤
      (graphFourWalks (fun x y => CoherentRelationLevel X B theta F sigma j
        (x+(k.1-k.2.1),x) (y+(k.1-k.2.1),y)) k.2.1 k.2.2).card := by
  apply Finset.card_le_card_of_injOn (fun p => p.2.2) ?_
    (fourWalkCollisionFibre_second_injOn _ k)
  intro p hp
  obtain ⟨hp,hkey⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpW,hsteps⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hpW
  have h1 := (Finset.mem_filter.mp hp1).2
  have h2 := (Finset.mem_filter.mp hp2).2
  have hw := matched_coherent_four_walk X B theta F sigma E hcoh h1 h2 hsteps
  dsimp only [fourWalkCollisionKey] at hkey
  have hu : p.1.1.1 = k.1 := congrArg (fun k : ZMod N × ZMod N × ZMod N => k.1) hkey
  have hu' : p.2.1.1 = k.2.1 := congrArg (fun k => k.2.1) hkey
  have hv' : p.2.1.2 = k.2.2 := congrArg (fun k => k.2.2) hkey
  simpa only [hu,hu',hv',Finset.mem_coe] using hw

end LeanProofs.GowersSzemeredi
