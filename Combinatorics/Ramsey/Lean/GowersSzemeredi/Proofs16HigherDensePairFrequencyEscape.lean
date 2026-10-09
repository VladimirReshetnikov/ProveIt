import GowersSzemeredi.Proofs16HigherPairEscapeComponent

/-! Dense failed higher containments yield one controlled progression
map escaping on a dense set of endpoint pairs. The four-way choice and
nine-dimensional projection multiplicity are both explicit. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem higher_failed_containments_dense_pair_escape {N d : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (HigherArrangementParameter N)) (T : ZMod N → Finset (ZMod N))
    (D : HigherArrangementParameter N → Finset (ZMod N))
    (F : (ZMod N × ZMod N) → Finset (ZMod N)) {r sigma delta : Real}
    (hr : 0 < r) (hr4 : r < 4) (hd : 0 < delta) (hB : delta*(N : Real)^11 ≤ B.card)
    (hT : ∀ x, (T x).card ≤ d)
    (hs : ∀ p ∈ B, ((D p).card : Real)*4*sigma ≤ 1/(4*Real.pi))
    (hFD : ∀ p ∈ B, ∀ j : Fin 4, F (higherArrangementEndpointPair p (Fin.castAdd 4 j)) ⊆ D p)
    (hfail : ∀ p ∈ B, ¬ bohr (D p) sigma ⊆
      bohrQuarterSum (higherLeftFrequencies T (higherArrangementEndpoints p))
        (higherRightFrequencies T (higherArrangementEndpoints p)) r) :
    ∃ (j : Fin 4) (theta : PairFrequencyMap N) (E : Finset (ZMod N × ZMod N)),
      (∃ n < 8, theta.Controlled ((higherArrangementPairDensity (higherEscapeCoordinateDensity delta d r) n)^2)) ∧
      E ⊆ B.image (fun p => higherArrangementEndpointPair p (Fin.castAdd 4 j)) ∧
      (higherEscapeDensity delta d r/4)*(N : Real)^2 ≤ E.card ∧
      ∀ e ∈ E, e.1-e.2 ∈ theta.domain ∧
        theta.toFun (e.1-e.2) ∈ boundedFrequencySpan (fun a : ↥(T e.1 ∪ T e.2) => (a : ZMod N))
          (2*bohrExtensionCutoff (8*d) r) ∧
        theta.toFun (e.1-e.2) ∉ boundedFrequencySpan (fun a : F e => (a : ZMod N)) 1 := by
  obtain ⟨f,theta,Q,hf,hQB,hcontrol,hvalue,_,hescape,hQ⟩ :=
    higher_failed_containments_pair_maps B T D hr hr4 hd hB hT hs hfail
  let good (p : HigherArrangementParameter N) (j : Fin 4) : Prop :=
    let i := Fin.castAdd 4 j
    let e := higherArrangementEndpointPair p i
    higherArrangementPairDifference p i ∈ (theta i).domain ∧
    (theta i).toFun (higherArrangementPairDifference p i) ∈
      boundedFrequencySpan (fun a : ↥(T e.1 ∪ T e.2) => (a : ZMod N)) (2*bohrExtensionCutoff (8*d) r) ∧
    (theta i).toFun (higherArrangementPairDifference p i) ∉
      boundedFrequencySpan (fun a : F e => (a : ZMod N)) 1
  have hex : ∀ p ∈ Q, ∃ j, good p j := by
    intro p hp
    exact higher_left_pair_escape f theta T F (D p) p _ hf (hFD p (hQB hp)) (hvalue p hp) (hescape p hp)
  let label (p : HigherArrangementParameter N) : Fin 4 := if hp : p ∈ Q then (hex p hp).choose else 0
  have hlabel (p : HigherArrangementParameter N) (hp : p ∈ Q) : good p (label p) := by
    simpa only [label,dif_pos hp] using (hex p hp).choose_spec
  obtain ⟨j,_,hj⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := Q) (t := (Finset.univ : Finset (Fin 4))) (f := label)
    (b := (higherEscapeDensity delta d r/4)*(N : Real)^11)
    (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty (by
      simpa only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,
        show 4*(higherEscapeDensity delta d r/4*(N : Real)^11) =
          higherEscapeDensity delta d r*(N : Real)^11 by ring] using hQ)
  let R := Q.filter fun p => label p = j
  let E := R.image fun p => higherArrangementEndpointPair p (Fin.castAdd 4 j)
  have hRsub : R ⊆ B := (Finset.filter_subset _ _).trans hQB
  refine ⟨j,theta (Fin.castAdd 4 j),E,hcontrol _,Finset.image_subset_image hRsub,?_,?_⟩
  · exact higher_arrangements_pair_density R E (Fin.castAdd 4 j)
      (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩) hj
  · intro e he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hpQ,hpj⟩ := Finset.mem_filter.mp hp
    have hg := hlabel p hpQ
    rw [hpj] at hg
    exact hg

end LeanProofs.GowersSzemeredi
