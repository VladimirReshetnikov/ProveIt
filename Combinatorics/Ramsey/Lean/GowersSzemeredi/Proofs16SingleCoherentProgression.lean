import GowersSzemeredi.Proofs16UnifiedFreimanFamily

/-! One coherent family on a proper progression, with a single bounded
Freiman frequency list and a retained connection to the original anchors. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def freimanFrequencyBohr {N ell : Nat} [NeZero N] (B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (sigma : Real) (u : ZMod N) : Finset (ZMod N) :=
  bohr (B ∪ Finset.univ.image (fun i => theta i u)) sigma

def IsSingleCoherentProgression {N : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (delta kappa : Real) (d : Nat) (r : Real)
    (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N) (B : Finset (ZMod N))
    {ell : Nat} (theta : Fin ell → ZMod N → ZMod N) (x y : ZMod N → ZMod N)
    (t : Fin 4 → ZMod N) (color : ZMod N → Fin 4) (X : Finset (ZMod N))
    (Q : Finset (Fin 4 → ZMod N)) : Prop :=
    P.rank ≤ rowCommonBohrRank delta (uniformAnchorIndexDensity delta kappa d r) d r+1 ∧
    P.Proper ∧
    rowProgressionDensity delta (uniformAnchorIndexDensity delta kappa d r) d r*N ≤ (P.carrier.card : Real) ∧
    B.card ≤ 8*jointSelectionRank d r ∧ ell ≤ 8*jointSelectionRank d r ∧
    (∀ i, FreimanHom 2 P.carrier (theta i) ∧ theta i 0 = 0) ∧
    t 0+t 1 = t 2+t 3 ∧ X ⊆ P.carrier ∧
    singleProgressionDensity delta kappa d r*N ≤ (X.card : Real) ∧
    singleProgressionDensity delta kappa d r*(N : Real)^3 ≤ Q.card ∧
    (∀ u ∈ X,
      IsFreimanLinearOn (freimanFrequencyBohr B theta (jointSelectionRadius d r/2) u)
        (shiftAnchorMap T L r x y (t (color u)+u)) ∧
      shiftAnchorMap T L r x y (t (color u)+u) 0 = 0 ∧
      ∃ a : Fin 4 → ZMod N, a 0+a 1 = a 2+a 3 ∧ shiftAnchorArrangement x y a ∈ H ∧
        a (color u) = t (color u)+u) ∧
    ∀ b ∈ Q, b 0+b 1 = b 2+b 3 ∧ Function.Injective b ∧
      (∀ j, b j ∈ X ∧ color (b j) = j) ∧
      shiftAnchorArrangement x y (fun j => t j+b j) ∈ H ∧
      ∀ z, (∀ j, z ∈ freimanFrequencyBohr B theta (jointSelectionRadius d r/2) (b j)) →
        shiftAnchorMap T L r x y (t (color (b 0))+b 0) z+
          shiftAnchorMap T L r x y (t (color (b 1))+b 1) z =
        shiftAnchorMap T L r x y (t (color (b 2))+b 2) z+
          shiftAnchorMap T L r x y (t (color (b 3))+b 3) z

def HasSingleCoherentProgression {N : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (delta kappa : Real) (d : Nat) (r : Real) : Prop :=
  ∃ (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N) (B : Finset (ZMod N))
    (ell : Nat) (theta : Fin ell → ZMod N → ZMod N) (x y : ZMod N → ZMod N)
    (t : Fin 4 → ZMod N) (color : ZMod N → Fin 4) (X : Finset (ZMod N))
    (Q : Finset (Fin 4 → ZMod N)),
    IsSingleCoherentProgression H T L delta kappa d r P B theta x y t color X Q

theorem HasCoherentProgressionRows.single_system {N d : Nat} [NeZero N]
    {H : Finset (HigherArrangementParameter N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {delta kappa r : Real}
    (h : HasCoherentProgressionRows H T L delta kappa d r)
    (hN : 8 ≤ coherentProgressionDensity delta kappa d r*(N : Real)) :
    HasSingleCoherentProgression H T L delta kappa d r := by
  obtain ⟨s,J,x,y,P,t,S,psi,c,hs,hbudget,hJ,hPrank,hPproper,hPmass,ht,hSne,hS,hconst,hpsi,hprops⟩ := h
  obtain ⟨ell,theta,hell,htheta,heq⟩ := exists_unified_freiman_family P.carrier J psi hJ hpsi
  obtain ⟨color,R,hRS,hR,hXP,hX,hlocal,hcoherent⟩ := coherent_four_rows_to_single
    S P.carrier J c psi (fun j u => shiftAnchorMap T L r x y (t j+u)) (jointSelectionRadius d r)
    (fun b hb => (hprops b hb).1) (fun b hb => (hprops b hb).2.1) hS hN
    (fun b hb => (hprops b hb).2.2.2.2.1) (fun b hb => (hprops b hb).2.2.2.2.2.1)
  have hdomain (u : ZMod N) : freimanFrequencyBohr (affineRowConstants J c) theta
      (jointSelectionRadius d r/2) u = unifiedRowBohrDomain J c psi (jointSelectionRadius d r) u := by
    unfold freimanFrequencyBohr unifiedRowBohrDomain
    rw [heq u]
  refine ⟨P,affineRowConstants J c,ell,theta,x,y,t,color,labeledRowSupport S color,R,
    hPrank,hPproper,hPmass,hconst,by omega,htheta,ht,hXP,hX,hR,?_,?_⟩
  · intro u hu
    refine ⟨?_,(hlocal u hu).2,?_⟩
    · rw [hdomain]
      exact (hlocal u hu).1
    · obtain ⟨b,hb,he⟩ := labeledRowSupport_witness S color hu
      refine ⟨fun j => t j+b j,?_,(hprops b hb).2.2.2.1,?_⟩
      · have hba := (hprops b hb).1
        dsimp
        linear_combination ht+hba
      · dsimp
        rw [he]
  · intro b hb
    obtain ⟨hba,hbinj,hbX,hbc⟩ := hcoherent b hb
    refine ⟨hba,hbinj,hbX,(hprops b (hRS hb)).2.2.2.1,?_⟩
    intro z hz
    exact hbc z (fun j => (hdomain (b j)) ▸ hz j)

end LeanProofs.GowersSzemeredi
