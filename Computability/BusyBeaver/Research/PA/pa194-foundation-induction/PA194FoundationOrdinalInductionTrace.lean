import PA194FoundationOrdinalInductionContradiction

/-! Existential witness elimination for the minimum-bad trace argument. -/
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND

def leastBadExistsContradiction {Γ : List Form} (e : EqualityProofs Γ)
    (p : Formula 1) (s c : Nat)
    (hs : ND.Proof Γ (domain (.fvar s)))
    (hc : ND.Proof Γ (predicateTrace (∼p) (.fvar s) (.fvar c)))
    (hl : ND.Proof Γ (leastExists (.fvar c)))
    (hbase : ND.Proof Γ (inductionBase p))
    (hstep : ND.Proof Γ (inductionStep p)) : ND.Proof Γ ⊥ := by
  apply exsElim hl
  let σ : Formula 1 := least (Rew.bShift (.fvar c)) (.bvar 0)
  let C := σ.free :: shifted Γ
  have dl : ND.Proof C (least (.fvar (c+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; ordinalSyntax
  have dc : ND.Proof C (predicateTrace (∼p.shift) (.fvar (s+1)) (.fvar (c+1))) := by
    simpa [C] using up (predicateTraceShift (∼p) s c hc) σ.free
  exact leastBadContradiction (e.shift.up σ.free) p.shift (s+1) (c+1) 0
    (up (domainShift s hs) σ.free) dc dl
    (up (inductionBaseShift p hbase) σ.free) (up (inductionStepShift p hstep) σ.free)

def badInsideOrdinalContradiction {Γ : List Form} (e : EqualityProofs Γ)
    (p : Formula 1) (s a : Nat)
    (hs : ND.Proof Γ (domain (.fvar s)))
    (ha : ND.Proof Γ (mem (.fvar s) (.fvar a)))
    (hn : ND.Proof Γ (∼(p/[.fvar a])))
    (hsep : ND.Proof Γ (separationFormula (∼p)))
    (hbase : ND.Proof Γ (inductionBase p))
    (hstep : ND.Proof Γ (inductionStep p)) : ND.Proof Γ ⊥ := by
  apply exsElim (predicateTraceFromSeparation (∼p) s hsep)
  let σ : Formula 1 := predicateTrace (∼p) (Rew.bShift (.fvar s)) (.bvar 0)
  let C := σ.free :: shifted Γ
  have dc : ND.Proof C (predicateTrace (∼p.shift) (.fvar (s+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    change ND.Proof C ((predicateTrace (∼p) (Rew.bShift (.fvar s : Term 0)) (.bvar 0)).free) at h
    rw [predicateTraceFree] at h
    simpa [C] using h
  have ds := up (domainShift s hs) σ.free
  have da := up (memberShift s a ha) σ.free
  have dn : ND.Proof C ((∼p.shift)/[.fvar (a+1)]) := by
    have h := up (shiftProof hn) σ.free
    have he : (∼(p/[(.fvar a : Term 0)])).shift = ∼(p/[.fvar a]).shift := by simp
    rw [he,predicateInstanceShift] at h
    simpa [C] using h
  exact leastBadExistsContradiction (e.shift.up σ.free) p.shift (s+1) 0 ds dc
    (predicateTraceMinimum (∼p.shift) (s+1) 0 (a+1) ds dc da dn)
    (up (inductionBaseShift p hbase) σ.free) (up (inductionStepShift p hstep) σ.free)

#print axioms leastBadExistsContradiction
#print axioms badInsideOrdinalContradiction
end M6.PA.RelationalSource.Ordinal
