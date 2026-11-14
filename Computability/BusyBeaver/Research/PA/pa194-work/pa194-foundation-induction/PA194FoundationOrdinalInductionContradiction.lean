import PA194FoundationOrdinalInductionSchema
import PA194FoundationOrdinalTraceMinimum

/-! The finite minimum-counterexample contradiction. -/
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND

def leastBadContradiction {Γ : List Form} (e : EqualityProofs Γ)
    (p : Formula 1) (s c b : Nat)
    (hs : ND.Proof Γ (domain (.fvar s)))
    (hc : ND.Proof Γ (predicateTrace (∼p) (.fvar s) (.fvar c)))
    (hl : ND.Proof Γ (least (.fvar c) (.fvar b)))
    (hbase : ND.Proof Γ (inductionBase p))
    (hstep : ND.Proof Γ (inductionStep p)) : ND.Proof Γ ⊥ := by
  have hbad := mp (andLeft hl) (andLeft (predicateTraceAt (∼p) s c b hc))
  have hb := memberDomain s b hs (andLeft hbad)
  have hnb : ND.Proof Γ (∼(p/[.fvar b])) := by simpa using andRight hbad
  have hnz : ND.Proof Γ (∼zero (.fvar b)) := by
    apply byContradiction
    have hz : ND.Proof (∼∼zero (.fvar b) :: Γ) (zero (.fvar b)) := by
      simpa using (assumption (p := ∼∼zero (.fvar b)) (by simp))
    exact contradiction (inductionBaseAt p b (up hbase _) (up hb _) hz) (up hnb _)
  apply exsElim (domainGreatest b hb (notZeroNonempty b hnz))
  let σ : Formula 1 := greatest (Rew.bShift (.fvar b)) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hg : ND.Proof C (greatest (.fvar (b+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; ordinalSyntax
  have db := up (domainShift b hb) σ.free
  have ds := up (domainShift s hs) σ.free
  have dc : ND.Proof C (predicateTrace (∼p.shift) (.fvar (s+1)) (.fvar (c+1))) := by
    simpa [C] using up (predicateTraceShift (∼p) s c hc) σ.free
  have dl := up (leastShift c b hl) σ.free
  have dm := memberDomain (b+1) 0 db (andLeft hg)
  have hp := badTraceMemberGood (e.shift.up σ.free) p.shift (s+1) (c+1) (b+1) 0
    ds dc dl (andLeft hg)
  have hpnext := inductionStepAt p.shift 0 (b+1) (up (inductionStepShift p hstep) σ.free)
    dm db (greatestSuccessor (e.shift.up σ.free) (b+1) 0 (andLeft (andLeft db)) hg) hp
  have hn : ND.Proof C (∼(p.shift/[.fvar (b+1)])) := by
    have h := up (shiftProof hnb) σ.free
    have he : (∼(p/[((.fvar b) : Term 0)])).shift = ∼(p/[.fvar b]).shift := by simp
    rw [he, predicateInstanceShift] at h
    exact h
  exact contradiction hpnext hn

#print axioms leastBadContradiction
end M6.PA.RelationalSource.Ordinal
