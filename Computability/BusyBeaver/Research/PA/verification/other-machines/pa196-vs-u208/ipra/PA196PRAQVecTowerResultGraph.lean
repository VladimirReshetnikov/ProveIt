import PA196PRAQVecTowerCSeqInduction

/-! Candidate-PRA semantics of the full arithmetic tower result graph. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA196PRAQVecTowerResultGraph
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
  PRAHistoryTruncation PA196PAQVecSeqTrace PA196PRAQVecTower
  PA196PRAQVecTowerCSeq PA196PRAQVecTowerCSeqInduction

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero

theorem resultGraph_eq (t n seed : M)
    (h : boundBlueprint.resultDef.val.Evalb ![t,n,seed]) : t = tower n seed := by
  simp only [PR.Blueprint.resultDef, HierarchySymbol.Semiformula.val_mkSigma,
    Semiformula.eval_ex, LogicalConnective.HomClass.map_and, Semiformula.eval_rew] at h
  obtain ⟨s,hs,hm⟩ := h
  have hv : (Semiterm.val (L := ℒₒᵣ) ![s,t,n,seed] Empty.elim ∘
      (Rew.subst (#0 :> fun x => #(BinderNotation.finSuccItr x 3))) ∘ Semiterm.bvar) = ![s,seed] := by
    funext j
    exact Fin.cases rfl (fun k => Fin.cases rfl (fun a => Fin.elim0 a) k) j
  have hf : (Semiterm.val (L := ℒₒᵣ) ![s,t,n,seed] Empty.elim ∘
      (Rew.subst (#0 :> fun x => #(BinderNotation.finSuccItr x 3))) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,hf] at hs
  have hm' : memRel.val.Evalb ![s,n,t] := by
    simpa [memRelOpr, Semiformula.Operator.val, Matrix.comp_vecCons'',
      PRAHistoryTruncation.val_comp_bvar] using hm
  clear hm
  have hm := hm'
  clear hm'
  have hseq := ((cseq_spec s seed).mp hs).1
  obtain ⟨hmap,l,hl,d,hd,hdom,hund⟩ := (seq_iff s).mp hseq
  have hlh : lhDef.val.Evalb ![l,s] :=
    (lh_iff l s).mpr ⟨fun _ => ⟨d,hd,hdom,hund⟩, fun hn => absurd hseq hn⟩
  have hexp (x : M) : ∃ y, Exponential x y := ⟨_,exponential_expF x⟩
  have hdomi := (PRAHistoryDomainExtension.domain_iff hexp d s).mp hdom
  have hlt : n < l := (PRAHistoryUnderCanonical.modelUnderBits d l n hund).mp
    ((hdomi n).mpr ⟨t, PRAHistoryDomainExtension.memRel_value_lt hexp hm, hm⟩)
  have he := cseq_entries s seed l hs hl hlh n hlt
  obtain ⟨d₀,_,hdom₀,huniq₀⟩ := (PRAHistorySequenceExtension.mapping_iff hexp s).mp hmap
  have hdomi₀ := (PRAHistoryDomainExtension.domain_iff hexp d₀ s).mp hdom₀
  obtain ⟨y,_,_,hu⟩ := huniq₀ n ((hdomi₀ n).mpr
    ⟨t,PRAHistoryDomainExtension.memRel_value_lt hexp hm,hm⟩)
  rw [hu t (PRAHistoryDomainExtension.memRel_value_lt hexp hm) hm,
      hu (tower n seed) (PRAHistoryDomainExtension.memRel_value_lt hexp he) he]

#print axioms resultGraph_eq
end PA196PRAQVecTowerResultGraph
