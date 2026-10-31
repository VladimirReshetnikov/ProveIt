import DiophantineConsistency.PRAHistorySequenceExtension
import DiophantineConsistency.PRAWitnessArithmetic
import DiophantineConsistency.PRAHistoryUnderCanonical
import DiophantineConsistency.PRAHistoryExpCode
import DiophantineConsistency.PRAHistoryUnderExtension
import Foundation.FirstOrder.Arithmetic.HFS.Fixpoint
/-! # Truncating fixpoint computation histories

Foundation's fixpoint stages are values of a primitive recursion whose
computation history is an unbounded witness: `limSeqDef L k` is
`∃ s, cseqDef s ∧ ⟨k, L⟩ ∈ s`, and a given history `s` may be arbitrarily
longer than `k`. A witness bound needs a history bounded by a function of `k`.

The restriction `s'` of `s` to the indices `≤ k` is one (`truncate_spec`). It
is again a history (zero and successor clauses are inherited, and its domain is
`under (k+1)`), it still ends in `⟨k, L⟩`, and every entry at index `i+1`
satisfies `succDef`, whose members are syntactically `≤ i`; so every entry is
below `2^(k+1)` and every member of `s'` is at most `⟪k, 2^(k+1)⟫`.

No property of the blueprint's core is used: the argument is uniform in the
blueprint. Everything is proved in `𝗜𝚺₀` with a total exponential, the
arithmetic of every candidate-PRA model; the only further input is the
characterization of the bits of `under`, which `PRAHistoryUnderCanonical`
supplies in candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryTruncation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

section sigma0
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]

/-- **A set whose members are all below `m` is below `2^m`.** -/
theorem lt_exp_of_bits {a m p : V} (hp : Exponential m p)
    (h : ∀ j, bitDef.val.Evalb ![j,a] → j < m) : a < p := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  by_contra hge
  have hge : p ≤ a := not_lt.mp hge
  have ha : 0 < a := lt_of_lt_of_le hp.range_pos hge
  obtain ⟨y, hya, hL, hay⟩ := log_pos ha
  have hdiv : a / y = 1 := div_eq_of (by simpa using hya) (by rw [one_add_one_eq_two, mul_comm]; exact hay)
  have hbit : bitDef.val.Evalb ![log a, a] :=
    (PRAHistoryInsertMembership.bit_iff_lenbit (log a) a y hL).mpr
      (LenBit.iff_rem.mpr (by rw [hdiv]; simp))
  have hlt : log a + 1 ≤ m := lt_iff_succ_le.mp (h _ hbit)
  have h2 : Exponential (log a + 1) (2 * y) := Exponential.exponential_succ_mul_two.mpr hL
  exact absurd (lt_of_lt_of_le hay (Exponential.monotone_le h2 hp hlt)) (not_lt.mpr hge)

theorem cseq_iff (φ : Fixpoint.Blueprint 0) (s : V) :
    φ.prBlueprint.cseqDef.val.Evalb ![s] ↔
      seqDef.val.Evalb ![s] ∧ (0 < s ∧ memRel.val.Evalb ![s,0,0]) ∧
        ∀ x < 2 * s, ∀ l ≤ 2 * s, lhDef.val.Evalb ![l,s] → x + 1 < l →
          ∀ z < s, memRel.val.Evalb ![s,x,z] →
            ∃ y < s, φ.succDef.val.Evalb ![y,z,x] ∧ memRel.val.Evalb ![s,x+1,y] := by
  simp [PR.Blueprint.cseqDef, Fixpoint.Blueprint.prBlueprint, Semiformula.ballLT,
    Semiformula.bexsLT, Semiformula.bexsLTSucc, FirstOrder.ball, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq,
    Semiformula.Operator.Eq.sentence_eq, lt_succ_iff_le, memRelOpr]

theorem seq_iff (s : V) :
    seqDef.val.Evalb ![s] ↔ isMappingDef.val.Evalb ![s] ∧
      ∃ l ≤ 2 * s, ∃ d ≤ 2 * s, domainDef.val.Evalb ![d,s] ∧ underDef.val.Evalb ![d,l] := by
  simp [seqDef, Semiformula.bexsLT, Semiformula.bexsLTSucc, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le]

theorem lh_iff (l s : V) :
    lhDef.val.Evalb ![l,s] ↔
      (seqDef.val.Evalb ![s] →
        ∃ d ≤ 2 * s, domainDef.val.Evalb ![d,s] ∧ underDef.val.Evalb ![d,l]) ∧
      (¬seqDef.val.Evalb ![s] → l = 0) := by
  simp [lhDef, Semiformula.bexsLT, Semiformula.bexsLTSucc, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq,
    Semiformula.Operator.Eq.sentence_eq, lt_succ_iff_le]

/-- Members of a stage are below its index. -/
theorem succ_lt_exp (φ : Fixpoint.Blueprint 0) (hexp : ∀ i : V, ∃ p, Exponential i p)
    {u z i p : V} (hp : Exponential (i + 1) p) (hs : φ.succDef.val.Evalb ![u,z,i]) : u < p := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  refine lt_exp_of_bits hp (fun j hj => ?_)
  have hs' : ∀ x < u + (i + 1),
      (bitDef.val.Evalb ![x,u] → (x = i ∨ x < i) ∧ (φ.core.sigma).val.Evalb ![x,z]) ∧
        ((x = i ∨ x < i) → (φ.core.pi).val.Evalb ![x,z] → bitDef.val.Evalb ![x,u]) := by
    simpa [Fixpoint.Blueprint.succDef, Semiformula.ballLT, FirstOrder.ball,
      Semiformula.Operator.val, operator_mem_def, Semiformula.Operator.LT.sentence_eq,
      Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.Eq.sentence_eq] using hs
  have hju : j < u + (i + 1) := lt_of_lt_of_le (PRAHistoryDomainExtension.bit_lt hexp hj) le_self_add
  rcases ((hs' j hju).1 hj).1 with h | h
  · exact h ▸ lt_add_one i
  · exact lt_trans h (lt_add_one i)

/-- **The restriction of a fixpoint history to the indices `≤ k` is a history
ending in the same `⟨k, L⟩`, all of whose members are at most `⟪k, 2^(k+1)⟫`.** -/
theorem truncate_spec (φ : Fixpoint.Blueprint 0) (hexp : ∀ i : V, ∃ p, Exponential i p)
    (hunder : ∀ d l i : V, underDef.val.Evalb ![d,l] → (bitDef.val.Evalb ![i,d] ↔ i < l))
    {s s' k L E : V} (hE : Exponential (k + 1) E)
    (hs : φ.prBlueprint.cseqDef.val.Evalb ![s])
    (hkL : memRel.val.Evalb ![s,k,L])
    (hs' : ∀ y, bitDef.val.Evalb ![y,s'] ↔ bitDef.val.Evalb ![y,s] ∧ π₁ y ≤ k) :
    φ.prBlueprint.cseqDef.val.Evalb ![s'] ∧ memRel.val.Evalb ![s',k,L] ∧
      ∀ y, bitDef.val.Evalb ![y,s'] → y ≤ ⟪k, E⟫ := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have vlt {t i y : V} (h : memRel.val.Evalb ![t,i,y]) : y < t :=
    PRAHistoryDomainExtension.memRel_value_lt hexp h
  have rel' (i z : V) : memRel.val.Evalb ![s',i,z] ↔ memRel.val.Evalb ![s,i,z] ∧ i ≤ k := by
    rw [PRAHistorySeqConsMembership.memRel_iff, PRAHistorySeqConsMembership.memRel_iff, hs',
      pi₁_pair]
  obtain ⟨hseq, ⟨-, h00⟩, hsucc⟩ := (cseq_iff φ s).mp hs
  obtain ⟨hmap, l, hl, d, hd, hdom, hund⟩ := (seq_iff s).mp hseq
  have hdomi := (PRAHistoryDomainExtension.domain_iff hexp d s).mp hdom
  have entry (i : V) (hi : i < l) : ∃ y < s, memRel.val.Evalb ![s,i,y] :=
    (hdomi i).mp ((hunder d l i hund).mpr hi)
  have hkl : k < l := (hunder d l k hund).mp ((hdomi k).mpr ⟨L, vlt hkL, hkL⟩)
  obtain ⟨d₀, -, hdom₀, huniq₀⟩ := (PRAHistorySequenceExtension.mapping_iff hexp s).mp hmap
  have hdomi₀ := (PRAHistoryDomainExtension.domain_iff hexp d₀ s).mp hdom₀
  have uniq {i y y' : V} (hy : memRel.val.Evalb ![s,i,y]) (hy' : memRel.val.Evalb ![s,i,y']) :
      y' = y := by
    obtain ⟨y₀, -, -, hu⟩ := huniq₀ i ((hdomi₀ i).mpr ⟨y, vlt hy, hy⟩)
    rw [hu y (vlt hy) hy, hu y' (vlt hy') hy']
  have hlh : lhDef.val.Evalb ![l,s] :=
    (lh_iff l s).mpr ⟨fun _ => ⟨d, hd, hdom, hund⟩, fun h => absurd hseq h⟩
  have hpair : bitDef.val.Evalb ![⟪k,L⟫,s] := (PRAHistorySeqConsMembership.memRel_iff s k L).mp hkL
  have hks : k < s := lt_of_le_of_lt (le_pair_left k L) (PRAHistoryDomainExtension.bit_lt hexp hpair)
  have hs2 : s ≤ 2 * s := by rw [two_mul]; exact le_self_add
  -- every entry at an index `≤ k` is below `2^(k+1)`
  have hent {i z : V} (hik : i ≤ k) (hz : memRel.val.Evalb ![s,i,z]) : z < E := by
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · rw [uniq h00 hz]; exact hE.range_pos
    · have hjk : j < k := lt_iff_succ_le.mpr hik
      obtain ⟨zj, -, hzj⟩ := entry j (lt_trans hjk hkl)
      obtain ⟨y, -, hsy, hy⟩ := hsucc j (lt_of_lt_of_le (lt_trans hjk hks) hs2) l hl hlh
        (lt_of_le_of_lt hik hkl) zj (vlt hzj) hzj
      obtain ⟨pj, hpj⟩ := hexp (j + 1)
      rw [uniq hy hz]
      exact lt_of_lt_of_le (succ_lt_exp φ hexp hpj hsy)
        (Exponential.monotone_le hpj hE (le_trans hik (le_of_lt (lt_add_one k))))
  have hkL' : memRel.val.Evalb ![s',k,L] := (rel' k L).mpr ⟨hkL, le_rfl⟩
  have hpair' : bitDef.val.Evalb ![⟪k,L⟫,s'] := (PRAHistorySeqConsMembership.memRel_iff s' k L).mp hkL'
  -- sizes: `2^k ≤ 2^⟪k,L⟫ ≤ s'`
  obtain ⟨P, hP⟩ := hexp ⟪k,L⟫
  obtain ⟨Ek, hEk⟩ := hexp k
  have hPs' : P ≤ s' := ((PRAHistoryInsertMembership.bit_iff_lenbit _ _ P hP).mp hpair').le
  have hEks' : Ek ≤ s' := le_trans (Exponential.monotone_le hEk hP (le_pair_left k L)) hPs'
  have hEE : E = 2 * Ek := hE.uniq (Exponential.exponential_succ_mul_two.mpr hEk)
  -- the domain of `s'` is `under (k+1)`
  have hE1 : (E - 1) + 1 = E := tsub_add_cancel_of_le (pos_iff_one_le.mp hE.range_pos)
  have hund' : underDef.val.Evalb ![E - 1, k + 1] :=
    (PRAHistoryUnderExtension.under_iff_exponential (E - 1) (k + 1)).mpr (by rw [hE1]; exact hE)
  have hunder' (i : V) : bitDef.val.Evalb ![i, E - 1] ↔ i ≤ k := by
    rw [hunder _ _ i hund', lt_succ_iff_le]
  have hdom' : domainDef.val.Evalb ![E - 1, s'] := by
    refine (PRAHistoryDomainExtension.domain_iff hexp (E - 1) s').mpr (fun i => ?_)
    rw [hunder' i]
    constructor
    · intro hik
      obtain ⟨y, -, hy⟩ := entry i (lt_of_le_of_lt hik hkl)
      have hy' := (rel' i y).mpr ⟨hy, hik⟩
      exact ⟨y, vlt hy', hy'⟩
    · rintro ⟨y, -, hy⟩
      exact ((rel' i y).mp hy).2
  have hd' : E - 1 ≤ 2 * s' := by
    have h1 : E - 1 < E := by
      conv_rhs => rw [← hE1]
      exact lt_add_one _
    exact le_of_lt (lt_of_lt_of_le h1 (by rw [hEE, two_mul, two_mul]; exact add_le_add hEks' hEks'))
  have hk1 : k + 1 ≤ 2 * s' := by
    have h1 : k + 1 ≤ s' := lt_iff_succ_le.mp (lt_of_lt_of_le hEk.lt hEks')
    exact le_trans h1 (by rw [two_mul]; exact le_self_add)
  have hmap' : isMappingDef.val.Evalb ![s'] := by
    refine (PRAHistorySequenceExtension.mapping_iff hexp s').mpr ⟨E - 1, hd', hdom', fun i hi => ?_⟩
    have hik := (hunder' i).mp hi
    obtain ⟨y, -, hy⟩ := entry i (lt_of_le_of_lt hik hkl)
    have hy' := (rel' i y).mpr ⟨hy, hik⟩
    exact ⟨y, vlt hy', hy', fun y' _ h => uniq hy ((rel' i y').mp h).1⟩
  have hseq' : seqDef.val.Evalb ![s'] :=
    (seq_iff s').mpr ⟨hmap', k + 1, hk1, E - 1, hd', hdom', hund'⟩
  -- the length of `s'` is `k+1`
  have hlen' {l' : V} (h : lhDef.val.Evalb ![l',s']) : l' = k + 1 := by
    obtain ⟨d'', -, hdom'', hund''⟩ := ((lh_iff l' s').mp h).1 hseq'
    have hdi'' := (PRAHistoryDomainExtension.domain_iff hexp d'' s').mp hdom''
    have hdi' := (PRAHistoryDomainExtension.domain_iff hexp (E - 1) s').mp hdom'
    have same (i : V) : i < l' ↔ i < k + 1 := by
      rw [← hunder d'' l' i hund'', ← hunder _ (k + 1) i hund', hdi'', hdi']
    rcases lt_trichotomy l' (k + 1) with h | h | h
    · exact absurd ((same l').mpr h) (_root_.lt_irrefl l')
    · exact h
    · exact absurd ((same (k + 1)).mp h) (_root_.lt_irrefl _)
  refine ⟨(cseq_iff φ s').mpr ⟨hseq', ⟨lt_of_le_of_lt (by simp)
    (PRAHistoryDomainExtension.bit_lt hexp hpair'), (rel' 0 0).mpr ⟨h00, by simp⟩⟩, ?_⟩,
    hkL', ?_⟩
  · intro x _ l' _ hl' hxl z _ hz
    rw [hlen' hl'] at hxl
    have hxk : x < k := (add_lt_add_iff_right 1).mp hxl
    have hz' := ((rel' x z).mp hz).1
    obtain ⟨y, -, hsy, hy⟩ := hsucc x (lt_of_lt_of_le (lt_trans hxk hks) hs2) l hl hlh
      (lt_of_le_of_lt (lt_iff_succ_le.mp hxk) hkl) z (vlt hz') hz'
    have hy' := (rel' (x + 1) y).mpr ⟨hy, lt_iff_succ_le.mp hxk⟩
    exact ⟨y, vlt hy', hsy, hy'⟩
  · intro y hy
    obtain ⟨hys, hy1⟩ := (hs' y).mp hy
    have hm : memRel.val.Evalb ![s, π₁ y, π₂ y] :=
      (PRAHistorySeqConsMembership.memRel_iff s _ _).mpr (by rw [pair_unpair]; exact hys)
    calc y = ⟪π₁ y, π₂ y⟫ := (pair_unpair y).symm
      _ ≤ ⟪k, E⟫ := pair_le_pair hy1 (le_of_lt (hent hy1 hm))

/-- The collector's guard: `y ∈ π₁ ih` and `π₁ y ≤ π₂ ih`. -/
noncomputable def truncGuard : 𝚺₀.Semisentence 2 := .mkSigma
  “y ih. ∃ a <⁺ ih, !pi₁Def a ih ∧ y ∈ a ∧ ∃ b <⁺ ih, !pi₂Def b ih ∧
    ∃ c <⁺ y, !pi₁Def c y ∧ c ≤ b”

theorem truncGuard_iff (y ih : V) :
    truncGuard.val.Evalb ![y,ih] ↔ bitDef.val.Evalb ![y, π₁ ih] ∧ π₁ y ≤ π₂ ih := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have h1 (a x : V) : pi₁Def.val.Evalb ![a,x] ↔ a = π₁ x := pi₁_defined.defined ![a,x]
  have h2 (a x : V) : pi₂Def.val.Evalb ![a,x] ↔ a = π₂ x := pi₂_defined.defined ![a,x]
  have hg : truncGuard.val.Evalb ![y,ih] ↔ ∃ a ≤ ih, pi₁Def.val.Evalb ![a,ih] ∧
      bitDef.val.Evalb ![y,a] ∧ ∃ b ≤ ih, pi₂Def.val.Evalb ![b,ih] ∧
        ∃ c ≤ y, pi₁Def.val.Evalb ![c,y] ∧ c ≤ b := by
    simp [truncGuard, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
      Semiformula.Operator.val, operator_mem_def, Semiformula.Operator.LT.sentence_eq,
      Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.Eq.sentence_eq, lt_succ_iff_le,
      le_iff_eq_or_lt]
  rw [hg]
  simp only [h1, h2]
  constructor
  · rintro ⟨a, -, rfl, ha, b, -, rfl, c, -, rfl, hc⟩
    exact ⟨ha, hc⟩
  · rintro ⟨ha, hc⟩
    exact ⟨_, pi₁_le_self ih, rfl, ha, _, pi₂_le_self ih, rfl, _, pi₁_le_self y, rfl, hc⟩

end sigma0

section models
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRABoundedCharacteristic
  PRABoundedFormula PRAHistoryFixpointCollector
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

noncomputable def guardMatrix : Semisentence language 2 := Semiformula.lMap embedding truncGuard.val

theorem guardMatrix_bounded : Hierarchy 𝚺 0 guardMatrix :=
  ParsonsHierarchyMap.hierarchy truncGuard.sigma_prop

/-- The candidate-PRA exponential. -/
noncomputable def expF (x : M) : M := Structure.func (L := language) PRAHistoryExpCode.expCode (fun _ => x)

theorem exponential_expF (x : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
    Exponential x (expF x) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  exact (PRAHistoryExpCode.graph_iff x _).mp (PRAHistoryExpCode.modelExpCode x)

/-- **Every history has a truncation of size `2^(⟪k, 2^(k+1)⟫+1)`.** -/
theorem modelTruncate (φ : Fixpoint.Blueprint 0) {s k L : M} :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
    φ.prBlueprint.cseqDef.val.Evalb ![s] → memRel.val.Evalb ![s,k,L] →
      ∃ s', φ.prBlueprint.cseqDef.val.Evalb ![s'] ∧ memRel.val.Evalb ![s',k,L] ∧
        s' < expF (⟪k, expF (k + 1)⟫ + 1) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  intro hs hkL
  have hexp (i : M) : ∃ p, Exponential i p := ⟨_, exponential_expF i⟩
  obtain ⟨ins, hins⟩ := PRAHistoryInsertCode.PRA_has_insertCode
  obtain ⟨good, -, hgbit, hgood⟩ :=
    PRA_proves_boundedBooleanCharacteristic guardMatrix guardMatrix_bounded
  have hbnd : Hierarchy 𝚺 0 PRAHistoryInsertCode.bitGraph :=
    ParsonsHierarchyMap.hierarchy bitDef.sigma_prop
  obtain ⟨bit, -, -, hbit⟩ := PRA_proves_boundedBooleanCharacteristic PRAHistoryInsertCode.bitGraph hbnd
  let s' := Structure.func (L := language) (collectCode good ins) ![s, ⟪s, k⟫]
  have hc := (oneCorrectSentence_iff good guardMatrix).mp
    (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hgood)
  have hs' : ∀ y, bitDef.val.Evalb ![y,s'] ↔ bitDef.val.Evalb ![y,s] ∧ π₁ y ≤ k := by
    intro y
    rw [modelCollectInvariant good ins bit hgbit hins hbit s y ⟪s, k⟫, hc ![y, ⟪s, k⟫],
      guardMatrix, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]
    change _ ∧ truncGuard.val.Evalb ![y, ⟪s, k⟫] ↔ _
    rw [truncGuard_iff, pi₁_pair, pi₂_pair]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨h1, h2⟩; exact ⟨PRAHistoryDomainExtension.bit_lt hexp h1, h1, h2⟩
  obtain ⟨hcs, hkL', hle⟩ := truncate_spec φ hexp
    (fun d l i hd => PRAHistoryUnderCanonical.modelUnderBits d l i hd)
    (exponential_expF (k + 1)) hs hkL hs'
  exact ⟨s', hcs, hkL', lt_exp_of_bits (exponential_expF _)
    (fun j hj => lt_succ_iff_le.mpr (hle j hj))⟩

theorem expF_mono {x y : M} (h : x ≤ y) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
    expF x ≤ expF y := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  exact Exponential.monotone_le (exponential_expF x) (exponential_expF y) h

/-- The history bound of `modelTruncate`, as a monotone function of the stage. -/
noncomputable def histBound (k : M) : M :=
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  expF (⟪k, expF (k + 1)⟫ + 1)

theorem histBound_mono {x y : M} (h : x ≤ y) : histBound x ≤ histBound y := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  exact expF_mono (add_le_add (pair_le_pair h (expF_mono (add_le_add h le_rfl))) le_rfl)

open PRAWitnessCalculus PRAWitnessArithmetic

/-- **Fixpoint stages have bounded witnesses** once the blueprint's core has:
the history is truncated, and every other witness sits below a bounded
universal of `cseqDef`, where the core bounds apply. -/
theorem wb_limSeqDef (φ : Fixpoint.Blueprint 0)
    (hσ : WB M φ.core.sigma.val) (hπ : WB M (∼φ.core.pi.val)) :
    WB M φ.limSeqDef.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hsucc : WB M φ.succDef.val := by
    have := wb_bitDef (M := M); have := wb_neg_bitDef (M := M)
    simp only [Fixpoint.Blueprint.succDef, HierarchySymbol.Semiformula.val_mkSigma]
    wb_auto
  have hcseq : WB M φ.prBlueprint.cseqDef.val := by
    have := wb_seqDef (M := M); have := wb_lhDef (M := M); have := wb_neg_lhDef (M := M)
    have := wb_memRel (M := M); have := wb_neg_memRel (M := M)
    have : WB M memRelOpr.sentence := wb_memRel (M := M)
    have : WB M (∼memRelOpr.sentence) := wb_neg_memRel (M := M)
    simp only [PR.Blueprint.cseqDef, Fixpoint.Blueprint.prBlueprint,
      HierarchySymbol.Semiformula.val_mkSigma]
    wb_auto
  have : WB M memRelOpr.sentence := wb_memRel (M := M)
  simp only [Fixpoint.Blueprint.limSeqDef, PR.Blueprint.resultDef,
    HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs (fun e => histBound (e 1)) (fun e e' h => histBound_mono (h 1)) ?_ (by wb_auto)
  rintro e ⟨x, hx⟩
  obtain ⟨L, k, rfl⟩ : ∃ L k : M, e = ![L, k] := ⟨e 0, e 1, Matrix.fun_eq_vec_two e⟩
  have hx' : φ.prBlueprint.cseqDef.val.Evalb ![x] ∧ memRel.val.Evalb ![x, k, L] := by
    simpa [Semiformula.Operator.val, memRelOpr] using hx
  obtain ⟨s', h1, h2, h3⟩ := modelTruncate φ hx'.1 hx'.2
  refine ⟨s', le_of_lt (show s' < histBound k from h3), ?_⟩
  simpa [Semiformula.Operator.val, memRelOpr] using And.intro h1 h2

theorem limSeq_value_lt (φ : Fixpoint.Blueprint 0) {L k : M} :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
    φ.limSeqDef.val.Evalb ![L,k] → L < histBound k := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  intro h
  have hexp (i : M) : ∃ p, Exponential i p := ⟨_, exponential_expF i⟩
  obtain ⟨s, hs, hkL⟩ : ∃ s, φ.prBlueprint.cseqDef.val.Evalb ![s] ∧ memRel.val.Evalb ![s,k,L] := by
    simpa [Fixpoint.Blueprint.limSeqDef, PR.Blueprint.resultDef, Semiformula.Operator.val,
      memRelOpr] using h
  obtain ⟨s', -, hkL', h3⟩ := modelTruncate φ hs hkL
  exact lt_trans (PRAHistoryDomainExtension.memRel_value_lt hexp hkL') h3

/-- **Fixpoint membership has bounded witnesses**, positively. -/
theorem wb_fixpoint_sigma (φ : Fixpoint.Blueprint 0)
    (hσ : WB M φ.core.sigma.val) (hπ : WB M (∼φ.core.pi.val)) :
    WB M φ.fixpointDefΔ₁.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hl := wb_limSeqDef φ hσ hπ
  have := wb_bitDef (M := M)
  simp only [Fixpoint.Blueprint.fixpointDefΔ₁, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs (fun e => histBound (e 0 + 1)) (fun e e' h => histBound_mono (add_le_add (h 0) le_rfl))
    ?_ (by wb_auto)
  rintro e ⟨L, hL⟩
  obtain ⟨x, rfl⟩ : ∃ x : M, e = ![x] := ⟨e 0, Matrix.fun_eq_vec_one e⟩
  have hlim : φ.limSeqDef.val.Evalb ![L, x + 1] := by
    have h := hL
    simp [Semiformula.Operator.val] at h
    exact h.1
  exact ⟨L, le_of_lt (show L < histBound (x + 1) from limSeq_value_lt φ hlim), hL⟩

/-- **Fixpoint non-membership has bounded witnesses**: the negated `Π` form is
`∃ L, limSeq L (x+1) ∧ x ∉ L`, with the same witness. -/
theorem wb_fixpoint_neg_pi (φ : Fixpoint.Blueprint 0)
    (hσ : WB M φ.core.sigma.val) (hπ : WB M (∼φ.core.pi.val)) :
    WB M (∼φ.fixpointDefΔ₁.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hl := wb_limSeqDef φ hσ hπ
  have := wb_neg_bitDef (M := M)
  simp only [Fixpoint.Blueprint.fixpointDefΔ₁, HierarchySymbol.Semiformula.pi_mkDelta,
    HierarchySymbol.Semiformula.val_mkPi, Semiformula.neg_all, Semiformula.imp_eq, DeMorgan.or,
    DeMorgan.neg]
  refine wb_exs (fun e => histBound (e 0 + 1)) (fun e e' h => histBound_mono (add_le_add (h 0) le_rfl))
    ?_ (by wb_auto)
  rintro e ⟨L, hL⟩
  obtain ⟨x, rfl⟩ : ∃ x : M, e = ![x] := ⟨e 0, Matrix.fun_eq_vec_one e⟩
  have hlim : φ.limSeqDef.val.Evalb ![L, x + 1] := by
    have h := hL
    simp [Semiformula.Operator.val] at h
    exact h.1
  exact ⟨L, le_of_lt (show L < histBound (x + 1) from limSeq_value_lt φ hlim), hL⟩

end models
end DiophantineConsistency.PRAHistoryTruncation
