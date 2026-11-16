import PA194FileTraversal
import PA194ReturnFileMeaning
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace PA194UpdatedSevenMark
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194RegisterFile PA194ReturnFileMeaning PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- With the exact nine-block remaining file, the first seven physical
blocks form the scanner input and the two-block remainder is even. -/
theorem matchSevenMark (idx n : Nat) (hn : idx+n=7) (e : Fin (idx+2) → M)
    (rest : Fin (n+2) → M) (v : M) :
    ∃ a : Fin 8 → M, ∃ t s next tail : M,
      F (fileCode idx) (replaceLast idx (fun i : Fin (idx+1) => e i.succ)
        (F block ![v,F (fileCode (n+1)) rest])) = F (fileCode 7) a ∧
      a (Fin.last 7) = t+t ∧ t=s+s+1 ∧ s=F PA194UnaryRuns.ones ![next,tail] := by
  have hc : idx=0 ∨ idx=1 ∨ idx=2 ∨ idx=3 ∨ idx=4 ∨ idx=5 ∨ idx=6 ∨ idx=7 := by omega
  rcases hc with h|h|h|h|h|h|h|h <;> subst idx
  · have hnn : n=7 := by omega
    subst n
    let tail := F (fileCode 2) ![rest 6,rest 7,rest 8]
    have heven : ∃ t : M, tail = t+t := by
      dsimp only [tail]
      rw [modelFileSucc,modelBlock]
      exact ⟨_,rfl⟩
    obtain ⟨t,ht⟩ := heven
    have htail : tail = F block ![rest 6,F (fileCode 1) ![rest 7,rest 8]] := by
      dsimp only [tail]
      rw [modelFileSucc]
      rfl
    have hh := congrArg (fun x : M => F halfCode (fun _ => x)) (ht.symm.trans htail)
    rw [modelBlock,(modelDouble t).2,(modelDouble _).2] at hh
    let witness := F PA194UnaryRuns.ones ![rest 6,F (fileCode 1) ![rest 7,rest 8]]
    have hs : t = witness+witness+1 := by
      rw [hh]
      change F PA194UnaryRuns.ones ![F addCode ![rest 6,F oneCode Fin.elim0],F (fileCode 1) ![rest 7,rest 8]] = _
      rw [modelAddOne,PA194UnaryRuns.modelOnesSucc]
    refine ⟨![v,rest 0,rest 1,rest 2,rest 3,rest 4,rest 5,tail],t,witness,rest 6,F (fileCode 1) ![rest 7,rest 8],?_,?_,?_,?_⟩
    · simp only [modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
      simp [replaceLast,Fin.snoc,tail,modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
    · exact ht
    · exact hs
    · rfl
  · have hnn : n=6 := by omega
    subst n
    let tail := F (fileCode 2) ![rest 5,rest 6,rest 7]
    have heven : ∃ t : M, tail = t+t := by
      dsimp only [tail]
      rw [modelFileSucc,modelBlock]
      exact ⟨_,rfl⟩
    obtain ⟨t,ht⟩ := heven
    have htail : tail = F block ![rest 5,F (fileCode 1) ![rest 6,rest 7]] := by
      dsimp only [tail]
      rw [modelFileSucc]
      rfl
    have hh := congrArg (fun x : M => F halfCode (fun _ => x)) (ht.symm.trans htail)
    rw [modelBlock,(modelDouble t).2,(modelDouble _).2] at hh
    let witness := F PA194UnaryRuns.ones ![rest 5,F (fileCode 1) ![rest 6,rest 7]]
    have hs : t = witness+witness+1 := by
      rw [hh]
      change F PA194UnaryRuns.ones ![F addCode ![rest 5,F oneCode Fin.elim0],F (fileCode 1) ![rest 6,rest 7]] = _
      rw [modelAddOne,PA194UnaryRuns.modelOnesSucc]
    refine ⟨![e 1,v,rest 0,rest 1,rest 2,rest 3,rest 4,tail],t,witness,rest 5,F (fileCode 1) ![rest 6,rest 7],?_,?_,?_,?_⟩
    · simp only [modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
      simp [replaceLast,Fin.snoc,tail,modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
    · exact ht
    · exact hs
    · rfl
  · have hnn : n=5 := by omega
    subst n
    let tail := F (fileCode 2) ![rest 4,rest 5,rest 6]
    have heven : ∃ t : M, tail = t+t := by
      dsimp only [tail]
      rw [modelFileSucc,modelBlock]
      exact ⟨_,rfl⟩
    obtain ⟨t,ht⟩ := heven
    have htail : tail = F block ![rest 4,F (fileCode 1) ![rest 5,rest 6]] := by
      dsimp only [tail]
      rw [modelFileSucc]
      rfl
    have hh := congrArg (fun x : M => F halfCode (fun _ => x)) (ht.symm.trans htail)
    rw [modelBlock,(modelDouble t).2,(modelDouble _).2] at hh
    let witness := F PA194UnaryRuns.ones ![rest 4,F (fileCode 1) ![rest 5,rest 6]]
    have hs : t = witness+witness+1 := by
      rw [hh]
      change F PA194UnaryRuns.ones ![F addCode ![rest 4,F oneCode Fin.elim0],F (fileCode 1) ![rest 5,rest 6]] = _
      rw [modelAddOne,PA194UnaryRuns.modelOnesSucc]
    refine ⟨![e 1,e 2,v,rest 0,rest 1,rest 2,rest 3,tail],t,witness,rest 4,F (fileCode 1) ![rest 5,rest 6],?_,?_,?_,?_⟩
    · simp only [modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
      simp [replaceLast,Fin.snoc,tail,modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
    · exact ht
    · exact hs
    · rfl
  · have hnn : n=4 := by omega
    subst n
    let tail := F (fileCode 2) ![rest 3,rest 4,rest 5]
    have heven : ∃ t : M, tail = t+t := by
      dsimp only [tail]
      rw [modelFileSucc,modelBlock]
      exact ⟨_,rfl⟩
    obtain ⟨t,ht⟩ := heven
    have htail : tail = F block ![rest 3,F (fileCode 1) ![rest 4,rest 5]] := by
      dsimp only [tail]
      rw [modelFileSucc]
      rfl
    have hh := congrArg (fun x : M => F halfCode (fun _ => x)) (ht.symm.trans htail)
    rw [modelBlock,(modelDouble t).2,(modelDouble _).2] at hh
    let witness := F PA194UnaryRuns.ones ![rest 3,F (fileCode 1) ![rest 4,rest 5]]
    have hs : t = witness+witness+1 := by
      rw [hh]
      change F PA194UnaryRuns.ones ![F addCode ![rest 3,F oneCode Fin.elim0],F (fileCode 1) ![rest 4,rest 5]] = _
      rw [modelAddOne,PA194UnaryRuns.modelOnesSucc]
    refine ⟨![e 1,e 2,e 3,v,rest 0,rest 1,rest 2,tail],t,witness,rest 3,F (fileCode 1) ![rest 4,rest 5],?_,?_,?_,?_⟩
    · simp only [modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
      simp [replaceLast,Fin.snoc,tail,modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
    · exact ht
    · exact hs
    · rfl
  · have hnn : n=3 := by omega
    subst n
    let tail := F (fileCode 2) ![rest 2,rest 3,rest 4]
    have heven : ∃ t : M, tail = t+t := by
      dsimp only [tail]
      rw [modelFileSucc,modelBlock]
      exact ⟨_,rfl⟩
    obtain ⟨t,ht⟩ := heven
    have htail : tail = F block ![rest 2,F (fileCode 1) ![rest 3,rest 4]] := by
      dsimp only [tail]
      rw [modelFileSucc]
      rfl
    have hh := congrArg (fun x : M => F halfCode (fun _ => x)) (ht.symm.trans htail)
    rw [modelBlock,(modelDouble t).2,(modelDouble _).2] at hh
    let witness := F PA194UnaryRuns.ones ![rest 2,F (fileCode 1) ![rest 3,rest 4]]
    have hs : t = witness+witness+1 := by
      rw [hh]
      change F PA194UnaryRuns.ones ![F addCode ![rest 2,F oneCode Fin.elim0],F (fileCode 1) ![rest 3,rest 4]] = _
      rw [modelAddOne,PA194UnaryRuns.modelOnesSucc]
    refine ⟨![e 1,e 2,e 3,e 4,v,rest 0,rest 1,tail],t,witness,rest 2,F (fileCode 1) ![rest 3,rest 4],?_,?_,?_,?_⟩
    · simp only [modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
      simp [replaceLast,Fin.snoc,tail,modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
    · exact ht
    · exact hs
    · rfl
  · have hnn : n=2 := by omega
    subst n
    let tail := F (fileCode 2) ![rest 1,rest 2,rest 3]
    have heven : ∃ t : M, tail = t+t := by
      dsimp only [tail]
      rw [modelFileSucc,modelBlock]
      exact ⟨_,rfl⟩
    obtain ⟨t,ht⟩ := heven
    have htail : tail = F block ![rest 1,F (fileCode 1) ![rest 2,rest 3]] := by
      dsimp only [tail]
      rw [modelFileSucc]
      rfl
    have hh := congrArg (fun x : M => F halfCode (fun _ => x)) (ht.symm.trans htail)
    rw [modelBlock,(modelDouble t).2,(modelDouble _).2] at hh
    let witness := F PA194UnaryRuns.ones ![rest 1,F (fileCode 1) ![rest 2,rest 3]]
    have hs : t = witness+witness+1 := by
      rw [hh]
      change F PA194UnaryRuns.ones ![F addCode ![rest 1,F oneCode Fin.elim0],F (fileCode 1) ![rest 2,rest 3]] = _
      rw [modelAddOne,PA194UnaryRuns.modelOnesSucc]
    refine ⟨![e 1,e 2,e 3,e 4,e 5,v,rest 0,tail],t,witness,rest 1,F (fileCode 1) ![rest 2,rest 3],?_,?_,?_,?_⟩
    · simp only [modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
      simp [replaceLast,Fin.snoc,tail,modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
    · exact ht
    · exact hs
    · rfl
  · have hnn : n=1 := by omega
    subst n
    let tail := F (fileCode 2) ![rest 0,rest 1,rest 2]
    have heven : ∃ t : M, tail = t+t := by
      dsimp only [tail]
      rw [modelFileSucc,modelBlock]
      exact ⟨_,rfl⟩
    obtain ⟨t,ht⟩ := heven
    have htail : tail = F block ![rest 0,F (fileCode 1) ![rest 1,rest 2]] := by
      dsimp only [tail]
      rw [modelFileSucc]
      rfl
    have hh := congrArg (fun x : M => F halfCode (fun _ => x)) (ht.symm.trans htail)
    rw [modelBlock,(modelDouble t).2,(modelDouble _).2] at hh
    let witness := F PA194UnaryRuns.ones ![rest 0,F (fileCode 1) ![rest 1,rest 2]]
    have hs : t = witness+witness+1 := by
      rw [hh]
      change F PA194UnaryRuns.ones ![F addCode ![rest 0,F oneCode Fin.elim0],F (fileCode 1) ![rest 1,rest 2]] = _
      rw [modelAddOne,PA194UnaryRuns.modelOnesSucc]
    refine ⟨![e 1,e 2,e 3,e 4,e 5,e 6,v,tail],t,witness,rest 0,F (fileCode 1) ![rest 1,rest 2],?_,?_,?_,?_⟩
    · simp only [modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
      simp [replaceLast,Fin.snoc,tail,modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
    · exact ht
    · exact hs
    · rfl
  · have hnn : n=0 := by omega
    subst n
    let tail := F block ![v,F (fileCode 1) rest]
    have heven : ∃ t : M, tail = t+t := by
      dsimp only [tail]
      rw [modelBlock]
      exact ⟨_,rfl⟩
    obtain ⟨t,ht⟩ := heven
    have htail : tail = F block ![v,F (fileCode 1) rest] := by
      dsimp only [tail]
    have hh := congrArg (fun x : M => F halfCode (fun _ => x)) (ht.symm.trans htail)
    rw [modelBlock,(modelDouble t).2,(modelDouble _).2] at hh
    let witness := F PA194UnaryRuns.ones ![v,F (fileCode 1) rest]
    have hs : t = witness+witness+1 := by
      rw [hh]
      change F PA194UnaryRuns.ones ![F addCode ![v,F oneCode Fin.elim0],F (fileCode 1) rest] = _
      rw [modelAddOne,PA194UnaryRuns.modelOnesSucc]
    refine ⟨![e 1,e 2,e 3,e 4,e 5,e 6,e 7,tail],t,witness,v,F (fileCode 1) rest,?_,?_,?_,?_⟩
    · simp only [modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
      simp [replaceLast,Fin.snoc,tail,modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
    · exact ht
    · exact hs
    · rfl
#print axioms matchSevenMark
end models
end PA194UpdatedSevenMark
