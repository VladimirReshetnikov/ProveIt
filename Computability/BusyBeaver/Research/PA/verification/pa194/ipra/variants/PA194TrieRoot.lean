import PA194SourceContracts
import PA194CompressedSourceFrame
import PA194ClockInvariantDefinable
import PA194HalfDiv

/-! Arithmetic encoding of the source root for variant address tries. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194TrieRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PRATermCompilation
open PA194BinaryDouble (unary modelUnary)
open PA194CompressedRootCode (indexed indexedCorrect wordCode wordCodeCorrect)
open PA194CompressedSourceFrame (args packedFileCode packedFileCodeCorrect)
open PA194ClockInvariantDefinable PA194SourceControllerCode
open PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194FiniteControls PA194HalfDiv PA194StateOne
open ConPA.Machine ConPA.Machine.Compressed
open M6.Runtime

def trieDepth : M6.Source.PathTrie.Tree → Nat
  | .leaf _ => 0
  | .node l r => 1 + max (trieDepth l) (trieDepth r)

private theorem depth_bounds (tree : M6.Source.PathTrie.Tree) (site : M6.Source.Site)
    (hm : site ∈ M6.Source.PathTrie.flatten tree) : site.path.length ≤ trieDepth tree := by
  induction tree generalizing site with
  | leaf op =>
    simp only [M6.Source.PathTrie.flatten, List.mem_singleton] at hm
    subst site
    rfl
  | node l r hl hr =>
    simp only [M6.Source.PathTrie.flatten, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨site, hm, rfl⟩ | ⟨site, hm, rfl⟩
    · have hb := (hl site hm).trans (Nat.le_max_left (trieDepth l) (trieDepth r))
      simpa [M6.Source.PathTrie.prepend, trieDepth, Nat.add_comm] using Nat.succ_le_succ hb
    · have hb := (hr site hm).trans (Nat.le_max_right (trieDepth l) (trieDepth r))
      simpa [M6.Source.PathTrie.prepend, trieDepth, Nat.add_comm] using Nat.succ_le_succ hb

def triePath (tree : M6.Source.PathTrie.Tree) (i : Nat) : M6.Source.Path :=
  ((M6.Source.PathTrie.nthSite tree i).map (·.path)).getD []

theorem path_short (tree : M6.Source.PathTrie.Tree) (depth : trieDepth tree ≤ 48) (i : Nat) :
    (triePath tree i).length ≤ 48 := by
  unfold triePath
  rw [M6.Source.PathTrie.nthSite_eq]
  cases hs : getElem? (M6.Source.PathTrie.flatten tree) i with
  | none => simp
  | some s =>
    have hm := List.mem_of_getElem? hs
    simpa using (depth_bounds tree s hm).trans depth

variable (path : Nat → M6.Source.Path)

private def pathCodesFor (sites : Nat) : List (Code 1) := (List.range sites).map (wordCode ∘ path)

private def offsetsFor (sites : Nat) : List Nat := (List.range sites).map (fun i => 48-(path i).length)

private def rightHalfFor (sites : Nat) : Code 3 := bin (indexed (pathCodesFor path sites)) (.proj 0)
  (bin zeros (bin addCode (.proj 1) (unary (lookupCode 0 (offsetsFor path sites)) (.proj 0))) (unary pushOne (.proj 2)))

/-- The physical root as a function of the source ordinal, extra gap, and register file. -/
def rootCodeFor (sites : Nat) : Code 3 :=
  bin pairCode (unary (constantCode 24) (.proj 0))
    (bin pairCode (unary (constantCode 1) (.proj 0)) (rightHalfFor path sites))

/-- Use the common register file with a table-specific address lookup. -/
def sourceRootCodeFor (sites : Nat) : Code 4 := .comp (rootCodeFor path sites) (pack 3 ![unary pc (.proj 0),.proj 1,
  .comp packedFileCode (pack 3 ![.proj 0,.proj 2,.proj 3])])

abbrev pathCodes : List (Code 1) := pathCodesFor path 3673
abbrev offsets : List Nat := offsetsFor path 3673
abbrev rightHalf : Code 3 := rightHalfFor path 3673
abbrev rootCode : Code 3 := rootCodeFor path 3673
abbrev sourceRootCode : Code 4 := sourceRootCodeFor path 3673

private theorem pathCodeAt {sites : Nat} (i : Fin sites) :
    (pathCodesFor path sites).getD i.val (.proj 0) = wordCode (path i.val) := by
  have hi : i.val < (pathCodesFor path sites).length := by simpa [pathCodesFor] using i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  simp [pathCodesFor]

private theorem offsetAt {sites : Nat} (i : Fin sites) :
    (offsetsFor path sites).getD i.val 0 = 48-(path i.val).length := by
  have hi : i.val < (offsetsFor path sites).length := by simpa [offsetsFor] using i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  simp [offsetsFor]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (label : Nat → Nat)

private theorem zeros_eq (n x : M) : F zeros ![n,x] = bitPrefix false n x := by
  have hp : 𝚺₁-Function₂ (bitPrefix (V := M) false) := by
    change 𝚺₁-Function₂ (fun n x : M => Exp.exp n * x)
    definability
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact equalPred _ _ (bindBinary _ x (binaryCodeDef zeros)) (bindBinary _ x hp)
  | zero => rw [modelZerosZero, bitPrefix_zero]
  | succ n ih =>
    have hz := PA194BidirectionalRunScan.runSucc false n x
    change F zeros ![n + 1,x] = F zeros ![n,x] + F zeros ![n,x] at hz
    rw [hz, ih, bitPrefix_succ]
    simp [two_mul]

private theorem word_eq (bits : List Bool) (x : M) :
    bits.foldr ConPA.Machine.Compressed.push x = modelWord bits x := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simp only [List.foldr_cons, ih, PA194SymbolicMove.wordPush]
    cases bit <;> simp [ConPA.Machine.Compressed.push, PA194BidirectionalRow.push, two_mul]

theorem root_eval (rootControl : label 84 = 24) (gap : M) (box : BoxSt → M) (i extra : Nat) (effect : Eff) :
    PA194SourceContracts.root label path gap box i extra effect =
      ⟪(24 : M),(1 : M),modelWord (path i)
        (F zeros ![gap+modelNumeral M (48+extra-(path i).length),
          F pushOne (fun _ => box (.plain effect))])⟫ := by
  simp only [PA194SourceContracts.root, PA194RuntimeContracts.rootFrame, encode, scanFrame, if_true,
    rootControl, packBits, packSegments, runLength, Nat.cast_one, one_mul,
    modelNumeralCast, word_eq, zeros_eq, modelPushOne]
  simp [ConPA.Machine.Compressed.push, two_mul]

theorem root_advanced_gap (rootControl : label 84 = 24)
    (short : ∀ i, (path i).length ≤ 48) (gap : M) (box : BoxSt → M) (i : Nat) (effect : Eff) :
    PA194SourceContracts.root label path gap box i 1 effect = PA194SourceContracts.root label path (gap + 1) box i 0 effect := by
  rw [root_eval _ _ rootControl, root_eval _ _ rootControl]
  have hs := short i
  have h : 48+1-(path i).length = 1+(48-(path i).length) := by omega
  rw [h, modelNumeralAdd, modelNumeralOne, Nat.add_zero, add_assoc]

theorem rootCodeFor_eval {sites : Nat} (rootControl : label 84 = 24) (i : Fin sites) (gap file : M) :
    F (rootCodeFor path sites) ![modelNumeral M i.val,gap,file] =
      PA194SourceContracts.root label path gap (fun _ => file) i.val := by
  rw [root_eval _ _ rootControl]
  simp only [rootCodeFor, rightHalfFor, modelBin, modelUnary, modelProjection,
    modelConstant, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    modelLookupNumeral, offsetAt, modelPairCode, modelNumeralOne]
  rw [indexedCorrect, pathCodeAt, wordCodeCorrect]
  simp only [Nat.add_zero, modelNumeralCast, Nat.cast_ofNat, Nat.cast_one] <;> rfl

theorem rootCode_eval (rootControl : label 84 = 24) (i : Fin 3673) (gap file : M) :
    F (rootCode path) ![modelNumeral M i.val,gap,file] =
      PA194SourceContracts.root label path gap (fun _ => file) i.val :=
  rootCodeFor_eval path label rootControl i gap file

theorem root_initial_file (rootControl : label 84 = 24) (gap : M) (box : BoxSt → M) (i : Nat) (effect : Eff) :
    PA194SourceContracts.root label path gap box i 0 effect =
      PA194SourceContracts.root label path gap (fun _ => box (.plain effect)) i := by
  rw [root_eval _ _ rootControl, root_eval _ _ rootControl]

theorem sourceRootFor_eval {sites : Nat} (rootControl : label 84 = 24) (s gap count spare : M) (i : Fin sites)
    (hpc : F pc ![s] = modelNumeral M i.val) :
    F (sourceRootCodeFor path sites) ![s,gap,count,spare] =
      PA194SourceContracts.root label path gap (fun _ => F PA194RegisterPermutation.sourceFileCode (args s count spare)) i.val := by
  rw [sourceRootCodeFor, modelComposition, getCode_pack]
  have he : (fun j : Fin 3 => F (![unary pc (.proj 0),.proj 1,
      .comp packedFileCode (pack 3 ![.proj 0,.proj 2,.proj 3])] j : Code 4) ![s,gap,count,spare]) =
      ![modelNumeral M i.val,gap,F PA194RegisterPermutation.sourceFileCode (args s count spare)] := by
    funext j
    fin_cases j
    · change F (unary pc (.proj 0)) ![s,gap,count,spare] = modelNumeral M i.val
      rw [modelUnary, modelProjection]
      have hv : (fun _ : Fin 1 => s) = ![s] := by
        funext j
        exact Fin.cases rfl (fun k => Fin.elim0 k) j
      change F pc (fun _ => s) = modelNumeral M i.val
      rw [hv]
      exact hpc
    · exact modelProjection _ _
    · change F (.comp packedFileCode (pack 3 ![.proj 0,.proj 2,.proj 3])) ![s,gap,count,spare] = _
      rw [modelComposition, getCode_pack]
      have hv : (fun j : Fin 3 => F (![.proj 0,.proj 2,.proj 3] j : Code 4) ![s,gap,count,spare]) =
          ![s,count,spare] := by
        funext j
        fin_cases j <;> exact modelProjection _ _
      rw [hv, packedFileCodeCorrect] <;> rfl
  rw [he, rootCodeFor_eval _ _ rootControl]

theorem sourceRoot_eval (rootControl : label 84 = 24) (s gap count spare : M) (i : Fin 3673)
    (hpc : F pc ![s] = modelNumeral M i.val) :
    F (sourceRootCode path) ![s,gap,count,spare] =
      PA194SourceContracts.root label path gap (fun _ => F PA194RegisterPermutation.sourceFileCode (args s count spare)) i.val :=
  sourceRootFor_eval path label rootControl s gap count spare i hpc

#print axioms sourceRootFor_eval
#print axioms sourceRoot_eval
#print axioms root_advanced_gap
end models
end PA194TrieRoot
