import DiophantineConsistency.NativePackedMachine54
import DiophantineConsistency.NativeLocalCoefficients54
import Mathlib.Order.Interval.Finset.Fin

/-! # The page's arithmetic mode ranks bind to the actual compact54 table -/

namespace DiophantineConsistency.OnePageModes54

open NativeClauseModes54 NativeModesData54
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024

/-- The unsorted action tile at index `2+j`, with state/read implicit in j. -/
def actionLabel (j : ℕ) : Label :=
  let d := NativePackedMachine54.digit j
  let t := d % 256
  let v := d / 256 % 2
  let h := d / 512
  ⟨(1-h)*(512+t),512+j,h*(256+t),v⟩

/-- The 25 template modes, in their precise order on the printed page. -/
def templates : List (Label × Kind) := [
  (⟨0,942,0,942⟩,.ordinary),(⟨0,943,0,943⟩,.ordinary),
  (⟨0,0,0,0⟩,.ordinary),(⟨0,1,0,1⟩,.ordinary),
  (⟨0,0,0,6⟩,.ordinary),(⟨0,1,0,6⟩,.ordinary),
  (⟨0,942,0,6⟩,.ordinary),(⟨0,943,0,6⟩,.ordinary),
  (⟨2,2,2,0⟩,.ordinary),(⟨3,4,4,698⟩,.ordinary),(⟨4,4,4,0⟩,.ordinary),
  (⟨1,6,1,2⟩,.ordinary),(⟨1,6,1,3⟩,.ordinary),(⟨1,6,1,4⟩,.ordinary),
  (⟨0,5,0,5⟩,.ordinary),(⟨0,5,1,5⟩,.ordinary),(⟨0,5,2,5⟩,.ordinary),
  (⟨1,5,0,5⟩,.ordinary),(⟨1,5,1,5⟩,.ordinary),(⟨1,5,2,5⟩,.ordinary),
  (⟨4,5,0,5⟩,.ordinary),(⟨4,5,1,5⟩,.ordinary),(⟨4,5,2,5⟩,.ordinary),
  (rightLabel,.rightReceiver),(leftLabel,.leftReceiver)]

def tailMode (i : Fin 455) : Label × Kind :=
  if h : i.val < 430 then (actionLabel i.val,.ordinary)
  else templates[i.val-430]'(by change i.val-430<25; omega)

private def prefixMode (i : Fin 2) : Label × Kind :=
  if i.val=0 then (⟨2,3,3,1⟩,.ordinary) else (⟨5,0,0,0⟩,.ordinary)

def unsortedMode (i : Fin 457) : Label × Kind := Fin.addCases (m := 2) (n := 455) prefixMode tailMode i

/-- Base1024 lexicographic keys use four complete label fields. -/
def key (t : Label) : ℕ := 2^30*t.west+2^20*t.north+2^10*t.east+t.south

def Q : ℕ := 2^40

/-- A certificate used only to prove the quotient-rank formula, not part of
its definition and not an extra constant on the equation page. -/
private def forwardList : List (Fin 455) := [
  8,9,373,378,387,379,391,380,10,388,393,381,11,12,13,14,15,16,398,382,
  399,17,408,18,19,20,427,411,395,21,407,383,374,375,22,23,24,25,26,27,
  28,29,30,31,32,33,412,384,413,34,35,36,37,38,39,415,40,41,42,43,
  44,45,46,47,48,49,50,51,419,385,52,376,53,54,55,56,57,58,396,59,
  389,420,60,61,62,400,63,64,65,66,67,68,69,70,71,401,72,73,414,74,
  425,386,75,76,77,78,79,80,416,421,81,82,397,83,84,402,85,86,87,88,
  89,90,91,92,409,424,435,410,93,94,95,96,97,422,98,99,100,101,448,102,
  103,104,428,105,106,426,107,108,109,110,111,112,442,440,113,114,115,116,117,439,
  431,118,119,120,121,418,122,123,124,125,126,127,128,129,130,131,132,133,134,135,
  136,137,138,139,140,141,142,143,144,145,146,449,433,429,147,148,149,150,151,152,
  153,154,155,450,156,157,158,159,160,161,162,163,164,394,165,166,167,168,169,170,
  171,172,451,430,173,174,175,176,177,178,179,452,180,181,182,183,437,377,184,185,
  186,187,188,189,190,403,191,192,193,194,195,196,197,406,198,199,200,201,202,203,
  204,205,206,207,208,209,210,211,212,436,213,404,214,405,215,216,217,218,219,220,
  221,222,223,224,225,226,227,228,229,230,231,446,232,233,444,445,234,235,236,237,
  238,239,240,241,423,441,242,243,244,245,246,247,248,249,250,453,251,252,447,253,
  254,255,256,257,258,259,260,261,262,263,264,265,392,266,432,267,268,269,270,271,
  272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,
  292,293,294,295,296,443,297,298,299,300,301,438,302,303,304,305,306,307,417,434,
  308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,
  328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,
  348,349,350,351,352,353,354,355,390,454,357,359,0,3,1,4,356,358,366,367,
  368,363,364,365,5,6,7,360,361,362,369,370,371,372,2
]
private theorem forward_length : forwardList.length = 455 := by decide
private def forward (i : Fin 455) : Fin 455 :=
  forwardList[i.val]'(by rw [forward_length]; exact i.isLt)
private theorem forward_sorted :
    forwardList.insertionSort (· ≤ ·) = List.finRange 455 := by rfl
private theorem forward_nodup : forwardList.Nodup := by
  have h := (List.perm_insertionSort (· ≤ ·) forwardList).nodup_iff
  rw [forward_sorted] at h
  exact h.mp (List.nodup_finRange 455)
private theorem forward_injective : Function.Injective forward := by
  intro i j h
  apply Fin.ext
  exact forward_nodup.getElem_inj_iff.mp h

/-- The inverse is proof-only; the printed quotient rank and all equation
coefficients are defined independently of this equivalence. -/
noncomputable def tailPermutation : Equiv.Perm (Fin 455) :=
  Equiv.ofBijective forward ⟨forward_injective, Finite.surjective_of_injective forward_injective⟩

/-- The literal finite certificate connects seed decoding and all templates
with the already checked sorted modes. It evaluates no large coefficient port. -/
theorem tailMode_eq (i : Fin 455) :
    tailMode i = mode (Fin.natAdd 2 (tailPermutation i)) := by
  have h : List.ofFn tailMode = List.ofFn (fun j : Fin 455 => mode (Fin.natAdd 2 (tailPermutation j))) := by rfl
  exact congrFun (List.ofFn_injective h) i

private theorem sorted_adjacent (i : Fin 454) :
    key (mode (Fin.natAdd 2 i.castSucc)).1 < key (mode (Fin.natAdd 2 i.succ)).1 := by
  have h : List.ofFn (fun j : Fin 454 => decide (key (mode (Fin.natAdd 2 j.castSucc)).1 <
      key (mode (Fin.natAdd 2 j.succ)).1)) = List.ofFn (fun _ : Fin 454 => true) := by rfl
  exact of_decide_eq_true (congrFun (List.ofFn_injective h) i)

theorem sorted_strict : StrictMono (fun i : Fin 455 => key (mode (Fin.natAdd 2 i)).1) :=
  Fin.strictMono_iff_lt_succ.mpr sorted_adjacent

theorem sorted_key_lt (i : Fin 457) : key (mode i).1 < Q := by
  have h : List.ofFn (fun j : Fin 457 => decide (key (mode j).1 < Q)) =
      List.ofFn (fun _ : Fin 457 => true) := by rfl
  exact of_decide_eq_true (congrFun (List.ofFn_injective h) i)

theorem tail_key_lt (i : Fin 455) : key (tailMode i).1 < Q := by
  rw [tailMode_eq]
  exact sorted_key_lt _


end DiophantineConsistency.OnePageModes54
