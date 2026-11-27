import DiophantineConsistency.NativeStencil54
import DiophantineConsistency.NativeSelectorClause54

/-! # A pure finite coefficient identity for the compact54 native cell -/

namespace DiophantineConsistency.NativeCellRecipe54

open NativeStencil54 NativeClauseBits54 NativeSelectorClause54 NativeLocalCoefficients54 NativeModesData54
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local irreducible] modeList Finset.sum

/-- Separate the 457 selector coefficients from the fixed bit-position syntax. -/
def shape (a : Fin 457 → ℕ) : List (ℕ × ℕ) :=
  List.ofFn (fun i : Fin 457 => (i.val,a i)) ++
  List.ofFn (fun j : Fin 42 => (copyPosition j,copyBitCoefficient j)) ++
  List.ofFn (fun j : Fin 8 => (567+j.val,rightBitCoefficient j)) ++
  List.ofFn (fun j : Fin 8 => (575+j.val,leftBitCoefficient j)) ++
  [(583,commonBitCoefficient),(1203,anchorCoefficient),(1807,anchorCoefficient),(507,0),(508,0)]

private theorem zipIdx_modes : List.ofFn (fun i : Fin 457 => (mode i,i.val)) = modeList.zipIdx := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_zipIdx,modeList_length]
  · intro j h₁ h₂
    simp only [List.getElem_ofFn,List.getElem_zipIdx,mode,Nat.zero_add]

/-- Pure finite metadata equality, before inserting any assignment values. -/
theorem entries_eq_shape : NativeStencil54.entries =
    shape (fun i : Fin 457 => selectorCoefficient (mode i).2 (mode i).1) := by
  have hs : (modeList.zipIdx.map fun p => (p.2,selectorCoefficient p.1.2 p.1.1)) =
      List.ofFn (fun i : Fin 457 => (i.val,selectorCoefficient (mode i).2 (mode i).1)) := by
    rw [← zipIdx_modes,List.map_ofFn]
    apply congrArg (fun g : Fin 457 → ℕ × ℕ => List.ofFn g)
    funext i
    rfl
  unfold NativeStencil54.entries shape
  rw [hs,
    List.ofFn_eq_map (f := fun j : Fin 42 => (copyPosition j,copyBitCoefficient j)),
    List.ofFn_eq_map (f := fun j : Fin 8 => (567+j.val,rightBitCoefficient j)),
    List.ofFn_eq_map (f := fun j : Fin 8 => (575+j.val,leftBitCoefficient j))]

private theorem map_commuted (l : List (ℕ × ℕ)) (f : ℕ → ℕ) :
    l.map (fun p => p.2*f p.1) = l.map (fun p => f p.1*p.2) := by
  apply List.map_congr_left
  intro p _
  exact Nat.mul_comm _ _

private theorem mapped_sum_append (f : ℕ → ℕ) (l r : List (ℕ × ℕ)) :
    ((l ++ r).map fun p => f p.1 * p.2).sum =
      (l.map fun p => f p.1 * p.2).sum + (r.map fun p => f p.1 * p.2).sum := by
  rw [List.map_append, List.sum_append]

private theorem mapped_sum_ofFn {n : ℕ} (f : ℕ → ℕ) (p a : Fin n → ℕ) :
    ((List.ofFn fun i => (p i, a i)).map fun (q : ℕ × ℕ) => f q.1 * q.2).sum =
      ∑ i, f (p i) * a i := by
  calc
    _ = (List.ofFn fun i => f (p i) * a i).sum := congrArg List.sum List.map_ofFn
    _ = _ := Fin.sum_ofFn _

private theorem mapped_sum_tail (f : ℕ → ℕ) (p₀ p₁ p₂ p₃ p₄ a₀ a₁ a₂ : ℕ) :
    ([(p₀, a₀), (p₁, a₁), (p₂, a₂), (p₃, 0), (p₄, 0)].map
      fun (p : ℕ × ℕ) => f p.1 * p.2).sum =
      f p₀ * a₀ + (f p₁ * a₁ + f p₂ * a₂) := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mul_zero, add_zero]

/-- The semantic sum is checked with an abstract selector coefficient
function and abstract segment lengths. -/
theorem shape_sum (a : Fin 457 → ℕ) (f : ℕ → ℕ) :
    ((shape a).map fun p => f p.1*p.2).sum =
      (∑ i : Fin 457, f i.val*a i) +
      (∑ j : Fin 42, f (copyPosition j)*copyBitCoefficient j) +
      (∑ j : Fin 8, f (567+j.val)*rightBitCoefficient j) +
      (∑ j : Fin 8, f (575+j.val)*leftBitCoefficient j) +
      (f 583*commonBitCoefficient+(f 1203*anchorCoefficient+f 1807*anchorCoefficient)) := by
  simp only [shape, mapped_sum_append, mapped_sum_ofFn, mapped_sum_tail]

private theorem selector_word (f : ℕ → ℕ) : selectorWord (fun i : Fin 457 => f i.val) =
    ∑ i : Fin 457, f i.val*selectorCoefficient (mode i).2 (mode i).1 := rfl

private theorem regroup (sel cop rig lef com a1 a2 : ℕ) :
    sel+cop+rig+lef+(com+(a1+a2)) = sel+(rig+lef+com)+(cop+a1+a2) := by omega

/-- Every literal coefficient, copied-bit position and anchor agrees with
the local decoder for an arbitrary assignment of values to positions. -/
theorem coefficient_sum_eq_nativeWord (f : ℕ → ℕ) :
    (NativeStencil54.entries.map fun p => p.2*f p.1).sum =
      nativeWord (fun i : Fin 457 => f i.val)
        (binaryValue (fun i : Fin 8 => f (567+i.val)))
        (binaryValue (fun i : Fin 8 => f (575+i.val))) (f 583)
        (binaryValue (fun i : Fin 42 => f (copyPosition i)))
        (f 539) (f 1203) (f 1807) := by
  have he := congrArg (fun l : List (ℕ × ℕ) => (l.map fun p => f p.1*p.2).sum) entries_eq_shape
  rw [map_commuted NativeStencil54.entries f,he,
    shape_sum (fun i : Fin 457 => selectorCoefficient (mode i).2 (mode i).1) f,
    ← selector_word f]
  have hc := copiedWord_eq_bit_sum (fun i : Fin 42 => f (copyPosition i)) (f 1203) (f 1807)
  rw [show copyPosition (0 : Fin 42) = 539 from rfl] at hc
  rw [nativeWord,
    auxiliaryWord_eq_bit_sum (fun i : Fin 8 => f (567+i.val))
      (fun i : Fin 8 => f (575+i.val)) (f 583),hc]
  exact regroup
    (selectorWord (fun i : Fin 457 => f i.val))
    (∑ i : Fin 42, f (copyPosition i)*copyBitCoefficient i)
    (∑ i : Fin 8, f (567+i.val)*rightBitCoefficient i)
    (∑ i : Fin 8, f (575+i.val)*leftBitCoefficient i)
    (f 583*commonBitCoefficient) (f 1203*anchorCoefficient) (f 1807*anchorCoefficient)

end DiophantineConsistency.NativeCellRecipe54
