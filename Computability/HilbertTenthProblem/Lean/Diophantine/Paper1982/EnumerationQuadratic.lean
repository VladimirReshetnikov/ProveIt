import Diophantine.Paper1978.Godel

/-!
# A finite quadratic gate system for the 1978 Diophantine enumeration

The existing enumeration represents every Diophantine set by some `W n`
on positive inputs. For each fixed `n`, membership in `W n` is equivalent
to finitely many integer addition and multiplication gates. There are
`3*(n+1)` integer node values. The extra final group of gates lets the
construction include `n = 0` without a separate case.

The converse uses the proved recursion reconstruction `Jones1978.S_eq_P`.
No conversion to natural witnesses, polynomial assembly, or claim that all
recursively enumerable sets are Diophantine is made in this module.
-/

namespace Jones1982
namespace EnumerationQuadratic

/-- Node positions needed for the addition and multiplication gates at
indices `0, …, n`, inclusive. -/
abbrev GateIndex (n : ℕ) := Fin (3 * (n + 1))

@[simp] theorem card_gateIndex (n : ℕ) :
    Fintype.card (GateIndex n) = 3 * (n + 1) := by
  simp [GateIndex]

def nodeZero (n : ℕ) : GateIndex n := ⟨0, by omega⟩

def nodeAdd (n : ℕ) (i : Fin (n + 1)) : GateIndex n :=
  ⟨3 * i.val, by omega⟩

def nodeMul (n : ℕ) (i : Fin (n + 1)) : GateIndex n :=
  ⟨3 * i.val + 1, by omega⟩

def nodeLeft (n : ℕ) (i : Fin (n + 1)) : GateIndex n :=
  ⟨Jones1978.K i.val, by have := Jones1978.K_le i.val; omega⟩

def nodeRight (n : ℕ) (i : Fin (n + 1)) : GateIndex n :=
  ⟨Jones1978.L i.val, by have := Jones1978.L_le i.val; omega⟩

/-- A finite system of integer equations, each of degree at most two
in the node values and input. The enumeration index is fixed. -/
structure GateSys (n x : ℕ) (t : GateIndex n → ℤ) : Prop where
  zero : t (nodeZero n) = 0
  output : t (nodeLeft n (Fin.last n)) = t (nodeRight n (Fin.last n)) + x
  add : ∀ i : Fin (n + 1),
    t (nodeAdd n i) = t (nodeLeft n i) + t (nodeRight n i)
  mul : ∀ i : Fin (n + 1),
    t (nodeMul n i) = t (nodeLeft n i) * t (nodeRight n i)

/-- Evaluate the finitely many enumeration polynomials at one integer
assignment to their original variables. -/
def values (n : ℕ) (X : ℕ → ℤ) : GateIndex n → ℤ :=
  fun k => Jones1978.P k.val X

/-- The original enumeration values satisfy every gate. -/
theorem exists_gateSys_of_mem {n x : ℕ} (h : x ∈ Jones1978.W n) :
    ∃ t : GateIndex n → ℤ, GateSys n x t := by
  obtain ⟨X, hX⟩ := h
  refine ⟨values n X, ?_⟩
  exact {
    zero := Jones1978.P_zero X
    output := hX
    add := fun i => Jones1978.P_add' i.val X
    mul := fun i => Jones1978.P_mul i.val X
  }

/-- Extend a finite node assignment by zero outside its range, so it can
be supplied to the existing sequence reconstruction theorem. -/
def extend {n : ℕ} (t : GateIndex n → ℤ) (k : ℕ) : ℤ :=
  if hk : k < 3 * (n + 1) then t ⟨k, hk⟩ else 0

@[simp] theorem extend_at {n : ℕ} (t : GateIndex n → ℤ) (k : GateIndex n) :
    extend t k.val = t k := by
  simp [extend, k.isLt]

/-- The gate recurrences reconstruct the enumeration values, hence the
output equation gives membership in `W n`. -/
theorem mem_of_gateSys {n x : ℕ} {t : GateIndex n → ℤ} (h : GateSys n x t) :
    x ∈ Jones1978.W n := by
  have h0 : extend t 0 = 0 := by
    have hz := h.zero
    rw [← extend_at t (nodeZero n)] at hz
    simpa only [nodeZero] using hz
  have hrec : ∀ i < n + 1,
      extend t (3 * i) = extend t (Jones1978.K i) + extend t (Jones1978.L i) ∧
      extend t (3 * i + 1) = extend t (Jones1978.K i) * extend t (Jones1978.L i) := by
    intro i hi
    let j : Fin (n + 1) := ⟨i, hi⟩
    constructor
    · have ha := h.add j
      rw [← extend_at t (nodeAdd n j), ← extend_at t (nodeLeft n j),
        ← extend_at t (nodeRight n j)] at ha
      simpa only [nodeAdd, nodeLeft, nodeRight, j] using ha
    · have hm := h.mul j
      rw [← extend_at t (nodeMul n j), ← extend_at t (nodeLeft n j),
        ← extend_at t (nodeRight n j)] at hm
      simpa only [nodeMul, nodeLeft, nodeRight, j] using hm
  have hvalues := Jones1978.S_eq_P (n := n + 1) h0 hrec
  refine ⟨fun j => extend t (3 * j + 2), ?_⟩
  rw [← hvalues (Jones1978.K n) (by have := Jones1978.K_le n; omega),
    ← hvalues (Jones1978.L n) (by have := Jones1978.L_le n; omega)]
  have hout := h.output
  rw [← extend_at t (nodeLeft n (Fin.last n)),
    ← extend_at t (nodeRight n (Fin.last n))] at hout
  simpa only [nodeLeft, nodeRight, Fin.val_last] using hout

/-- A finite quadratic integer gate system characterizes each member of
the 1978 enumeration. This holds for all natural inputs, so in particular
for the positive inputs used in the enumeration's representation theorem. -/
theorem mem_W_iff_gateSys (n x : ℕ) :
    x ∈ Jones1978.W n ↔ ∃ t : GateIndex n → ℤ, GateSys n x t :=
  ⟨exists_gateSys_of_mem, fun ⟨_, h⟩ => mem_of_gateSys h⟩

/-- Every Diophantine set, with an arbitrary-degree representing polynomial,
is represented on positive inputs by one of these finite quadratic systems.
The gate values are still integers at this stage. -/
theorem exists_gateSys_representation {S : Set ℕ} (hS : Jones1978.IsDiophantine S) :
    ∃ n : ℕ, ∀ x : ℕ, 0 < x →
      (x ∈ S ↔ ∃ t : GateIndex n → ℤ, GateSys n x t) := by
  obtain ⟨n, hn⟩ := Jones1978.lemma_3_1 hS
  exact ⟨n, fun x hx => (hn x hx).trans (mem_W_iff_gateSys n x)⟩

end EnumerationQuadratic
end Jones1982
