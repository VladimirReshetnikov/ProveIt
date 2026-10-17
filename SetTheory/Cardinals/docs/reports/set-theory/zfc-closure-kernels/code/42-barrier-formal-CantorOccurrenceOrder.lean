import Std

/-!
Exact Cantor/command-code facts supporting the earlier-DROP injection.

`tri`, `P`, `Cmd`, `pack`, and `encL` reproduce the definitions in ProveIt's
2026-10-16 source archive, `FirstOrder/Fol.lean` and
`BusyBeaver/ZFC/Enum254.lean`. The short Cantor injectivity proof is adapted
from that archive. The monotonicity/context and marked-replacement results
are the new application. This file does not formalize the time schedule of
the concrete register-machine enumerator or its Turing-machine simulation.
-/

namespace CantorOccurrenceOrder

def tri : Nat → Nat
  | 0 => 0
  | n + 1 => tri n + n + 1

def P (x y : Nat) : Nat := y + tri (x + y)

theorem tri_mono {m n : Nat} (h : m ≤ n) : tri m ≤ tri n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => simp only [tri]; omega

theorem tri_strict {m n : Nat} (h : m < n) : tri m < tri n := by
  have hm := tri_mono (Nat.succ_le_of_lt h)
  simp only [tri] at hm
  omega

theorem P_left_strict (y : Nat) {a b : Nat} (h : a < b) : P a y < P b y := by
  have ht := tri_strict (show a + y < b + y by omega)
  simp only [P]
  omega

theorem P_right_strict (x : Nat) {a b : Nat} (h : a < b) : P x a < P x b := by
  have ht := tri_strict (show x + a < x + b by omega)
  simp only [P]
  omega

theorem P_injective {x₁ y₁ x₂ y₂ : Nat} (h : P x₁ y₁ = P x₂ y₂) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  simp only [P] at h
  have hs : x₁ + y₁ = x₂ + y₂ := by
    rcases Nat.lt_trichotomy (x₁ + y₁) (x₂ + y₂) with hlt | heq | hgt
    · have hm := tri_mono (Nat.succ_le_of_lt hlt)
      simp only [tri] at hm; omega
    · exact heq
    · have hm := tri_mono (Nat.succ_le_of_lt hgt)
      simp only [tri] at hm; omega
  have ht : tri (x₁ + y₁) = tri (x₂ + y₂) := by rw [hs]
  omega

@[simp] theorem P_eq_iff (x₁ y₁ x₂ y₂ : Nat) :
    P x₁ y₁ = P x₂ y₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  constructor
  · exact P_injective
  · rintro ⟨rfl, rfl⟩; rfl

inductive Cmd where
  | mp (x : Nat)
  | drop (x : Nat)
  | nip (x : Nat)
  | ax (c x y u : Nat)
  deriving DecidableEq

def pack : Cmd → Nat → Nat
  | .mp x, r => P 0 (P x r)
  | .drop x, r => P 1 (P x r)
  | .nip x, r => P 2 (P x r)
  | .ax c x y u, r => P (c + 3) (P x (P y (P u r)))

def encL : Cmd → List Cmd → Nat
  | c, [] => pack c 0
  | c, c' :: cs => pack c (encL c' cs + 1)

theorem pack_strict (c : Cmd) {r s : Nat} (h : r < s) : pack c r < pack c s := by
  cases c with
  | mp x => exact P_right_strict 0 (P_right_strict x h)
  | drop x => exact P_right_strict 1 (P_right_strict x h)
  | nip x => exact P_right_strict 2 (P_right_strict x h)
  | ax c x y u =>
    exact P_right_strict (c + 3)
      (P_right_strict x (P_right_strict y (P_right_strict u h)))

theorem drop_lt_nip (x r : Nat) : pack (.drop x) r < pack (.nip x) r :=
  P_left_strict (P x r) (by omega)

theorem pack_injective {c d : Cmd} {r s : Nat} (h : pack c r = pack d s) :
    c = d ∧ r = s := by
  cases c <;> cases d <;> simp_all [pack]

/-- Nonempty command lists have unique numerical codes. Empty lists are not
included, since the single command MP0 itself has code zero. -/
theorem encL_injective (c : Cmd) (cs : List Cmd) (d : Cmd) (ds : List Cmd)
    (h : encL c cs = encL d ds) : c = d ∧ cs = ds := by
  induction cs generalizing c d ds with
  | nil =>
    cases ds with
    | nil => exact ⟨(pack_injective h).1, rfl⟩
    | cons d' ds =>
      have := (pack_injective h).2
      omega
  | cons c' cs ih =>
    cases ds with
    | nil =>
      have := (pack_injective h).2
      omega
    | cons d' ds =>
      obtain ⟨hcd, htail⟩ := pack_injective h
      have ht : encL c' cs = encL d' ds := by omega
      obtain ⟨hhead, hrest⟩ := ih c' d' ds ht
      exact ⟨hcd, by rw [hhead, hrest]⟩

/-- Code a fixed prefix before an already coded, nonempty suffix. -/
def context : List Cmd → Nat → Nat
  | [], r => r
  | c :: cs, r => pack c (context cs r + 1)

theorem context_strict (cs : List Cmd) {r s : Nat} (h : r < s) :
    context cs r < context cs s := by
  induction cs with
  | nil => exact h
  | cons c cs ih => exact pack_strict c (by omega)

/-- Replacing a marked NIP by DROP strictly lowers the whole candidate code,
for every fixed prefix, suffix, and command parameter. -/
theorem marked_drop_earlier (pre suf : List Cmd) (x : Nat) :
    context pre (encL (.drop x) suf) <
      context pre (encL (.nip x) suf) := by
  apply context_strict
  cases suf with
  | nil => exact drop_lt_nip x 0
  | cons c cs => exact drop_lt_nip x (encL c cs + 1)

/-- The involution changes only the marked opcode, preserving its parameter. -/
def swap : Cmd → Cmd
  | .drop x => .nip x
  | .nip x => .drop x
  | c => c

theorem swap_involutive (c : Cmd) : swap (swap c) = c := by cases c <;> rfl

def swapAt : Nat → List Cmd → List Cmd
  | _, [] => []
  | 0, c :: cs => swap c :: cs
  | n + 1, c :: cs => c :: swapAt n cs

theorem swapAt_involutive (n : Nat) (cs : List Cmd) :
    swapAt n (swapAt n cs) = cs := by
  induction n generalizing cs with
  | zero => cases cs <;> simp [swapAt, swap_involutive]
  | succ n ih => cases cs <;> simp [swapAt, ih]

theorem swapAt_injective (n : Nat) {cs ds : List Cmd}
    (h : swapAt n cs = swapAt n ds) : cs = ds := by
  have hh := congrArg (swapAt n) h
  simpa only [swapAt_involutive] using hh

def listCode : List Cmd → Option Nat
  | [] => none
  | c :: cs => some (encL c cs)

theorem encL_append (c : Cmd) (cs : List Cmd) (d : Cmd) (ds : List Cmd) :
    encL c (cs ++ d :: ds) = context (c :: cs) (encL d ds) := by
  induction cs generalizing c with
  | nil => rfl
  | cons c' cs ih =>
    simp only [List.cons_append, encL, context]
    rw [ih c']
    rfl

theorem listCode_context (pre : List Cmd) (c : Cmd) (cs : List Cmd) :
    listCode (pre ++ c :: cs) = some (context pre (encL c cs)) := by
  cases pre with
  | nil => rfl
  | cons p ps =>
    simp only [List.cons_append, listCode]
    rw [encL_append]

theorem swapAt_marked (pre : List Cmd) (c : Cmd) (cs : List Cmd) :
    swapAt pre.length (pre ++ c :: cs) = pre ++ swap c :: cs := by
  induction pre with
  | nil => rfl
  | cons p ps ih => simp only [List.length_cons, List.cons_append, swapAt, ih]

/-- Full numerical statement for the exact list encoding, with the marked
position retained. Both candidates are nonempty; the image is strictly
earlier in numerical enumeration. -/
theorem marked_occurrence_lower (pre suf : List Cmd) (x : Nat) :
    ∃ lower upper,
      listCode (pre ++ .nip x :: suf) = some upper ∧
      listCode (swapAt pre.length (pre ++ .nip x :: suf)) = some lower ∧
      lower < upper := by
  refine ⟨context pre (encL (.drop x) suf),
    context pre (encL (.nip x) suf), listCode_context _ _ _, ?_,
    marked_drop_earlier _ _ _⟩
  rw [swapAt_marked]
  exact listCode_context pre (.drop x) suf

theorem listCode_injective {cs ds : List Cmd} (h : listCode cs = listCode ds) : cs = ds := by
  cases cs with
  | nil => cases ds <;> simp_all [listCode]
  | cons c cs =>
    cases ds with
    | nil => simp [listCode] at h
    | cons d ds =>
      have hh : encL c cs = encL d ds := by simpa [listCode] using h
      obtain ⟨hc, hs⟩ := encL_injective c cs d ds hh
      rw [hc, hs]

/-- A marked occurrence is encoded by its candidate and position. Images of
two different marked occurrences cannot collide. This is injectivity on
occurrences, not merely on candidate numbers. -/
theorem occurrence_image_injective (cs ds : List Cmd) (i j : Nat)
    (h : (listCode (swapAt i cs), i) = (listCode (swapAt j ds), j)) :
    cs = ds ∧ i = j := by
  have hij : i = j := congrArg Prod.snd h
  subst j
  have hc := listCode_injective (congrArg Prod.fst h)
  exact ⟨swapAt_injective i hc, rfl⟩

#print axioms marked_drop_earlier
#print axioms marked_occurrence_lower
#print axioms encL_injective
#print axioms occurrence_image_injective

end CantorOccurrenceOrder
