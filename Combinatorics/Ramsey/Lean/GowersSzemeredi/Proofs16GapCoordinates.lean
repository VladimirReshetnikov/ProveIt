import GowersSzemeredi.Proofs16BilinearBohrVariety

/-! Freiman-linear maps on generalized progressions are affine in the
coordinates.

Let `P n = a + Σ i, n i • g i` for `n` in the box `∏ i, [0, Lens i)`. If `L`
is Freiman-linear on a set containing all these points, then

`L (P n) = L (P 0) + Σ i, n i * (L (P (eᵢ)) − L (P 0))`.

Research notes J.2 need this off the origin. A Bohr set is essentially a
proper generalized progression, and a Freiman-linear map on it is affine
in the progression's coordinates, not in the ambient variable; Dirichlet
is then applied per coordinate. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The point of a generalized progression with base `a`, generators `g`
and coordinates `n`. -/
def gapPoint {N m : Nat} (a : ZMod N) (g : Fin m → ZMod N) (n : Fin m → Nat) : ZMod N :=
  a + ∑ i, (n i : ZMod N) * g i

theorem gapPoint_zero {N m : Nat} (a : ZMod N) (g : Fin m → ZMod N) :
    gapPoint a g 0 = a := by
  simp [gapPoint]

theorem gapPoint_single {N m : Nat} (a : ZMod N) (g : Fin m → ZMod N) (j : Fin m) (t : Nat) :
    gapPoint a g (Pi.single j t) = a + (t : ZMod N) * g j := by
  unfold gapPoint
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [Pi.single_apply, hij]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Splitting off coordinate `j`. -/
theorem gapPoint_split {N m : Nat} (a : ZMod N) (g : Fin m → ZMod N) (n : Fin m → Nat) (j : Fin m) :
    gapPoint a g n + gapPoint a g 0 =
      gapPoint a g (Function.update n j 0) + gapPoint a g (Pi.single j (n j)) := by
  rw [gapPoint_zero, gapPoint_single]
  unfold gapPoint
  have h : ∑ i, (n i : ZMod N) * g i =
      ∑ i, ((Function.update n j 0 i : Nat) : ZMod N) * g i + (n j : ZMod N) * g j := by
    have hpt : ∀ i, (n i : ZMod N) * g i =
        ((Function.update n j 0 i : Nat) : ZMod N) * g i +
          (((Pi.single j (n j) : Fin m → Nat) i : Nat) : ZMod N) * g i := by
      intro i
      by_cases hij : i = j
      · subst hij; simp
      · simp [Function.update_of_ne hij, Pi.single_apply, hij]
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [Pi.single_apply, hij]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [h]
  ring

/-- **Coordinate affinity.** -/
theorem freiman_linear_gap_affine {N m : Nat} {S : Finset (ZMod N)} {L : ZMod N → ZMod N}
    (hL : IsFreimanLinearOn S L) (a : ZMod N) (g : Fin m → ZMod N) (Lens : Fin m → Nat)
    (hpos : ∀ i, 0 < Lens i)
    (hS : ∀ n : Fin m → Nat, (∀ i, n i < Lens i) → gapPoint a g n ∈ S) :
    ∀ n : Fin m → Nat, (∀ i, n i < Lens i) →
      L (gapPoint a g n) = L a + ∑ i, (n i : ZMod N) * (L (a + g i) - L a) := by
  -- one coordinate at a time
  have hline : ∀ (j : Fin m) (t : Nat), t < Lens j →
      L (gapPoint a g (Pi.single j t)) = L a + (t : ZMod N) * (L (a + g j) - L a) := by
    intro j t ht
    have hin : ∀ s, s < Lens j → gapPoint a g (Pi.single j s) ∈ S := by
      intro s hs
      apply hS
      intro i
      by_cases hij : i = j
      · subst hij; simpa using hs
      · simp [Pi.single_apply, hij, hpos i]
    have h := affine_of_second_difference (fun s => L (gapPoint a g (Pi.single j s))) (Lens j)
      (fun s hs => by
        have hq := hL (gapPoint a g (Pi.single j (s + 2))) (gapPoint a g (Pi.single j s))
          (gapPoint a g (Pi.single j (s + 1))) (gapPoint a g (Pi.single j (s + 1)))
          (hin _ hs) (hin _ (by omega)) (hin _ (by omega)) (hin _ (by omega))
          (by simp only [gapPoint_single]; push_cast; ring)
        show L (gapPoint a g (Pi.single j (s + 2))) - L (gapPoint a g (Pi.single j (s + 1))) =
          L (gapPoint a g (Pi.single j (s + 1))) - L (gapPoint a g (Pi.single j s))
        linear_combination hq) t ht
    simp only [nsmul_eq_mul] at h
    rw [h]
    simp [gapPoint_single, gapPoint_zero]
  -- induction over the set of active coordinates
  have hmain : ∀ (s : Finset (Fin m)) (n : Fin m → Nat), (∀ i, n i < Lens i) →
      (∀ i, i ∉ s → n i = 0) →
      L (gapPoint a g n) = L a + ∑ i ∈ s, (n i : ZMod N) * (L (a + g i) - L a) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro n _ hn
      have : n = 0 := funext fun i => hn i (Finset.notMem_empty i)
      subst this
      simp [gapPoint_zero]
    | insert j s hjs ih =>
      intro n hn hsupp
      set n' := Function.update n j 0
      have hn' : ∀ i, n' i < Lens i := by
        intro i
        by_cases hij : i = j
        · subst hij; simp [n', hpos i]
        · simp [n', Function.update_of_ne hij, hn i]
      have hsupp' : ∀ i, i ∉ s → n' i = 0 := by
        intro i hi
        by_cases hij : i = j
        · subst hij; simp [n']
        · simp only [n', Function.update_of_ne hij]
          exact hsupp i (by simp [hij, hi])
      have hq := hL (gapPoint a g n) (gapPoint a g 0) (gapPoint a g n')
        (gapPoint a g (Pi.single j (n j)))
        (hS n hn) (hS 0 (fun i => hpos i)) (hS n' hn')
        (hS _ (by
          intro i
          by_cases hij : i = j
          · subst hij; simpa using hn i
          · simp [Pi.single_apply, hij, hpos i]))
        (gapPoint_split a g n j)
      rw [gapPoint_zero] at hq
      have hIH := ih n' hn' hsupp'
      have hlin := hline j (n j) (hn j)
      rw [Finset.sum_insert hjs]
      have hsame : ∑ i ∈ s, (n' i : ZMod N) * (L (a + g i) - L a) =
          ∑ i ∈ s, (n i : ZMod N) * (L (a + g i) - L a) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hij : i ≠ j := fun h => hjs (h ▸ hi)
        simp [n', Function.update_of_ne hij]
      rw [hsame] at hIH
      linear_combination hq + hIH + hlin
  intro n hn
  simpa using hmain Finset.univ n hn (fun i hi => absurd (Finset.mem_univ i) hi)

end LeanProofs.GowersSzemeredi
