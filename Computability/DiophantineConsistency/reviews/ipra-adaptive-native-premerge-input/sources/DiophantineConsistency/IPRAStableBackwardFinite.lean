import DiophantineConsistency.IPRAStableBackwardReach
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace DiophantineConsistency.IPRAStableBackwardFinite
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting DiophantineConsistency.IPRAStableBackwardReach
open DiophantineConsistency.IPRAStableBackward DiophantineConsistency.IPRANativeFormula
variable {L : Language}

def reachList : Proposition L → List (Proposition L)
  | φ ⋏ ψ => (φ ⋏ ψ) :: (reachList φ ++ reachList ψ)
  | φ ⋎ ψ => (φ ⋎ ψ) :: (reachList φ ++ reachList ψ)
  | ∀⁰ φ => (∀⁰ φ) :: reachList (free φ)
  | ∃⁰ φ => (∃⁰ φ) :: reachList (free φ)
  | φ => [φ]
  termination_by φ => φ.complexity

theorem mem_self (φ : Proposition L) : φ ∈ reachList φ := by
  cases φ <;> simp [reachList] <;> exact Or.inl rfl

theorem reachListClosed {root ψ : Proposition L} (h : Reach root ψ) :
    ∀ χ, χ ∈ reachList ψ → χ ∈ reachList root := by
  induction h with
  | self => exact fun _ h => h
  | @andLeft φ ψ _ ih | @andRight φ ψ _ ih | @orLeft φ ψ _ ih | @orRight φ ψ _ ih =>
    intro χ hχ
    apply ih
    first
    | change χ ∈ reachList (Semiformula.and φ ψ)
    | change χ ∈ reachList (Semiformula.or φ ψ)
    rw [reachList]
    simp [hχ]
  | @allFree φ _ ih | @exsFree φ _ ih =>
    intro χ hχ
    apply ih
    first
    | change χ ∈ reachList (Semiformula.all φ)
    | change χ ∈ reachList (Semiformula.exs φ)
    rw [reachList]
    exact List.mem_cons_of_mem _ hχ

theorem reachMem {root ψ : Proposition L} (h : Reach root ψ) : ψ ∈ reachList root :=
  reachListClosed h ψ (mem_self ψ)
noncomputable def backwardFromList [L.DecidableEq] {Λ : Hilbertᵢ L} (root : Proposition L)
    (stable : ∀ ψ, ψ ∈ reachList root → NeedsStability ψ → Λ ⊢! ∼∼native ψ 🡒 native ψ) :
    Λ ⊢! rootᴺ 🡒 native root :=
  nativeBackwardReach root (fun ψ hreach hneed => stable ψ (reachMem hreach) hneed)
end DiophantineConsistency.IPRAStableBackwardFinite
