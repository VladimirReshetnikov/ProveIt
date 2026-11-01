import ZFCinPA.CollectionResources254
import ZFCinPA.LPieces
import BusyBeaver.ZFC.KSeed222

set_option autoImplicit false

/-!
# Elliot Glazer's seed property in any model of ZF, from explicit resources

For an arbitrary relation `Q` on a model of ZF (with Foundation and power
sets), the seed property at every input follows from three resources about
`Q`: witness-rank Separation (as for Collection), a limit ordinal `β` above any
given ordinal whose elements bound the least witness ranks of all inputs from
earlier stages, and output Separation over `V_β`. The container is

`C = {y ∈ V_β | ∃ x ∈ V_β, Q x y}`.

Every subset of a member of `V_β` lies in `V_β` (`β` is a limit), so the closure
clause follows from the rank bound. No constructibility or choice is used.
-/

namespace LeanProofs.ZFCinPA.SeedResources222
open _root_.SetTheory
open _root_.SetTheory.BusyBeaver.ZFC
open InternalOrd InternalRank ZFRank
open LeanProofs.ZFCinPA.CollectionResources254
open LeanProofs.ZFCinPA.LPieces (IsLim)
universe u
variable {V : Type u} {mem : V → V → Prop}

/-- **The seed property from a rank-closed limit.** -/
theorem seed_of_closure (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) (Q : V → V → Prop)
    (hSep : ∀ x a, ∃ s, ∀ c, mem c s ↔ mem c a ∧ WitnessRank H Q x c)
    (hcl : ∀ α, Ord mem α → ∃ β, IsLim mem β ∧ mem α β ∧
      ∀ γ, mem γ β → ∀ S, IsV H γ S → ∀ x, mem x S → ∀ c, TotalRank H Q x c → mem c β)
    (hOut : ∀ S, ∃ C, ∀ y, mem y C ↔ mem y S ∧ ∃ x, mem x S ∧ Q x y)
    (A : V) : KSeed222.SeedProp mem Q A := by
  classical
  have htot := totalRank_total H hR hP Q hSep
  obtain ⟨a, Sa, ha, hSa, hASa⟩ := ranked H hR hP A
  obtain ⟨β, hβ, haβ, hcl'⟩ := hcl a ha
  obtain ⟨Sβ, hSβ⟩ := isV_exists H hR hP hβ.1
  have hsub : ∀ γ T, mem γ β → IsV H γ T → Sub mem T Sβ :=
    fun γ T hγ hT => isV_mono H hR hP hβ.1 hγ hT hSβ
  have wit : ∀ γ S x, mem γ β → IsV H γ S → mem x S → ∀ y, Q x y →
      ∃ z, Q x z ∧ mem z Sβ := by
    intro γ S x hγ hS hx y hy
    obtain ⟨c, hc, -⟩ := htot x
    have hL : LeastRank H Q x c := hc.elim id (fun h => (h.1 ⟨y, hy⟩).elim)
    have hcβ := hcl' γ hγ S hS x hx c hc
    obtain ⟨T, z, hT, hzT, hQ⟩ := hL.2.1
    exact ⟨z, hQ, hsub c T hcβ hT z hzT⟩
  obtain ⟨C, hC⟩ := hOut Sβ
  refine ⟨C, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, hzS⟩ := wit a Sa A haβ hSa hASa y hy
    exact ⟨z, hz, (hC z).2 ⟨hzS, A, hsub a Sa haβ hSa A hASa, hz⟩⟩
  · obtain ⟨hyS, x, -, hxy⟩ := (hC y).1 hy
    refine ⟨x, hxy, fun x' hsubx y' hy' => ?_⟩
    obtain ⟨γ, T, hγ, hT, hyT⟩ := (isV_spec H hR hP hβ.1 hSβ y).1 hyS
    obtain ⟨γ', hγ'β, hγγ'⟩ := hβ.2.2 γ hγ
    have hγ'o : Ord mem γ' := ord_of_mem hβ.1 hγ'β
    obtain ⟨S', hS'⟩ := isV_exists H hR hP hγ'o
    have hx'S' : mem x' S' :=
      (isV_spec H hR hP hγ'o hS' x').2 ⟨γ, T, hγγ', hT, fun w hw => hyT w (hsubx w hw)⟩
    obtain ⟨z, hz, hzS⟩ := wit γ' S' x' hγ'β hS' hx'S' y' hy'
    exact ⟨z, hz, (hC z).2 ⟨hzS, x', hsub γ' S' hγ'β hS' x' hx'S', hz⟩⟩

end LeanProofs.ZFCinPA.SeedResources222
