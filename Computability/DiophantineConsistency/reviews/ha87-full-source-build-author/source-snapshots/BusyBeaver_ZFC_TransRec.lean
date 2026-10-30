import BusyBeaver.ZFC.InternalRank

/-!
Transfinite recursion for a definable stage operation.

Given an operation `G` on the sets of a model of ZF with Foundation whose graph
is defined by a named formula, there is a unique hierarchy

    stage a = ⋃ { G (stage c) | c ∈ a }

along the internal ordinals. With `G = P` this is the cumulative hierarchy of
`InternalRank`; with `G = Def` it will be Gödel's constructible hierarchy.

It is `InternalRank`'s generic recursion with `R z T := z ∈ G T`: approximations
are sets of Kuratowski pairs obeying the recursion; they agree where both are
defined, extend by one stage, glue below every ordinal, and so exist;
`IsStage` reads the hierarchy off them.
-/

namespace SetTheory.BusyBeaver.ZFC.TransRec

open NamedZF NForm InternalOrd InternalRank

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- A definable operation: `gF y x` defines `y = G x` (output name `y`, input name `x`). -/
structure DefOp (mem : V → V → Prop) (G : V → V) where
  gF : Nat → Nat → NForm
  spec : ∀ (ρ : Nat → V) (y x : Nat), NSat mem ρ (gF y x) ↔ ρ y = G (ρ x)

variable {G : V → V}

/-- `z ∈ G t`, with a fresh witness name. -/
def inGF (D : DefOp mem G) (z t : Nat) : NForm :=
  .ex (z + t + 1) (.and (D.gF (z + t + 1) t) (.mem z (z + t + 1)))

theorem nsat_inGF (D : DefOp mem G) (ρ : Nat → V) (z t : Nat) :
    NSat mem ρ (inGF D z t) ↔ mem (ρ z) (G (ρ t)) := by
  simp only [inGF, NSat, D.spec]
  simp (disch := omega) only [upd_same, upd_other]
  constructor
  · rintro ⟨d, rfl, h⟩; exact h
  · intro h; exact ⟨_, rfl, h⟩

/-! ## The `G`-hierarchy: `InternalRank`'s recursion with `R z T := z ∈ G T` -/

/-- `f` approximates the `G`-hierarchy on the ordinal `d`. -/
def Approx (H : ZFAxioms mem) (G : V → V) (f d : V) : Prop := RApprox H (fun z T => mem z (G T)) f d

/-- `S` is the stage `a` of the `G`-hierarchy. -/
def IsStage (H : ZFAxioms mem) (G : V → V) (a S : V) : Prop := RStage H (fun z T => mem z (G T)) a S

def isStageF (D : DefOp mem G) (a S : Nat) : NForm := rstageF (inGF D) a S

theorem nsat_isStageF (H : ZFAxioms mem) (D : DefOp mem G) (ρ : Nat → V) (a S : Nat) :
    NSat mem ρ (isStageF D a S) ↔ IsStage H G (ρ a) (ρ S) :=
  nsat_rstageF H (nsat_inGF D) ρ a S

/-- Every class `G T` is a set. -/
theorem gSets : RSets mem (fun z T => mem z (G T)) := fun T => ⟨G T, fun _ => Iff.rfl⟩

section Hierarchy

variable (H : ZFAxioms mem) (hR : Regular mem) (D : DefOp mem G)
include H hR D

theorem stage_exists' {a : V} (ha : Ord mem a) : ∃ S, IsStage H G a S :=
  rstage_exists' H hR (nsat_inGF D) gSets ha

omit D in
theorem stage_unique {a S S' : V} (ha : Ord mem a) (h : IsStage H G a S) (h' : IsStage H G a S') :
    S = S' := rstage_unique H hR ha h h'

/-- **The recursion equation:** `stage a = ⋃ {G (stage c) | c ∈ a}`. -/
theorem stage_spec {a S : V} (ha : Ord mem a) (h : IsStage H G a S) :
    ∀ z, mem z S ↔ ∃ c T, mem c a ∧ IsStage H G c T ∧ mem z (G T) :=
  rstage_spec H hR (nsat_inGF D) gSets ha h

/-- Stages grow along the ordinals. -/
theorem stage_mono {a c S T : V} (ha : Ord mem a) (hc : mem c a) (hT : IsStage H G c T)
    (hS : IsStage H G a S) : Sub mem T S :=
  rstage_mono H hR (nsat_inGF D) gSets ha hc hT hS

end Hierarchy

end SetTheory.BusyBeaver.ZFC.TransRec
