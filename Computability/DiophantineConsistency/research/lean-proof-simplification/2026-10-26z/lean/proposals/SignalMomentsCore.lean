/- DESIGN PROTOTYPE: not certified as compiling in this packet.
   See ../../validation/manifest.json and report.pdf for exact scope. -/
import DiophantineConsistency.WangTiles942Core

namespace NewArithmetic
open DiophantineConsistency.WangTiles942

/-- The existing signal constructor, with its target list exposed as a parameter. -/
def signalRowsOn (d : Bool) (qs : List ℕ) : List (ℕ × Tile) :=
  qs.flatMap (fun q => (List.range 2).map (fun b =>
    (423+2*rail d q+b, ⟨d.toNat*rail d q,b,(1-d.toNat)*rail d q,headColor q b⟩)))

theorem signal_pair_mass (d : Bool) (q : ℕ) :
    ((List.range 2).map (fun b => selectorWeight
      ⟨d.toNat*rail d q,b,(1-d.toNat)*rail d q,headColor q b⟩)).sum =
      171798956034 + 137438953472 * q +
      (if d then 2048 else 268435456) * rail d q := by
  cases d <;> simp [List.range_succ, selectorWeight, headColor] <;> omega

theorem signal_mass_formula (d : Bool) (qs : List ℕ) :
    ((signalRowsOn d qs).map (fun row => selectorWeight row.2)).sum =
      171798956034 * qs.length + 137438953472 * qs.sum +
      (if d then 2048 else 268435456) * (qs.map (rail d)).sum := by
  induction qs with
  | nil => simp [signalRowsOn]
  | cons q qs ih =>
    simp only [signalRowsOn, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_map] at *
    rw [signal_pair_mass, ih]
    simp only [List.length_cons, List.sum_cons, List.map_cons]
    ring

#print axioms signal_pair_mass
#print axioms signal_mass_formula
end NewArithmetic
