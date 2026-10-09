import GowersSzemeredi.Proofs16BohrFourTerm
import GowersSzemeredi.Proofs16TuplePatternBridge

/-! Compatible normalized local maps respect sums of quarter-radius
representations. This controls every intermediate point in the gluing proof. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Compatibility on the full intersection controls any additive
quadruple represented in the sum of the quarter neighborhoods. -/
theorem compatible_bohr_sum_quadruple {N : Nat} [NeZero N]
    (T U : Finset (ZMod N)) (f g : ZMod N → ZMod N) {r : Real} (hr : 0 ≤ r)
    (hf : IsFreimanLinearOn (bohr T r) f) (hg : IsFreimanLinearOn (bohr U r) g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfg : ∀ z ∈ bohr T r, z ∈ bohr U r → f z = g z)
    (a b : Fin 4 → ZMod N) (ha : ∀ i, a i ∈ bohr T (r/4)) (hb : ∀ i, b i ∈ bohr U (r/4))
    (he : (a 0+b 0)+(a 1+b 1) = (a 2+b 2)+(a 3+b 3)) :
    (f (a 0)+g (b 0))+(f (a 1)+g (b 1)) =
      (f (a 2)+g (b 2))+(f (a 3)+g (b 3)) := by
  have haD := bohr_four_term_mem T (ha 0) (ha 1) (ha 2) (ha 3)
  have hbD := bohr_four_term_mem U (hb 2) (hb 3) (hb 0) (hb 1)
  have heD : a 0+a 1-a 2-a 3 = b 2+b 3-b 0-b 1 := by linear_combination he
  have hc := hfg _ haD (heD.symm ▸ hbD)
  rw [freiman_bohr_four_term T f hr hf.freimanHom hf0 (ha 0) (ha 1) (ha 2) (ha 3),
    heD,freiman_bohr_four_term U g hr hg.freimanHom hg0 (hb 2) (hb 3) (hb 0) (hb 1)] at hc
  linear_combination hc

/-- The sum value is independent of its quarter-radius representation. -/
theorem compatible_bohr_sum_value_unique {N : Nat} [NeZero N]
    (T U : Finset (ZMod N)) (f g : ZMod N → ZMod N) {r : Real} (hr : 0 ≤ r)
    (hf : IsFreimanLinearOn (bohr T r) f) (hg : IsFreimanLinearOn (bohr U r) g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfg : ∀ z ∈ bohr T r, z ∈ bohr U r → f z = g z)
    {a b c d : ZMod N} (ha : a ∈ bohr T (r/4)) (hb : b ∈ bohr U (r/4))
    (hc : c ∈ bohr T (r/4)) (hd : d ∈ bohr U (r/4)) (he : a+b = c+d) :
    f a+g b = f c+g d := by
  have h0T := zero_mem_bohr T (by positivity : 0 ≤ r/4)
  have h0U := zero_mem_bohr U (by positivity : 0 ≤ r/4)
  have h := compatible_bohr_sum_quadruple T U f g hr hf hg hf0 hg0 hfg
    ![a,0,c,0] ![b,0,d,0]
    (by intro i; fin_cases i <;> assumption)
    (by intro i; fin_cases i <;> assumption) (by simpa using he)
  simpa [hf0,hg0] using h

end LeanProofs.GowersSzemeredi
