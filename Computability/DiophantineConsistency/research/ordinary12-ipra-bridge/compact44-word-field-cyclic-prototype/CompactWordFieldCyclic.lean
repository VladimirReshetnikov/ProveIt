import CompactWordFieldDigits
import DiophantineConsistency.HorizontalFieldBits

/-! Matched source digits at the exact cyclic field-column offsets. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactWordFieldCyclic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
open CompactMarkedTransport CompactConstructedWord CompactWordFieldDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem mod_add_mod' {n : V} (hn : 0<n) (x y : V) : (x%n+y)%n=(x+y)%n := by
  rw [mod_add hn, mod_eq_self_of_lt (mod_lt x hn), ← mod_add hn]
private theorem cyc_add_mod {n : V} (hn : 0<n) (k e : V) : (cyc n k e+e)%n=k%n := by
  unfold cyc
  rw [mod_add_mod' hn]
  have hle : e%n≤k+n := le_trans (le_of_lt (mod_lt e hn)) le_add_self
  have he : k+n-e%n+e=(k+n)+n*(e/n) := by
    calc
      _ = k+n-e%n+(n*(e/n)+e%n) := by rw [div_add_mod]
      _ = (k+n-e%n+e%n)+n*(e/n) := by ring
      _ = _ := by rw [tsub_add_cancel_of_le hle]
  rw [he,mod_add_mul' _ _ hn,mod_add_remove_right hn]

/-- The bare shift 30 and whole-cell shift `8807*s` select matched bits
    at each vertical field phase. -/
theorem vertical_sources {row dummy : V → V} [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hj : j<N) (hs : s<N) (u : ℕ) (hu : u<9) :
    dig 67 (packedWord row dummy N) (cyc (8807*N) (8807*j+((1013+u:ℕ):V)) 30) =
      dig 67 (packedWord row dummy N) (cyc (8807*N) (8807*j+((1013+u:ℕ):V)) (8807*s)) := by
  have hj' : cyc N j s < N := cyc_lt hw.pos _ _
  have he : (cyc N j s+s)%N=j := by rw [cyc_add_mod hw.pos, mod_eq_self_of_lt hj]
  have hb := vertical_digits hw hj hj' he u hu (dummy:=dummy)
  have hsub : ((1013+u:ℕ):V)-30=((983+u:ℕ):V) := by
    apply (eq_tsub_of_add_eq ?_).symm
    exact_mod_cast (show (983+u)+30=1013+u by omega)
  have hq : ((1013+u:ℕ):V)<8807 := by exact_mod_cast (show 1013+u<8807 by omega)
  have hq30 : (30:V)≤((1013+u:ℕ):V) := by exact_mod_cast (show 30≤1013+u by omega)
  rw [BlockCyclicIndex.reflected N j _ 30 hj hq hq30, hsub,
    BlockCyclicIndex.shift N j s _ hj hs hq]
  exact hb

/-- The bare shifts 62 and 8849 select matched bits at each horizontal
    field phase, including the cyclic predecessor cell. -/
theorem horizontal_sources {row dummy : V → V} [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hj : j<N) (u : ℕ) (hu : u<8) :
    dig 67 (packedWord row dummy N) (cyc (8807*N) (8807*j+((1065+u:ℕ):V)) 62) =
      dig 67 (packedWord row dummy N) (cyc (8807*N) (8807*j+((1065+u:ℕ):V)) 8849) := by
  have hj' : cyc N j 1 < N := cyc_lt hw.pos _ _
  have he : (cyc N j 1+1)%N=j := by rw [cyc_add_mod hw.pos, mod_eq_self_of_lt hj]
  have hb := horizontal_digits hw hj hj' he u hu (dummy:=dummy)
  have hsub : ((1065+u:ℕ):V)-62=((1003+u:ℕ):V) := by
    apply (eq_tsub_of_add_eq ?_).symm
    exact_mod_cast (show (1003+u)+62=1065+u by omega)
  have hq : ((1065+u:ℕ):V)<8807 := by exact_mod_cast (show 1065+u<8807 by omega)
  have hq62 : (62:V)≤((1065+u:ℕ):V) := by exact_mod_cast (show 62≤1065+u by omega)
  rw [BlockCyclicIndex.reflected N j _ 62 hj hq hq62, hsub,
    HorizontalFieldBits.previous N j u hu hw.pos hj]
  exact hb

#print axioms CompactWordFieldCyclic.vertical_sources
#print axioms CompactWordFieldCyclic.horizontal_sources
end CompactWordFieldCyclic
