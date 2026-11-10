import DiophantineConsistency.Source34.Source34Column
import DiophantineConsistency.Source34.Source34Field
import DiophantineConsistency.Source34.Source34Parity
import DiophantineConsistency.Mixed121.Mixed121FieldParity

/-! # Forward parity at the field and anchor phases, at the source34 ports

`Mixed121FieldParity` at the source34 tuple. For the constructed word, a
physical block digit is its raw column (`Source34Column.marked_physical_column`).
The halting chain's column decomposition (`Source34Field`, `Source34Parity`)
then applies to the constructed word, through `word_low_slots`:

* at `1000 + 2u` the column is the south bit `960 + 2u` (bare shift `40`)
  plus the temporal predecessor's north bit `1000 + 2u`, which are equal; the
  other bare sources `959 + 2u`, `8701 + 2u`, `7601 + 2u`, `999 + 2u` are
  outside the support;
* at `1021 + 2u` it is the east bit `980 + 2u` (bare shift `41`) plus the
  spatial predecessor's west bit `1020 + 2u` (bare shift `8802`), which are
  equal; the temporal source sits at the odd phase `1021 + 2u` and is zero;
* at `2195` and `3296` it is two anchors, each `1`.

(121x8801: windows `1013 + u` with shift `30` and `1065 + u` with shifts `62`,
`8843`.) So every such digit is even, hence carry-free against the high mask's
`1` there. The field lemmas take the window index `u` explicitly
(`vertical_fields`, `horizontal_fields`), matching `Source34HighPhase.active`.
`Mixed121FieldParity.cyc_add_mod` is generic and used directly. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Source34FieldParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking ArithmeticBinaryCarry
  CompactHeterogeneousCarry
open Mixed121Kernel (rho)
open CompactMarkedTransport CompactGenericAlignedMass Source34Kernel Source34Rotation Source34Flatten
  Mixed121Temporal Source34Cell Source34Word Source34Block Source34Column Source34Field
open Mixed121Rotation (coefficient word cap)
open Mixed121Flatten (selectors copies)
open Mixed121Column (Idx coeff aligned_digit)
open Mixed121Field (phase)
open Mixed121FieldParity (cyc_add_mod)
open Mixed121Word (one_noCarry_even)
attribute [local irreducible] paramKernel rho Compact943Data.rows Source34Ports.lowNat
  Source34Ports.highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The common setting at phase `q` of block `j` of the constructed word. -/
private theorem setting (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (q : ℕ) (hq : q<8801) :
    let C := packedWord row dummy N
    let n : V := 8801*N
    let k : V := 8801*j+(q:V)
    0<n ∧ k<n ∧ k%8801=(q:V) ∧ C<Exp.exp (121*n) ∧
    (∀ y<8801*N, 0<y → NoCarry (dig 121 C y) (dig 121 ((Source34Ports.lowNat:ℕ):V) (y%8801))) ∧
    dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) (q:V) % 2 =
      (Mixed121Parity.selectorsAt n C k 4393 + Mixed121Parity.selectorsAt n C k 5495 +
        bareColumn n C k + dig 121 C (cyc n k ((8801*s)%n))) % 2 := by
  intro C n k
  have hn : 0<n := mul_pos (by norm_num) hw.pos
  have hqV : (q:V)<8801 := by exact_mod_cast hq
  have hi := Mixed121Copy.index N j (q:V) hj hqV
  have hC : C<Exp.exp (121*n) := by
    dsimp [C,n]
    simpa only [mul_assoc] using packedWord_lt row dummy N
  have hslots : ∀ y<8801*N, 0<y →
      NoCarry (dig 121 C y) (dig 121 ((Source34Ports.lowNat:ℕ):V) (y%8801)) := by
    intro y hy _
    exact word_low_slots row dummy hw hbool y hy
  refine ⟨hn, hi.1, hi.2, hC, hslots, ?_⟩
  have hphysical := (marked_physical_column row dummy hw hN hs hbool j hj (q:V) hqV).2
  have hraw := Source34Parity.raw_mod_two n C (temporalWord n (121*(8801*s)) C) k hn hi.1 hC
  rw [hphysical]
  change raw 121 (coefficient (fun x : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies x : V)))
    (word 121 n C bandOffsets (temporalWord n (121*(8801*s)) C)) k % 2 = _
  rw [hraw, aligned_digit C n (8801*s) k hn hi.1 hC]

private theorem htwo (x : V) : (x + x) % 2 = 0 := by
  rw [show x + x = x*2 by ring, mod_mul (by norm_num : (0:V)<2), mod_self, mul_zero, zero_mod]

theorem vertical_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (u : ℕ) (hu : u<10) :
    dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j)
      ((1000+2*u:ℕ):V) % 2 = 0 := by
  obtain ⟨hn, hk, hp, hC, hslots, hcol⟩ :=
    setting row dummy hw hN hs hbool hj (1000+2*u) (by omega)
  set C := packedWord row dummy N
  set n : V := 8801*N
  set k : V := 8801*j+((1000+2*u:ℕ):V)
  obtain ⟨gsel, g41, g1100, g2200, g8802, -⟩ := vertical_geometry u hu
  obtain ⟨hs1, hs2⟩ := selectors_zero N C k (1000+2*u) hw.pos hp gsel hslots
  have hb41 := source_absent N C k (1000+2*u) 41 hw.pos hp g41 hslots
  have hb1100 := source_absent N C k (1000+2*u) 1100 hw.pos hp g1100 hslots
  have hb2200 := source_absent N C k (1000+2*u) 2200 hw.pos hp g2200 hslots
  have hb8802 := source_absent N C k (1000+2*u) 8802 hw.pos hp g8802 hslots
  rw [hcol, hs1, hs2, bare_expand n C k hn hk hC, hb41, hb1100, hb2200, hb8802]
  simp only [zero_add, add_zero]
  -- the two sources are matched bits
  have hj' : cyc N j s < N := cyc_lt hw.pos _ _
  have he : (cyc N j s+s)%N=j := by rw [cyc_add_mod hw.pos, mod_eq_self_of_lt hj]
  have hq : ((1000+2*u:ℕ):V)<8801 := by exact_mod_cast (show 1000+2*u<8801 by omega)
  have hq40 : (40:V)≤((1000+2*u:ℕ):V) := by exact_mod_cast (show 40≤1000+2*u by omega)
  have hsub : ((1000+2*u:ℕ):V)-40=((960+2*u:ℕ):V) := by
    apply (eq_tsub_of_add_eq ?_).symm
    exact_mod_cast (show (960+2*u)+40=1000+2*u by omega)
  have hleft : dig 121 C (cyc n k ((40:ℕ):V)) = dig 121 C (8801*j+((960+2*u:ℕ):V)) := by
    rw [show ((40:ℕ):V) = 40 by simp, Mixed121Copy.reflected N j _ 40 hj hq hq40, hsub]
  have hright : dig 121 C (cyc n k ((8801*s)%n)) =
      dig 121 C (8801*cyc N j s+((1000+2*u:ℕ):V)) := by
    rw [cyc_mod _ _ _ hn, Mixed121Copy.shift N j s _ hj hs hq]
  rw [hleft, hright, vertical_digits hw hj hj' he u hu]
  exact htwo _

private theorem previous (N j : V) (u : ℕ) (hu : u<10) (hN : 0<N) (hj : j<N) :
    cyc (8801*N) (8801*j+(((1021+2*u:ℕ)):V)) 8802 = 8801*(cyc N j 1)+(((1020+2*u:ℕ)):V) := by
  have hn : 0<8801*N := mul_pos (by norm_num) hN
  have hs1 : 1%N<N := mod_lt _ hN
  have hmod : (8801:V)%(8801*N)=8801*(1%N) := by
    simpa only [mul_one] using (ArithmeticModularCancellation.mul_mod_mul (k:=(8801:V)) (a:=(1:V))
      (b:=N) (by norm_num) hN)
  have hsub : (((1021+2*u:ℕ)):V) - 1 = (((1020+2*u:ℕ)):V) := by
    apply (eq_tsub_of_add_eq ?_).symm
    exact_mod_cast (show 1020+2*u+1 = 1021+2*u by omega)
  calc
    _ = cyc (8801*N) (cyc (8801*N) (8801*j+(((1021+2*u:ℕ)):V)) 1) 8801 := by
      rw [W121.TemporalSafeCyclic.cyc_nested _ _ _ _ hn]
      norm_num
    _ = cyc (8801*N) (8801*j+(((1020+2*u:ℕ)):V)) 8801 := by
      rw [Mixed121Copy.reflected N j _ 1 hj (by exact_mod_cast (show 1021+2*u<8801 by omega))
        (by exact_mod_cast (show 1≤1021+2*u by omega)), hsub]
    _ = cyc (8801*N) (8801*j+(((1020+2*u:ℕ)):V)) (8801*(1%N)) := by
      rw [←hmod,cyc_mod _ _ _ hn]
    _ = 8801*(cyc N j (1%N))+(((1020+2*u:ℕ)):V) :=
      Mixed121Copy.shift N j (1%N) _ hj hs1 (by exact_mod_cast (show 1020+2*u<8801 by omega))
    _ = _ := by rw [cyc_mod _ _ _ hN]

theorem horizontal_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (u : ℕ) (hu : u<10) :
    dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j)
      ((1021+2*u:ℕ):V) % 2 = 0 := by
  obtain ⟨hn, hk, hp, hC, hslots, hcol⟩ :=
    setting row dummy hw hN hs hbool hj (1021+2*u) (by omega)
  set C := packedWord row dummy N
  set n : V := 8801*N
  set k : V := 8801*j+((1021+2*u:ℕ):V)
  obtain ⟨gsel, g40, g1100, g2200, godd, -, -⟩ := horizontal_geometry u hu
  obtain ⟨hs1, hs2⟩ := selectors_zero N C k (1021+2*u) hw.pos hp gsel hslots
  have hb40 := source_absent N C k (1021+2*u) 40 hw.pos hp g40 hslots
  have hb1100 := source_absent N C k (1021+2*u) 1100 hw.pos hp g1100 hslots
  have hb2200 := source_absent N C k (1021+2*u) 2200 hw.pos hp g2200 hslots
  have hq : ((1021+2*u:ℕ):V)<8801 := by exact_mod_cast (show 1021+2*u<8801 by omega)
  have htemp : dig 121 C (cyc n k ((8801*s)%n)) = 0 := by
    rw [cyc_mod _ _ _ hn, Mixed121Copy.shift N j s _ hj hs hq]
    have hj' : cyc N j s < N := cyc_lt hw.pos _ _
    have hi' := Mixed121Copy.index N (cyc N j s) _ hj' hq
    exact zero_absent N C _ (1021+2*u) (by omega) hi'.1 hi'.2 godd hslots
  rw [hcol, hs1, hs2, bare_expand n C k hn hk hC, hb40, hb1100, hb2200, htemp]
  simp only [zero_add, add_zero]
  have hj' : cyc N j 1 < N := cyc_lt hw.pos _ _
  have he : (cyc N j 1+1)%N=j := by rw [cyc_add_mod hw.pos, mod_eq_self_of_lt hj]
  have hq41 : (41:V)≤((1021+2*u:ℕ):V) := by exact_mod_cast (show 41≤1021+2*u by omega)
  have hsub : ((1021+2*u:ℕ):V)-41=((980+2*u:ℕ):V) := by
    apply (eq_tsub_of_add_eq ?_).symm
    exact_mod_cast (show (980+2*u)+41=1021+2*u by omega)
  have hleft : dig 121 C (cyc n k ((41:ℕ):V)) = dig 121 C (8801*j+((980+2*u:ℕ):V)) := by
    rw [show ((41:ℕ):V) = 41 by simp, Mixed121Copy.reflected N j _ 41 hj hq hq41, hsub]
  have hright : dig 121 C (cyc n k ((8802:ℕ):V)) =
      dig 121 C (8801*cyc N j 1+((1020+2*u:ℕ):V)) := by
    rw [show ((8802:ℕ):V) = 8802 by simp, previous N j u hu hw.pos hj]
  rw [hleft, hright, horizontal_digits hw hj hj' he u hu]
  exact htwo _

/-- The anchor columns: two anchors, each `1`. -/
private theorem anchor_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (t b a : ℕ)
    (ht : t = 2195 ∨ t = 3296) (hab : a + b = t) (ha : a = 1095 ∨ a = 1096)
    (hbare : (b = 1100 ∧ ¬InSupp (phase t 2200)) ∨ (b = 2200 ∧ ¬InSupp (phase t 1100)))
    (h40 : ¬InSupp (phase t 40)) (h41 : ¬InSupp (phase t 41)) (h8802 : ¬InSupp (phase t 8802))
    (hsel : ∀ j<943, ¬InSupp (phase t (4393-j)) ∧ ¬InSupp (phase t (5495-j))) :
    dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) (t:V) % 2 = 0 := by
  obtain ⟨hn, hk, hp, hC, hslots, hcol⟩ := setting row dummy hw hN hs hbool hj t (by omega)
  set C := packedWord row dummy N
  set n : V := 8801*N
  set k : V := 8801*j+(t:V)
  obtain ⟨hs1, hs2⟩ := selectors_zero N C k t hw.pos hp hsel hslots
  have hb40 := source_absent N C k t 40 hw.pos hp h40 hslots
  have hb41 := source_absent N C k t 41 hw.pos hp h41 hslots
  have hb8802 := source_absent N C k t 8802 hw.pos hp h8802 hslots
  have htq : (t:V)<8801 := by exact_mod_cast (show t<8801 by omega)
  have hanchor : dig 121 C (cyc n k (b:V)) = 1 := by
    have hbt : (b:V)≤(t:V) := by exact_mod_cast (show b≤t by omega)
    have hsub : (t:V)-(b:V) = (a:V) := by
      apply (eq_tsub_of_add_eq ?_).symm
      exact_mod_cast hab
    rw [Mixed121Copy.reflected N j _ _ hj htq hbt, hsub]
    exact word_anchor row dummy N j hj a (by omega)
  have htemp : dig 121 C (cyc n k ((8801*s)%n)) = 1 := by
    rw [cyc_mod _ _ _ hn, Mixed121Copy.shift N j s _ hj hs htq]
    exact word_anchor row dummy N _ (cyc_lt hw.pos _ _) t (by omega)
  rw [hcol, hs1, hs2, bare_expand n C k hn hk hC, hb40, hb41, hb8802, htemp]
  rcases hbare with ⟨rfl, hother⟩ | ⟨rfl, hother⟩
  · have hz := source_absent N C k t 2200 hw.pos hp hother hslots
    rw [hz, hanchor]; norm_num
  · have hz := source_absent N C k t 1100 hw.pos hp hother hslots
    rw [hz, hanchor]; norm_num

theorem phase2195_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) :
    dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) 2195 % 2 = 0 := by
  have h := anchor_even row dummy hw hN hs hbool hj 2195 1100 1095 (Or.inl rfl) rfl (Or.inl rfl)
    (Or.inl ⟨rfl, by norm_num [phase, InSupp]⟩) (by norm_num [phase, InSupp])
    (by norm_num [phase, InSupp]) (by norm_num [phase, InSupp])
    (fun j hj => ⟨not_insupp _ (by unfold phase; omega), not_insupp _ (by unfold phase; omega)⟩)
  simpa only [Nat.cast_ofNat] using h

theorem phase3296_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) :
    dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) 3296 % 2 = 0 := by
  have h := anchor_even row dummy hw hN hs hbool hj 3296 2200 1096 (Or.inr rfl) rfl (Or.inr rfl)
    (Or.inr ⟨rfl, by norm_num [phase, InSupp]⟩) (by norm_num [phase, InSupp])
    (by norm_num [phase, InSupp]) (by norm_num [phase, InSupp])
    (fun j hj => ⟨not_insupp _ (by unfold phase; omega), not_insupp _ (by unfold phase; omega)⟩)
  simpa only [Nat.cast_ofNat] using h

/-! ## High-mask no-carry at the field and anchor phases -/

private theorem even_noCarry_one (x : V) (h : x%2=0) : NoCarry x 1 :=
  (noCarry_comm _ _).2 (one_noCarry_even x h)

theorem vertical_fields (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (u : ℕ) (hu : u<10) :
    NoCarry (dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j)
        ((1000+2*u:ℕ):V))
      (dig 121 ((Source34Ports.highNat : ℕ) : V) ((1000+2*u:ℕ):V)) := by
  rw [Source34Parity.model_high _ (high_vertical u hu)]
  exact even_noCarry_one _ (vertical_even row dummy hw hN hs hbool hj u hu)

theorem horizontal_fields (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (u : ℕ) (hu : u<10) :
    NoCarry (dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j)
        ((1021+2*u:ℕ):V))
      (dig 121 ((Source34Ports.highNat : ℕ) : V) ((1021+2*u:ℕ):V)) := by
  rw [Source34Parity.model_high _ (high_horizontal u hu)]
  exact even_noCarry_one _ (horizontal_even row dummy hw hN hs hbool hj u hu)

theorem phase2195_noCarry (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) :
    NoCarry (dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) 2195)
      (dig 121 ((Source34Ports.highNat : ℕ) : V) 2195) := by
  have h := Source34Parity.model_high (V:=V) 2195 Source34Parity.high2195
  simp only [Nat.cast_ofNat] at h
  rw [h]
  exact even_noCarry_one _ (phase2195_even row dummy hw hN hs hbool hj)

theorem phase3296_noCarry (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) :
    NoCarry (dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) 3296)
      (dig 121 ((Source34Ports.highNat : ℕ) : V) 3296) := by
  have h := Source34Parity.model_high (V:=V) 3296 Source34Parity.high3296
  simp only [Nat.cast_ofNat] at h
  rw [h]
  exact even_noCarry_one _ (phase3296_even row dummy hw hN hs hbool hj)

#print axioms Source34FieldParity.vertical_even
#print axioms Source34FieldParity.horizontal_even
#print axioms Source34FieldParity.phase2195_even
#print axioms Source34FieldParity.phase3296_even
#print axioms Source34FieldParity.vertical_fields
#print axioms Source34FieldParity.horizontal_fields
#print axioms Source34FieldParity.phase2195_noCarry
#print axioms Source34FieldParity.phase3296_noCarry
end Source34FieldParity
