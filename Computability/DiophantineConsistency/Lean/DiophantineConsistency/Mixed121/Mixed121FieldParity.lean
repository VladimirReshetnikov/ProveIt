import DiophantineConsistency.Mixed121.Mixed121Column
import DiophantineConsistency.Mixed121.Mixed121Field
import DiophantineConsistency.Mixed121.Mixed121Parity

/-! # Forward parity at the field and anchor phases, at 121x8801

The 121x8801 counterpart of Compact44's `CompactWordFieldCyclic`,
`CompactWordPhysicalFieldParity`, `CompactWordHorizontalParity`,
`CompactWordAnchorParity`, `CompactWordFieldHigh` and `CompactWordAnchorHigh`.
Compact44's marker-phase module `CompactWordMarkerParity` has no counterpart.
Its fields have eight or nine ordinary bits plus a marker phase, while here
all ten bits of each window are uniform: bit 9 of `label + 512` is `1` on
both sides.

For the constructed word, a physical block digit is its raw column
(`Mixed121Column.marked_physical_column`). The halting chain's column
decomposition (`Mixed121Field`, `Mixed121Parity`) then applies to the
constructed word, through `word_low_slots`:

* at `1013 + u` the column is the south bit `983 + u` (bare shift `30`) plus
  the temporal predecessor's north bit, which are equal;
* at `1065 + u` it is the east bit `1003 + u` (bare shift `62`) plus the
  spatial predecessor's west bit (bare shift `8843`), which are equal;
* at `2195` and `3296` it is two anchors, each `1`.

So every such digit is even, hence carry-free against the high mask's `1`
there. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Mixed121FieldParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking ArithmeticBinaryCarry
  CompactHeterogeneousCarry
open CompactMarkedTransport CompactGenericAlignedMass Mixed121Kernel Mixed121Rotation Mixed121Flatten Mixed121Temporal
  Mixed121Cell Mixed121Word Mixed121Block Mixed121Column Mixed121Field
attribute [local irreducible] paramKernel rho Compact943Data.rows Mixed121Ports.lowNat
  Mixed121Ports.highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem mod_add_mod' {n : V} (hn : 0<n) (x y : V) : (x%n+y)%n=(x+y)%n := by
  rw [mod_add hn, mod_eq_self_of_lt (mod_lt x hn), ← mod_add hn]

theorem cyc_add_mod {n : V} (hn : 0<n) (k e : V) : (cyc n k e+e)%n=k%n := by
  unfold cyc
  rw [mod_add_mod' hn]
  have hle : e%n≤k+n := le_trans (le_of_lt (mod_lt e hn)) le_add_self
  have he : k+n-e%n+e=(k+n)+n*(e/n) := by
    calc
      _ = k+n-e%n+(n*(e/n)+e%n) := by rw [div_add_mod]
      _ = (k+n-e%n+e%n)+n*(e/n) := by ring
      _ = _ := by rw [tsub_add_cancel_of_le hle]
  rw [he,mod_add_mul' _ _ hn,mod_add_remove_right hn]

/-- The common setting at phase `q` of block `j` of the constructed word. -/
private theorem setting (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (q : ℕ) (hq : q<8801) :
    let C := packedWord row dummy N
    let n : V := 8801*N
    let k : V := 8801*j+(q:V)
    0<n ∧ k<n ∧ k%8801=(q:V) ∧ C<Exp.exp (121*n) ∧
    (∀ y<8801*N, 0<y → NoCarry (dig 121 C y) (dig 121 ((Mixed121Ports.lowNat:ℕ):V) (y%8801))) ∧
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
      NoCarry (dig 121 C y) (dig 121 ((Mixed121Ports.lowNat:ℕ):V) (y%8801)) := by
    intro y hy _
    exact word_low_slots row dummy hw hbool y hy
  refine ⟨hn, hi.1, hi.2, hC, hslots, ?_⟩
  have hphysical := (marked_physical_column row dummy hw hN hs hbool j hj (q:V) hqV).2
  have hraw := Mixed121Parity.raw_mod_two n C (temporalWord n (121*(8801*s)) C) k hn hi.1 hC
  rw [hphysical]
  change raw 121 (coefficient (fun x : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies x : V)))
    (word 121 n C bandOffsets (temporalWord n (121*(8801*s)) C)) k % 2 = _
  rw [hraw, aligned_digit C n (8801*s) k hn hi.1 hC]

theorem vertical_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (u : ℕ) (hu : u<10) :
    dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j)
      ((1013+u:ℕ):V) % 2 = 0 := by
  obtain ⟨hn, hk, hp, hC, hslots, hcol⟩ :=
    setting row dummy hw hN hs hbool hj (1013+u) (by omega)
  set C := packedWord row dummy N
  set n : V := 8801*N
  set k : V := 8801*j+((1013+u:ℕ):V)
  obtain ⟨hs1, hs2⟩ := selectors_zero N C k (1013+u) hw.pos hp
    (fun j hj => by constructor <;> (unfold phase InSupp; omega)) hslots
  have hb62 := source_absent N C k (1013+u) 62 hw.pos hp (by unfold phase InSupp; omega) hslots
  have hb1100 := source_absent N C k (1013+u) 1100 hw.pos hp (by unfold phase InSupp; omega) hslots
  have hb2200 := source_absent N C k (1013+u) 2200 hw.pos hp (by unfold phase InSupp; omega) hslots
  have hb8843 := source_absent N C k (1013+u) 8843 hw.pos hp (by unfold phase InSupp; omega) hslots
  rw [hcol, hs1, hs2, bare_expand n C k hn hk hC, hb62, hb1100, hb2200, hb8843]
  simp only [zero_add, add_zero]
  -- the two sources are matched bits
  have hj' : cyc N j s < N := cyc_lt hw.pos _ _
  have he : (cyc N j s+s)%N=j := by rw [cyc_add_mod hw.pos, mod_eq_self_of_lt hj]
  have hq : ((1013+u:ℕ):V)<8801 := by exact_mod_cast (show 1013+u<8801 by omega)
  have hq30 : (30:V)≤((1013+u:ℕ):V) := by exact_mod_cast (show 30≤1013+u by omega)
  have hsub : ((1013+u:ℕ):V)-30=((983+u:ℕ):V) := by
    apply (eq_tsub_of_add_eq ?_).symm
    exact_mod_cast (show (983+u)+30=1013+u by omega)
  have hleft : dig 121 C (cyc n k ((30:ℕ):V)) = dig 121 C (8801*j+((983+u:ℕ):V)) := by
    rw [show ((30:ℕ):V) = 30 by simp, Mixed121Copy.reflected N j _ 30 hj hq hq30, hsub]
  have hright : dig 121 C (cyc n k ((8801*s)%n)) = dig 121 C (8801*cyc N j s+((1013+u:ℕ):V)) := by
    rw [cyc_mod _ _ _ hn, Mixed121Copy.shift N j s _ hj hs hq]
  rw [hleft, hright, vertical_digits hw hj hj' he u hu]
  have htwo : ∀ x : V, (x + x) % 2 = 0 := by
    intro x
    rw [show x + x = x*2 by ring, mod_mul (by norm_num : (0:V)<2), mod_self, mul_zero, zero_mod]
  exact htwo _

private theorem previous (N j : V) (u : ℕ) (hu : u<10) (hN : 0<N) (hj : j<N) :
    cyc (8801*N) (8801*j+(((1065+u:ℕ)):V)) 8843 = 8801*(cyc N j 1)+(((1023+u:ℕ)):V) := by
  have hn : 0<8801*N := mul_pos (by norm_num) hN
  have hs1 : 1%N<N := mod_lt _ hN
  have hmod : (8801:V)%(8801*N)=8801*(1%N) := by
    simpa only [mul_one] using (ArithmeticModularCancellation.mul_mod_mul (k:=(8801:V)) (a:=(1:V))
      (b:=N) (by norm_num) hN)
  have hsub : (((1065+u:ℕ)):V) - 42 = (((1023+u:ℕ)):V) := by
    apply (eq_tsub_of_add_eq ?_).symm
    exact_mod_cast (show 1023+u+42 = 1065+u by omega)
  calc
    _ = cyc (8801*N) (cyc (8801*N) (8801*j+(((1065+u:ℕ)):V)) 42) 8801 := by
      rw [W121.TemporalSafeCyclic.cyc_nested _ _ _ _ hn]
      norm_num
    _ = cyc (8801*N) (8801*j+(((1023+u:ℕ)):V)) 8801 := by
      rw [Mixed121Copy.reflected N j _ 42 hj (by exact_mod_cast (show 1065+u<8801 by omega))
        (by exact_mod_cast (show 42≤1065+u by omega)), hsub]
    _ = cyc (8801*N) (8801*j+(((1023+u:ℕ)):V)) (8801*(1%N)) := by
      rw [←hmod,cyc_mod _ _ _ hn]
    _ = 8801*(cyc N j (1%N))+(((1023+u:ℕ)):V) :=
      Mixed121Copy.shift N j (1%N) _ hj hs1 (by exact_mod_cast (show 1023+u<8801 by omega))
    _ = _ := by rw [cyc_mod _ _ _ hN]

theorem horizontal_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (u : ℕ) (hu : u<10) :
    dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j)
      ((1065+u:ℕ):V) % 2 = 0 := by
  obtain ⟨hn, hk, hp, hC, hslots, hcol⟩ :=
    setting row dummy hw hN hs hbool hj (1065+u) (by omega)
  set C := packedWord row dummy N
  set n : V := 8801*N
  set k : V := 8801*j+((1065+u:ℕ):V)
  obtain ⟨hs1, hs2⟩ := selectors_zero N C k (1065+u) hw.pos hp
    (fun j hj => by constructor <;> (unfold phase InSupp; omega)) hslots
  have hb30 := source_absent N C k (1065+u) 30 hw.pos hp (by unfold phase InSupp; omega) hslots
  have hb1100 := source_absent N C k (1065+u) 1100 hw.pos hp (by unfold phase InSupp; omega) hslots
  have hb2200 := source_absent N C k (1065+u) 2200 hw.pos hp (by unfold phase InSupp; omega) hslots
  have hq : ((1065+u:ℕ):V)<8801 := by exact_mod_cast (show 1065+u<8801 by omega)
  have htemp : dig 121 C (cyc n k ((8801*s)%n)) = 0 := by
    rw [cyc_mod _ _ _ hn, Mixed121Copy.shift N j s _ hj hs hq]
    have hj' : cyc N j s < N := cyc_lt hw.pos _ _
    have hi' := Mixed121Copy.index N (cyc N j s) _ hj' hq
    exact zero_absent N C _ (1065+u) (by omega) hi'.1 hi'.2 (by unfold InSupp; omega) hslots
  rw [hcol, hs1, hs2, bare_expand n C k hn hk hC, hb30, hb1100, hb2200, htemp]
  simp only [zero_add, add_zero]
  have hj' : cyc N j 1 < N := cyc_lt hw.pos _ _
  have he : (cyc N j 1+1)%N=j := by rw [cyc_add_mod hw.pos, mod_eq_self_of_lt hj]
  have hq62 : (62:V)≤((1065+u:ℕ):V) := by exact_mod_cast (show 62≤1065+u by omega)
  have hsub : ((1065+u:ℕ):V)-62=((1003+u:ℕ):V) := by
    apply (eq_tsub_of_add_eq ?_).symm
    exact_mod_cast (show (1003+u)+62=1065+u by omega)
  have hleft : dig 121 C (cyc n k ((62:ℕ):V)) = dig 121 C (8801*j+((1003+u:ℕ):V)) := by
    rw [show ((62:ℕ):V) = 62 by simp, Mixed121Copy.reflected N j _ 62 hj hq hq62, hsub]
  have hright : dig 121 C (cyc n k ((8843:ℕ):V)) = dig 121 C (8801*cyc N j 1+((1023+u:ℕ):V)) := by
    rw [show ((8843:ℕ):V) = 8843 by simp, previous N j u hu hw.pos hj]
  rw [hleft, hright, horizontal_digits hw hj hj' he u hu]
  have htwo : ∀ x : V, (x + x) % 2 = 0 := by
    intro x
    rw [show x + x = x*2 by ring, mod_mul (by norm_num : (0:V)<2), mod_self, mul_zero, zero_mod]
  exact htwo _

/-- The anchor columns: two anchors, each `1`. -/
private theorem anchor_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (t b a : ℕ)
    (ht : t = 2195 ∨ t = 3296) (hab : a + b = t) (ha : a = 1095 ∨ a = 1096)
    (hbare : (b = 1100 ∧ ¬InSupp (phase t 2200)) ∨ (b = 2200 ∧ ¬InSupp (phase t 1100)))
    (h30 : ¬InSupp (phase t 30)) (h62 : ¬InSupp (phase t 62)) (h8843 : ¬InSupp (phase t 8843))
    (hsel : ∀ j<943, ¬InSupp (phase t (4393-j)) ∧ ¬InSupp (phase t (5495-j))) :
    dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) (t:V) % 2 = 0 := by
  obtain ⟨hn, hk, hp, hC, hslots, hcol⟩ := setting row dummy hw hN hs hbool hj t (by omega)
  set C := packedWord row dummy N
  set n : V := 8801*N
  set k : V := 8801*j+(t:V)
  obtain ⟨hs1, hs2⟩ := selectors_zero N C k t hw.pos hp hsel hslots
  have hb30 := source_absent N C k t 30 hw.pos hp h30 hslots
  have hb62 := source_absent N C k t 62 hw.pos hp h62 hslots
  have hb8843 := source_absent N C k t 8843 hw.pos hp h8843 hslots
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
  rw [hcol, hs1, hs2, bare_expand n C k hn hk hC, hb30, hb62, hb8843, htemp]
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
    (Or.inl ⟨rfl, by unfold phase InSupp; omega⟩) (by unfold phase InSupp; omega)
    (by unfold phase InSupp; omega) (by unfold phase InSupp; omega)
    (fun j hj => by constructor <;> (unfold phase InSupp; omega))
  simpa only [Nat.cast_ofNat] using h

theorem phase3296_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) :
    dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) 3296 % 2 = 0 := by
  have h := anchor_even row dummy hw hN hs hbool hj 3296 2200 1096 (Or.inr rfl) rfl (Or.inr rfl)
    (Or.inr ⟨rfl, by unfold phase InSupp; omega⟩) (by unfold phase InSupp; omega)
    (by unfold phase InSupp; omega) (by unfold phase InSupp; omega)
    (fun j hj => by constructor <;> (unfold phase InSupp; omega))
  simpa only [Nat.cast_ofNat] using h

/-! ## High-mask no-carry at the field and anchor phases -/

private theorem even_noCarry_one (x : V) (h : x%2=0) : NoCarry x 1 :=
  (noCarry_comm _ _).2 (one_noCarry_even x h)

theorem vertical_fields (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j p : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (hlo : 1013≤p) (hhi : p<1023) :
    NoCarry (dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) p)
      (dig 121 ((Mixed121Ports.highNat : ℕ) : V) p) := by
  obtain ⟨m, rfl⟩ := eq_nat_of_lt_nat (n:=1023) hhi
  have hmlo : 1013≤m := by exact_mod_cast hlo
  have hmhi : m<1023 := by exact_mod_cast hhi
  obtain ⟨u, hu, rfl⟩ : ∃ u, u < 10 ∧ m = 1013+u := ⟨m-1013, by omega, by omega⟩
  rw [Mixed121Parity.model_high _ (high_vertical u hu)]
  exact even_noCarry_one _ (vertical_even row dummy hw hN hs hbool hj u hu)

theorem horizontal_fields (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j p : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (hlo : 1065≤p) (hhi : p<1075) :
    NoCarry (dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) p)
      (dig 121 ((Mixed121Ports.highNat : ℕ) : V) p) := by
  obtain ⟨m, rfl⟩ := eq_nat_of_lt_nat (n:=1075) hhi
  have hmlo : 1065≤m := by exact_mod_cast hlo
  have hmhi : m<1075 := by exact_mod_cast hhi
  obtain ⟨u, hu, rfl⟩ : ∃ u, u < 10 ∧ m = 1065+u := ⟨m-1065, by omega, by omega⟩
  rw [Mixed121Parity.model_high _ (high_horizontal u hu)]
  exact even_noCarry_one _ (horizontal_even row dummy hw hN hs hbool hj u hu)

theorem phase2195_noCarry (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) :
    NoCarry (dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) 2195)
      (dig 121 ((Mixed121Ports.highNat : ℕ) : V) 2195) := by
  have h := Mixed121Parity.model_high (V:=V) 2195 Mixed121Parity.high2195
  simp only [Nat.cast_ofNat] at h
  rw [h]
  exact even_noCarry_one _ (phase2195_even row dummy hw hN hs hbool hj)

theorem phase3296_noCarry (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) :
    NoCarry (dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) 3296)
      (dig 121 ((Mixed121Ports.highNat : ℕ) : V) 3296) := by
  have h := Mixed121Parity.model_high (V:=V) 3296 Mixed121Parity.high3296
  simp only [Nat.cast_ofNat] at h
  rw [h]
  exact even_noCarry_one _ (phase3296_even row dummy hw hN hs hbool hj)

#print axioms Mixed121FieldParity.vertical_even
#print axioms Mixed121FieldParity.horizontal_even
#print axioms Mixed121FieldParity.phase2195_even
#print axioms Mixed121FieldParity.phase3296_even
#print axioms Mixed121FieldParity.vertical_fields
#print axioms Mixed121FieldParity.horizontal_fields
#print axioms Mixed121FieldParity.phase2195_noCarry
#print axioms Mixed121FieldParity.phase3296_noCarry
end Mixed121FieldParity
