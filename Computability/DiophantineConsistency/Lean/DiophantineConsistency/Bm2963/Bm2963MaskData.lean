import DiophantineConsistency.ArithmeticMaskData

/-! # The two block-mask2963 masks, as radix-`2^47` digit lists

The block-mask2963 counterpart of `Adm942MaskData` (`CurrentMaskData2011`,
`ArithmeticMaskData`; `research/low-padding-independent/PROOF.md` §3):
`ρ = 2^47`, `L = 2963`, `d = 47·2963 = 139261`, `β = ρ^L − 1`.

* The low mask `MC = β − Σ_{e∈Es} ρ^e`, with the admissible942 physical support
  `Es = [0,951) ∪ [960,986) ∪ {1005}` (978 positions). It is identified with the
  explicit digit list `lowDigits` (`ρ−2` on `Es`, `ρ−1` elsewhere) by the
  telescoping geometric identity, without evaluating the numeral.
* The high mask `MF_native = 4·G_917(ρ) + μ ρ^1956 + ρ^960·G_9(ρ) + ρ^987·G_8(ρ)
  + ρ^1005`, `μ = 2^44 − 2`, is defined by its digit list `highDigits`: the
  origin test merged with the bit-2 padding of fields `1..916`, the temporal and
  spatial copy tests, the marker and the single clause band at `1956`.

`research/block-mask2963-calibration/tools/check_recipe.py` transcribes these
lists and matches the pinned payloads `MC` and `MF_source = MF_native + β`
byte for byte (finite evidence outside Lean). The generic digit-list lemmas
(`G`, `G_geom`, `ofDigits_replicate_append`, `getD_replicate_append`, `pcF`)
are the 2011 ones. -/
set_option autoImplicit false
set_option Elab.async false

namespace Bm2963MaskData
open DiophantineConsistency DiophantineConsistency.LowMaskCoding
open DiophantineConsistency.ArithmeticMaskData (G G_one G_geom ofDigits_replicate_append
  sum_range_pow sum_Ico_pow getD_replicate_append pcF)

def radix : ℕ := 2 ^ 47

def width : ℕ := 47 * 2963

def beta : ℕ := radix ^ 2963 - 1

/-- The physical support `Es` (`PROOF.md` §3). -/
irreducible_def lowSupport : Finset ℕ := Finset.range 951 ∪ Finset.Ico 960 986 ∪ {1005}

/-- Membership in `Es` as an interval predicate. -/
def InSupport (e : ℕ) : Prop := e < 951 ∨ (960 ≤ e ∧ e < 986) ∨ e = 1005

instance (e : ℕ) : Decidable (InSupport e) := by unfold InSupport; infer_instance

theorem mem_lowSupport (e : ℕ) : e ∈ lowSupport ↔ InSupport e := by
  rw [lowSupport_def]
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico, Finset.mem_singleton, InSupport]
  tauto

/-- The marker is outside both preceding support intervals. -/
theorem lowSupport_marker_disjoint :
    Disjoint (Finset.range 951 ∪ Finset.Ico 960 986) ({1005} : Finset ℕ) := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico,
    Finset.mem_singleton] at hj hk
  omega

/-! ## Support difference facts (`PROOF.md` §5) -/

/-- Every support position other than the marker is at most 985. -/
theorem le_985 {e : ℕ} (he : InSupport e) (h : e ≠ 1005) : e ≤ 985 := by
  unfold InSupport at he; omega

theorem le_1005 {e : ℕ} (he : InSupport e) : e ≤ 1005 := by
  unfold InSupport at he; omega

/-- `1005` is a support difference only as `1005 − 0`. -/
theorem gap_1005 {e : ℕ} (he : InSupport e) (h : InSupport (e + 1005)) : e = 0 := by
  unfold InSupport at he h; omega

/-! ## The low mask -/

def lowPort : ℕ := mask radix 2 2963 lowSupport

theorem support_value :
    (∑ j ∈ lowSupport, radix^j) = G radix 951 + radix^960 * G radix 26 + radix^1005 := by
  have h1 := CurrentMasks2011.lowSupport_range_Ico_disjoint
  have h2 := lowSupport_marker_disjoint
  rw [lowSupport_def, Finset.sum_union h2, Finset.sum_union h1, Finset.sum_singleton,
    sum_range_pow, show (986:ℕ) = 960 + 26 by rfl, sum_Ico_pow]

/-- The low digit list with digit values `t` (support) and `t+1` (elsewhere). -/
def lowList (t : ℕ) : List ℕ :=
  List.replicate 951 t ++ (List.replicate 9 (t+1) ++
    (List.replicate 26 t ++ (List.replicate 19 (t+1) ++
      (List.replicate 1 t ++ (List.replicate 1957 (t+1) ++ [])))))

theorem lowList_identity (b t : ℕ) (hb : t + 2 = b) :
    Nat.ofDigits b (lowList t) + (G b 951 + b^960 * G b 26 + b^1005) + 1 = b^2963 := by
  simp only [lowList, ofDigits_replicate_append, Nat.ofDigits_nil, G_one]
  have h951 := G_geom b t 951 hb
  have h9 := G_geom b t 9 hb
  have h26 := G_geom b t 26 hb
  have h19 := G_geom b t 19 hb
  have h1957 := G_geom b t 1957 hb
  rw [show b^960 = b^951 * b^9 by ring, show b^1005 = b^951 * b^9 * b^26 * b^19 by ring,
    show b^2963 = b^951 * b^9 * b^26 * b^19 * b^1 * b^1957 by ring,
    ← h951, ← h9, ← h26, ← h19, ← h1957, pow_one, ← hb]
  ring

theorem radix_eq : radix = 2^47 := rfl

/-- The low mask digits: `2^47-2` on the support, `2^47-1` elsewhere. -/
def lowDigits : List ℕ := lowList (radix - 2)

theorem radix_pred : radix - 2 + 1 = radix - 1 := by norm_num [radix_eq]

theorem lowPort_ofDigits : lowPort = Nat.ofDigits radix lowDigits := by
  have hc := lowList_identity radix (radix - 2) (by norm_num [radix_eq])
  unfold lowPort LowMaskCoding.mask LowMaskCoding.supportValue
  rw [support_value]
  unfold lowDigits
  generalize G radix 951 + radix^960 * G radix 26 + radix^1005 = s at hc ⊢
  generalize Nat.ofDigits radix (lowList (radix - 2)) = x at hc ⊢
  generalize radix ^ 2963 = p at hc ⊢
  omega

theorem lowDigits_length : lowDigits.length = 2963 := by
  simp only [lowDigits, lowList, List.length_append, List.length_replicate, List.length_nil]

theorem lowDigits_getD (j : ℕ) (hj : j < 2963) :
    lowDigits.getD j 0 =
      if j < 951 ∨ (960 ≤ j ∧ j < 986) ∨ j = 1005 then radix - 2 else radix - 1 := by
  rw [← radix_pred]
  unfold lowDigits lowList
  simp only [getD_replicate_append, List.getD_nil]
  split_ifs <;> omega

theorem lowDigits_lt {x : ℕ} (hx : x ∈ lowDigits) : x < 2^47 := by
  simp only [lowDigits, lowList, List.mem_append, List.mem_replicate, List.not_mem_nil,
    or_false] at hx
  rw [radix_eq] at hx
  norm_num at hx ⊢
  omega

/-! ## The high mask -/

/-- The clause-band digit `μ = 2^44 − 2`. -/
def mu : ℕ := 2 ^ 44 - 2

/-- All nonzero high-mask digits occur in this 1957-digit prefix: the origin and
bit-2 padding `4` at `0..916`, the temporal copies `960..968`, the spatial copies
`987..994`, the marker `1005` and the clause band `1956`. -/
def highPrefix : List ℕ :=
  List.replicate 917 4 ++ List.replicate 43 0 ++ List.replicate 9 1 ++ List.replicate 18 0 ++
    List.replicate 8 1 ++ List.replicate 10 0 ++ [1] ++ List.replicate 950 0 ++ [mu]

def highDigits : List ℕ := highPrefix ++ List.replicate 1006 0

def highPort : ℕ := Nat.ofDigits radix highDigits

theorem highPrefix_length : highPrefix.length = 1957 := by
  simp only [highPrefix, List.length_append, List.length_replicate, List.length_nil,
    List.length_cons]

theorem highDigits_lt' {x : ℕ} (hx : x ∈ highDigits) : x < 2^47 := by
  simp only [highDigits, highPrefix, mu, List.mem_append, List.mem_cons, List.mem_replicate,
    List.not_mem_nil, or_false] at hx
  norm_num at hx ⊢
  omega

theorem highDigits_length : highDigits.length = 2963 := by
  simp only [highDigits, highPrefix, List.length_append, List.length_replicate, List.length_nil,
    List.length_cons]

theorem highDigits_zero : highDigits.getD 0 0 = 4 := rfl

theorem highPort_ofDigits : highPort = Nat.ofDigits (2^47) highDigits := rfl

theorem low_population : (lowDigits.map (pcF 47)).sum = 138283 := by
  decide +kernel

theorem high_population : (highDigits.map (pcF 47)).sum = 978 := by
  decide +kernel

theorem digit_population :
    (lowDigits.map (pcF 47)).sum + (highDigits.map (pcF 47)).sum = 139261 := by
  rw [low_population, high_population]

end Bm2963MaskData

#print axioms Bm2963MaskData.mem_lowSupport
#print axioms Bm2963MaskData.gap_1005
#print axioms Bm2963MaskData.lowPort_ofDigits
#print axioms Bm2963MaskData.lowDigits_getD
#print axioms Bm2963MaskData.highDigits_lt'
#print axioms Bm2963MaskData.digit_population
