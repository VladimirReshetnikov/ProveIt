import DiophantineConsistency.ArithmeticMaskData

/-! # The two admissible942 masks, as radix-`2^47` digit lists

The admissible942 counterpart of `CurrentMaskData2011` and `ArithmeticMaskData`
(`research/admissible942-independent/PROOF.md` §3–§4): `ρ = 2^47`, `L = 4027`,
`d = 47·4027 = 189269`, `β = ρ^L − 1`.

* The low mask `MC = β − Σ_{e∈Es} ρ^e`, with the physical support
  `Es = [0,951) ∪ [960,986) ∪ {1005}` (978 positions: the 2011 support with the
  marker moved from 1004 to 1005). It is identified with the explicit digit
  list `lowDigits` (`ρ−2` on `Es`, `ρ−1` elsewhere) by the telescoping
  geometric identity, without evaluating the numeral.
* The high mask `MF_native = 4 + μ(ρ^1992 + ρ^2998) + ρ^960·G_9(ρ) + ρ^987·G_8(ρ)
  + ρ^1005 + (ρ−1)ρ^4004·G_18(ρ) + (2^27−1)ρ^4022`, `μ = 2^44 − 2`, is defined
  by its digit list `highDigits`.

`research/admissible942-calibration/tools/check_ports.py` transcribes these
lists and matches the pinned payloads `MC` and `MF_source = MF_native + β`
byte for byte (finite evidence outside Lean). The generic digit-list lemmas
(`G`, `G_geom`, `ofDigits_replicate_append`, `getD_replicate_append`, `pcF`)
are the 2011 ones. -/
set_option autoImplicit false
set_option Elab.async false

namespace Adm942MaskData
open DiophantineConsistency DiophantineConsistency.LowMaskCoding
open DiophantineConsistency.ArithmeticMaskData (G G_one G_geom ofDigits_replicate_append
  sum_range_pow sum_Ico_pow getD_replicate_append pcF)

def radix : ℕ := 2 ^ 47

def width : ℕ := 47 * 4027

def beta : ℕ := radix ^ 4027 - 1

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

/-- The clause gap `1006` is not a support difference. -/
theorem gap_1006 {e : ℕ} (he : InSupport e) : ¬ InSupport (e + 1006) := by
  unfold InSupport at he ⊢; omega

/-- Its successor `1007` is not a support difference either. -/
theorem gap_1007 {e : ℕ} (he : InSupport e) : ¬ InSupport (e + 1007) := by
  unfold InSupport at he ⊢; omega

/-- `1005` is a support difference only as `1005 − 0`. -/
theorem gap_1005 {e : ℕ} (he : InSupport e) (h : InSupport (e + 1005)) : e = 0 := by
  unfold InSupport at he h; omega

/-! ## The low mask -/

def lowPort : ℕ := mask radix 2 4027 lowSupport

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
      (List.replicate 1 t ++ (List.replicate 3021 (t+1) ++ [])))))

theorem lowList_identity (b t : ℕ) (hb : t + 2 = b) :
    Nat.ofDigits b (lowList t) + (G b 951 + b^960 * G b 26 + b^1005) + 1 = b^4027 := by
  simp only [lowList, ofDigits_replicate_append, Nat.ofDigits_nil, G_one]
  have h951 := G_geom b t 951 hb
  have h9 := G_geom b t 9 hb
  have h26 := G_geom b t 26 hb
  have h19 := G_geom b t 19 hb
  have h3021 := G_geom b t 3021 hb
  rw [show b^960 = b^951 * b^9 by ring, show b^1005 = b^951 * b^9 * b^26 * b^19 by ring,
    show b^4027 = b^951 * b^9 * b^26 * b^19 * b^1 * b^3021 by ring,
    ← h951, ← h9, ← h26, ← h19, ← h3021, pow_one, ← hb]
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
  generalize radix ^ 4027 = p at hc ⊢
  omega

theorem lowDigits_length : lowDigits.length = 4027 := by
  simp only [lowDigits, lowList, List.length_append, List.length_replicate, List.length_nil]

theorem lowDigits_getD (j : ℕ) (hj : j < 4027) :
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

/-- All nonzero high-mask digits occur in this 4023-digit prefix: the origin
`4`, the temporal copies `960..968`, the spatial copies `987..994`, the marker
`1005`, the two clause bands `1992, 2998`, the padding `4004..4021` and the
partial padding field `4022`. -/
def highPrefix : List ℕ :=
  4 :: (List.replicate 959 0 ++ List.replicate 9 1 ++ List.replicate 18 0 ++
    List.replicate 8 1 ++ List.replicate 10 0 ++ [1] ++ List.replicate 986 0 ++ [mu] ++
    List.replicate 1005 0 ++ [mu] ++ List.replicate 1005 0 ++
    List.replicate 18 (2 ^ 47 - 1) ++ [2 ^ 27 - 1])

def highDigits : List ℕ := highPrefix ++ List.replicate 4 0

def highPort : ℕ := Nat.ofDigits radix highDigits

theorem highPrefix_length : highPrefix.length = 4023 := by
  simp only [highPrefix, List.length_append, List.length_replicate, List.length_nil,
    List.length_cons]

theorem highDigits_lt' {x : ℕ} (hx : x ∈ highDigits) : x < 2^47 := by
  simp only [highDigits, highPrefix, mu, List.mem_append, List.mem_cons, List.mem_replicate,
    List.not_mem_nil, or_false] at hx
  norm_num at hx ⊢
  omega

theorem highDigits_length : highDigits.length = 4027 := by
  simp only [highDigits, highPrefix, List.length_append, List.length_replicate, List.length_nil,
    List.length_cons]

theorem highDigits_zero : highDigits.getD 0 0 = 4 := rfl

theorem highPort_ofDigits : highPort = Nat.ofDigits (2^47) highDigits := rfl

theorem low_population : (lowDigits.map (pcF 47)).sum = 188291 := by
  decide +kernel

theorem high_population : (highDigits.map (pcF 47)).sum = 978 := by
  decide +kernel

theorem digit_population :
    (lowDigits.map (pcF 47)).sum + (highDigits.map (pcF 47)).sum = 189269 := by
  rw [low_population, high_population]

end Adm942MaskData

#print axioms Adm942MaskData.mem_lowSupport
#print axioms Adm942MaskData.gap_1006
#print axioms Adm942MaskData.gap_1005
#print axioms Adm942MaskData.lowPort_ofDigits
#print axioms Adm942MaskData.lowDigits_getD
#print axioms Adm942MaskData.highDigits_lt'
#print axioms Adm942MaskData.digit_population
