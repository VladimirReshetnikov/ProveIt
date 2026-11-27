import GRHArticle.ProgressionFree.IntegerSmoothPacking
import GRHArticle.ProgressionFree.IntegerSmoothNaturalBound

/-!
# A finite upper bound for the natural density with integral ratios

The 268 weighted triples below have 321 distinct vertices. All vertices are
7-smooth and at most 9800. Each vertex has capacity its reciprocal times
10^8. Lean checks every capacity and the total packed weight.
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

private def edgeList : List IntegerPackingTriple :=
  [⟨1, 2, 25000000⟩, ⟨1, 3, 11111111⟩, ⟨1, 5, 4000000⟩, ⟨1, 6, 2467528⟩,
    ⟨1, 7, 2040816⟩, ⟨1, 8, 1562500⟩, ⟨1, 10, 1000000⟩, ⟨1, 14, 510204⟩,
    ⟨1, 15, 444444⟩, ⟨1, 16, 390625⟩, ⟨1, 21, 226757⟩, ⟨1, 24, 173611⟩,
    ⟨1, 27, 137174⟩, ⟨1, 30, 111111⟩, ⟨1, 32, 61035⟩, ⟨1, 35, 81632⟩,
    ⟨1, 40, 62500⟩, ⟨1, 42, 56689⟩, ⟨1, 48, 43402⟩, ⟨1, 54, 34293⟩,
    ⟨1, 56, 31887⟩, ⟨1, 60, 27777⟩, ⟨1, 70, 20408⟩, ⟨1, 80, 15625⟩,
    ⟨1, 81, 15241⟩, ⟨1, 84, 14172⟩, ⟨1, 90, 12345⟩, ⟨2, 3, 5194044⟩,
    ⟨2, 4, 3063964⟩, ⟨2, 5, 2000000⟩, ⟨2, 7, 1020408⟩, ⟨2, 8, 781250⟩,
    ⟨2, 9, 322930⟩, ⟨2, 12, 347222⟩, ⟨2, 15, 222222⟩, ⟨2, 18, 135030⟩,
    ⟨2, 20, 125000⟩, ⟨2, 21, 113378⟩, ⟨2, 24, 86805⟩, ⟨2, 27, 68587⟩,
    ⟨2, 28, 63775⟩, ⟨2, 30, 33725⟩, ⟨2, 35, 40816⟩, ⟨2, 40, 31250⟩,
    ⟨2, 45, 24691⟩, ⟨2, 56, 15943⟩, ⟨2, 60, 13888⟩, ⟨2, 63, 12597⟩,
    ⟨3, 2, 7268306⟩, ⟨3, 4, 1065027⟩, ⟨3, 5, 1333333⟩, ⟨3, 7, 680272⟩,
    ⟨3, 8, 520833⟩, ⟨3, 9, 411522⟩, ⟨3, 10, 316666⟩, ⟨3, 12, 175218⟩,
    ⟨3, 14, 170068⟩, ⟨3, 16, 130208⟩, ⟨3, 18, 102880⟩, ⟨3, 20, 83333⟩,
    ⟨3, 27, 45724⟩, ⟨3, 28, 42517⟩, ⟨3, 30, 24519⟩, ⟨3, 32, 32552⟩,
    ⟨3, 35, 27210⟩, ⟨3, 40, 20833⟩, ⟨3, 45, 16460⟩, ⟨3, 50, 13333⟩,
    ⟨3, 54, 11431⟩, ⟨3, 56, 10629⟩, ⟨5, 2, 4836472⟩, ⟨5, 3, 2222222⟩,
    ⟨5, 4, 163527⟩, ⟨5, 6, 462962⟩, ⟨5, 7, 408163⟩, ⟨5, 8, 312500⟩,
    ⟨5, 12, 138888⟩, ⟨5, 14, 102040⟩, ⟨5, 16, 78125⟩, ⟨5, 18, 61728⟩,
    ⟨5, 21, 45351⟩, ⟨5, 25, 32000⟩, ⟨5, 27, 27434⟩, ⟨5, 28, 9823⟩,
    ⟨5, 30, 22222⟩, ⟨5, 32, 19531⟩, ⟨5, 36, 15432⟩, ⟨5, 42, 11337⟩,
    ⟨6, 4, 916430⟩, ⟨6, 5, 200241⟩, ⟨6, 7, 233686⟩, ⟨6, 8, 140605⟩,
    ⟨6, 9, 182898⟩, ⟨6, 20, 41666⟩, ⟨6, 28, 21258⟩, ⟨7, 2, 3571428⟩,
    ⟨7, 3, 1587301⟩, ⟨7, 5, 571428⟩, ⟨7, 6, 330687⟩, ⟨7, 8, 223214⟩,
    ⟨7, 10, 142857⟩, ⟨7, 12, 99206⟩, ⟨7, 15, 63492⟩, ⟨7, 16, 55803⟩,
    ⟨7, 18, 44091⟩, ⟨7, 20, 35714⟩, ⟨7, 24, 5367⟩, ⟨7, 27, 19596⟩,
    ⟨7, 30, 15873⟩, ⟨7, 32, 13950⟩, ⟨7, 36, 11022⟩, ⟨8, 3, 1388888⟩,
    ⟨8, 5, 499999⟩, ⟨8, 7, 255102⟩, ⟨8, 15, 21829⟩, ⟨8, 21, 28344⟩,
    ⟨8, 27, 17146⟩, ⟨8, 35, 10204⟩, ⟨10, 3, 905521⟩, ⟨10, 4, 605468⟩,
    ⟨10, 7, 204081⟩, ⟨10, 8, 156250⟩, ⟨10, 9, 82304⟩, ⟨10, 12, 69444⟩,
    ⟨10, 15, 44444⟩, ⟨10, 18, 30864⟩, ⟨10, 21, 22675⟩, ⟨10, 25, 16000⟩,
    ⟨10, 27, 13717⟩, ⟨10, 28, 12755⟩, ⟨14, 3, 648319⟩, ⟨14, 4, 432477⟩,
    ⟨14, 5, 274285⟩, ⟨14, 8, 111607⟩, ⟨14, 9, 58788⟩, ⟨14, 12, 49603⟩,
    ⟨14, 15, 1892⟩, ⟨14, 18, 22045⟩, ⟨14, 20, 17857⟩, ⟨14, 21, 16196⟩,
    ⟨14, 25, 11428⟩, ⟨15, 2, 940232⟩, ⟨15, 4, 416666⟩, ⟨15, 7, 136054⟩,
    ⟨15, 8, 104166⟩, ⟨15, 9, 82304⟩, ⟨15, 10, 66666⟩, ⟨15, 12, 46296⟩,
    ⟨15, 14, 17006⟩, ⟨15, 18, 20576⟩, ⟨15, 20, 16666⟩, ⟨15, 25, 10666⟩,
    ⟨16, 3, 617283⟩, ⟨16, 5, 250000⟩, ⟨16, 7, 127551⟩, ⟨16, 9, 77160⟩,
    ⟨16, 24, 10850⟩, ⟨18, 12, 38580⟩, ⟨21, 2, 779531⟩, ⟨21, 4, 236447⟩,
    ⟨21, 5, 190476⟩, ⟨21, 8, 74404⟩, ⟨21, 9, 58788⟩, ⟨21, 10, 47619⟩,
    ⟨21, 12, 33068⟩, ⟨21, 14, 24295⟩, ⟨21, 18, 14697⟩, ⟨21, 20, 11904⟩,
    ⟨24, 4, 92684⟩, ⟨24, 5, 166666⟩, ⟨24, 7, 85034⟩, ⟨24, 9, 51440⟩,
    ⟨24, 16, 16276⟩, ⟨24, 18, 12860⟩, ⟨24, 20, 10416⟩, ⟨27, 2, 925925⟩,
    ⟨27, 5, 148148⟩, ⟨27, 7, 75585⟩, ⟨27, 8, 57870⟩, ⟨27, 10, 12517⟩,
    ⟨27, 12, 25720⟩, ⟨27, 14, 18896⟩, ⟨27, 16, 14467⟩, ⟨30, 4, 67708⟩,
    ⟨30, 5, 106666⟩, ⟨35, 2, 583987⟩, ⟨35, 3, 293944⟩, ⟨35, 4, 84759⟩,
    ⟨35, 6, 79365⟩, ⟨35, 8, 44642⟩, ⟨35, 9, 23515⟩, ⟨35, 12, 19841⟩,
    ⟨35, 16, 11160⟩, ⟨40, 3, 277777⟩, ⟨40, 7, 51020⟩, ⟨40, 12, 17361⟩,
    ⟨42, 7, 48590⟩, ⟨54, 4, 115740⟩, ⟨54, 5, 74074⟩, ⟨54, 7, 37792⟩,
    ⟨54, 8, 28935⟩, ⟨54, 9, 22862⟩, ⟨56, 3, 198412⟩, ⟨56, 5, 71428⟩,
    ⟨56, 12, 12400⟩, ⟨60, 8, 26041⟩, ⟨70, 3, 60093⟩, ⟨80, 6, 34722⟩,
    ⟨80, 7, 15686⟩, ⟨81, 2, 282921⟩, ⟨81, 5, 49382⟩, ⟨81, 7, 25195⟩,
    ⟨81, 8, 19290⟩, ⟨84, 8, 18601⟩, ⟨105, 2, 122272⟩, ⟨105, 4, 45883⟩,
    ⟨105, 6, 26455⟩, ⟨105, 8, 1240⟩, ⟨112, 6, 19433⟩, ⟨120, 4, 39062⟩,
    ⟨120, 9, 10288⟩, ⟨125, 2, 200000⟩, ⟨125, 3, 88888⟩, ⟨125, 7, 16326⟩,
    ⟨125, 8, 12500⟩, ⟨126, 5, 29853⟩, ⟨135, 2, 185185⟩, ⟨135, 7, 15117⟩,
    ⟨135, 8, 11574⟩, ⟨150, 5, 26666⟩, ⟨150, 7, 13605⟩, ⟨168, 2, 61171⟩,
    ⟨168, 4, 37202⟩, ⟨168, 5, 23809⟩, ⟨189, 2, 132275⟩, ⟨189, 5, 21164⟩,
    ⟨210, 2, 24553⟩, ⟨210, 3, 24691⟩, ⟨210, 4, 29761⟩, ⟨210, 5, 19047⟩,
    ⟨216, 5, 18518⟩, ⟨250, 4, 25000⟩, ⟨270, 3, 41152⟩, ⟨270, 4, 23148⟩,
    ⟨280, 2, 66964⟩, ⟨280, 3, 39682⟩, ⟨280, 4, 22321⟩, ⟨343, 2, 72886⟩,
    ⟨343, 3, 32393⟩, ⟨343, 5, 11661⟩, ⟨378, 3, 29394⟩, ⟨378, 4, 16534⟩,
    ⟨378, 5, 10582⟩, ⟨420, 4, 13640⟩, ⟨480, 4, 13020⟩, ⟨512, 2, 36621⟩,
    ⟨512, 3, 21701⟩, ⟨512, 4, 12207⟩, ⟨625, 2, 40000⟩, ⟨625, 3, 17777⟩,
    ⟨630, 3, 17636⟩, ⟨875, 2, 28571⟩, ⟨875, 3, 12698⟩, ⟨945, 3, 11757⟩,
    ⟨1000, 3, 11111⟩, ⟨1470, 2, 17006⟩, ⟨1715, 2, 14577⟩, ⟨2401, 2, 10412⟩]

private def nodeList : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16,
    18, 20, 21, 24, 25, 27, 28, 30, 32, 35, 36, 40, 42, 45,
    48, 49, 50, 54, 56, 60, 63, 64, 70, 72, 75, 80, 81, 84,
    90, 96, 98, 100, 105, 108, 112, 120, 125, 126, 128, 135, 140, 144,
    147, 150, 160, 162, 168, 175, 180, 189, 192, 196, 200, 210, 216, 224,
    225, 240, 243, 245, 250, 252, 256, 270, 280, 288, 294, 300, 315, 320,
    324, 336, 343, 350, 360, 375, 378, 384, 392, 400, 405, 420, 432, 441,
    448, 450, 480, 486, 490, 500, 504, 512, 525, 540, 560, 567, 576, 588,
    600, 625, 630, 640, 648, 672, 675, 686, 700, 720, 729, 735, 750, 756,
    768, 784, 800, 810, 840, 864, 875, 882, 896, 900, 945, 960, 972, 980,
    1000, 1008, 1024, 1029, 1050, 1080, 1120, 1125, 1134, 1152, 1176, 1200, 1215, 1225,
    1250, 1260, 1280, 1296, 1323, 1344, 1350, 1372, 1400, 1440, 1458, 1470, 1500, 1512,
    1536, 1568, 1575, 1600, 1620, 1680, 1701, 1715, 1728, 1750, 1764, 1792, 1800, 1875,
    1890, 1920, 1944, 1960, 2016, 2025, 2048, 2058, 2100, 2160, 2187, 2205, 2240, 2250,
    2268, 2304, 2352, 2400, 2401, 2430, 2450, 2500, 2520, 2592, 2625, 2646, 2688, 2700,
    2800, 2835, 2880, 2916, 2940, 3000, 3024, 3072, 3087, 3125, 3136, 3150, 3200, 3240,
    3360, 3402, 3430, 3456, 3500, 3528, 3600, 3645, 3675, 3750, 3780, 3840, 3888, 3920,
    3969, 4000, 4032, 4050, 4116, 4200, 4320, 4374, 4410, 4480, 4500, 4536, 4608, 4704,
    4725, 4800, 4802, 4860, 4900, 5040, 5103, 5120, 5184, 5250, 5292, 5376, 5400, 5600,
    5625, 5670, 5760, 5832, 5880, 6000, 6048, 6075, 6125, 6144, 6174, 6250, 6272, 6300,
    6400, 6480, 6561, 6615, 6720, 6804, 6860, 6912, 7056, 7168, 7200, 7290, 7350, 7500,
    7680, 7776, 7840, 7875, 7938, 8000, 8064, 8100, 8192, 8400, 8505, 8575, 8640, 8748,
    8750, 8820, 8960, 9000, 9072, 9216, 9375, 9408, 9450, 9600, 9604, 9720, 9800]

private def packing := edgeList.toFinset
private def vertices := nodeList.toFinset

private def legalEdge (e : IntegerPackingTriple) : Bool :=
  decide (0 < e.first ∧ 1 < e.ratio ∧ e.first ∈ nodeList ∧
    e.first*e.ratio ∈ nodeList ∧ e.first*e.ratio*e.ratio ∈ nodeList)

private def loadAt (n : ℕ) : ℕ :=
  (edgeList.map (fun e ↦ if n = e.first ∨ n = e.first*e.ratio ∨ n = e.first*e.ratio*e.ratio
    then e.weight else 0)).sum

private def legalNode (n : ℕ) : Bool :=
  decide (n ∈ Nat.smoothNumbers 8 ∧ n * loadAt n ≤ 100000000)

private theorem all_of_batches {α : Type*} {l : List α} {f : α → Bool} (k : ℕ)
    (h₁ : (l.take k).all f = true) (h₂ : (l.drop k).all f = true) : l.all f = true := by
  rw [← List.take_append_drop k l, List.all_append, h₁, h₂]
  rfl

private def edgeOrderKey (e : IntegerPackingTriple) : ℕ := 100 * e.first + e.ratio

section Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem edgeList_nodup : edgeList.Nodup := by
  have h : (edgeList.map edgeOrderKey).IsChain (· < ·) := by decide +kernel
  exact List.Nodup.of_map edgeOrderKey ((List.isChain_iff_pairwise.mp h).imp ne_of_lt)

private theorem edgeList_checked : edgeList.all legalEdge = true := by
  iterate 16
    apply all_of_batches 16
    · as_aux_lemma => decide +kernel
  decide +kernel

private theorem nodeList_checked : nodeList.all legalNode = true := by
  iterate 20
    apply all_of_batches 16
    · as_aux_lemma => decide +kernel
  decide +kernel

private theorem edgeList_totalWeight : (edgeList.map IntegerPackingTriple.weight).sum = 110295741 := by
  decide +kernel

end Certificate

private theorem packing_valid :
    (∀ e ∈ packing, 0 < e.first ∧ 1 < e.ratio ∧ e.vertices ⊆ vertices) ∧
    (∀ n ∈ vertices, n ∈ Nat.smoothNumbers 8 ∧ n * integerPackingLoad packing n ≤ 100000000) ∧
    (∑ e ∈ packing, e.weight) = 110295741 := by
  refine ⟨?_, ?_, (List.sum_toFinset _ edgeList_nodup).trans edgeList_totalWeight⟩
  · intro e h
    have he' := of_decide_eq_true (List.all_eq_true.mp edgeList_checked e (List.mem_toFinset.mp h))
    simpa only [IntegerPackingTriple.vertices, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      vertices, List.mem_toFinset] using he'
  · intro n h
    have hv' := of_decide_eq_true (List.all_eq_true.mp nodeList_checked n (List.mem_toFinset.mp h))
    have hl : integerPackingLoad packing n = loadAt n := by
      rw [integerPackingLoad, packing, List.sum_toFinset _ edgeList_nodup]
      simp only [IntegerPackingTriple.vertices, Finset.mem_insert, Finset.mem_singleton, loadAt]
    simpa only [hl] using hv'

private theorem seven_smooth_factor : integerSmoothDensityFactor 7 = (8:ℝ)/35 := by
  have h : (∏ p ∈ Nat.primesLE 7, (1-(p:ℚ)⁻¹)) = (8:ℚ)/35 := by decide +kernel
  simpa only [integerSmoothDensityFactor, Rat.cast_prod, Rat.cast_sub, Rat.cast_one, Rat.cast_inv,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat] using congrArg (fun a : ℚ ↦ (a : ℝ)) h

/-- The entire smooth optimization is bounded using the mass that every
admissible set omits on the packed vertices. -/
theorem integerSmoothLowerOptimization_seven_packing (integral : Bool) :
    integerSmoothLowerOptimization integral 7 ≤ (327204259:ℝ)/437500000 := by
  obtain ⟨he,hv,ht⟩ := packing_valid
  have h := integerSmoothLowerOptimization_le_of_packing integral 7 packing vertices
    100000000 (by decide) he hv
  rw [ht, seven_smooth_factor] at h
  norm_num at h ⊢
  linarith only [h]

/-- The integral-ratio natural density supremum is less than 0.747896,
strengthening the article's strict upper bound of 0.749192. -/
theorem integerNaturalDensitySupremum_integral_lt :
    integerNaturalDensitySupremum true < (747896:ℝ)/1000000 :=
  ((integerNaturalDensitySupremum_le_smoothLower true 7).trans
    (integerSmoothLowerOptimization_seven_packing true)).trans_lt (by norm_num)

end GRHArticle.ProgressionFree
