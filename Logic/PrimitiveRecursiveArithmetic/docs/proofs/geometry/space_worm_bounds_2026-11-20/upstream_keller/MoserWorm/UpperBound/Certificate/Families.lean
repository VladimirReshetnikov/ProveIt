import Mathlib.Tactic.IntervalCases
import MoserWorm.UpperBound.Certificate.Rows

namespace MoserWorm.UpperBound.Certificate

/-! ### `familyMaxNorm2`: cumulative arrays and the four family bounds -/

/-- Partial sums `Σ_{j<i} g j` over `Q2`. -/
def psum (g : ℕ → Q2) (i : ℕ) : Q2 := ((List.range i).map g).sum

@[simp] lemma psum_zero (g : ℕ → Q2) : psum g 0 = 0 := rfl

lemma psum_succ (g : ℕ → Q2) (i : ℕ) : psum g (i + 1) = psum g i + g i := by
  simp [psum, List.range_succ]

/-- The cumulative array built by the A/B loops. -/
def cumFold (g : ℕ → Q2) (cnt : ℕ) (cap : ℕ) : Array Q2 :=
  (List.range' 0 cnt 1).foldl
    (fun A i => A.push (qadd (A.getD i (0, 0)) (g i)))
    ((Array.mkEmpty cap).push (0, 0))

lemma array_getD_eq (a : Array Q2) (i : ℕ) (d : Q2) :
    a.getD i d = a[i]?.getD d := by
  unfold Array.getD
  split
  · rw [Array.getElem?_eq_getElem (by assumption)]; rfl
  · rw [Array.getElem?_eq_none (by omega)]; rfl

lemma cumFold_spec (g : ℕ → Q2) (cnt cap : ℕ) :
    (cumFold g cnt cap).size = cnt + 1 ∧
    ∀ i ≤ cnt, (cumFold g cnt cap).getD i (0, 0) = psum g i := by
  induction cnt with
  | zero =>
    refine ⟨by simp [cumFold], fun i hi => ?_⟩
    interval_cases i
    rw [array_getD_eq]
    simp [cumFold]
  | succ n ih =>
    obtain ⟨hsz, hval⟩ := ih
    have hrec : cumFold g (n + 1) cap
        = (cumFold g n cap).push
            (qadd ((cumFold g n cap).getD n (0, 0)) (g n)) := by
      unfold cumFold
      rw [List.range'_1_concat, List.foldl_append, List.foldl_cons,
        List.foldl_nil, Nat.zero_add]
    refine ⟨by rw [hrec, Array.size_push, hsz], fun i hi => ?_⟩
    rw [hrec, array_getD_eq]
    rcases Nat.lt_or_ge i (n + 1) with hlt | hge
    · rw [Array.getElem?_push_lt (by omega)]
      have h2 := hval i (by omega)
      rw [array_getD_eq, Array.getElem?_eq_getElem (by omega)] at h2
      simpa using h2
    · have hieq : i = n + 1 := by omega
      subst hieq
      rw [show n + 1 = (cumFold g n cap).size by omega,
        Array.getElem?_push_size]
      have h2 := hval n (by omega)
      rw [hsz]
      simp only [Option.getD_some]
      rw [h2, qadd_eq, psum_succ]

/-- Generic growing-fold lemmas. -/
lemma foldl_ge_init {α : Type*} (l : List α) (F : ℚ → α → ℚ)
    (hF : ∀ s x, s ≤ F s x) (init : ℚ) : init ≤ l.foldl F init := by
  induction l generalizing init with
  | nil => simp
  | cons y ys ih => exact le_trans (hF init y) (ih _)

lemma foldl_ge_of_mem {α : Type*} (l : List α) (F : ℚ → α → ℚ)
    (hF : ∀ s x, s ≤ F s x) (init : ℚ) {x : α} (hx : x ∈ l) (v : ℚ)
    (hv : ∀ s, v ≤ F s x) : v ≤ l.foldl F init := by
  induction l generalizing init with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact le_trans (hv init) (foldl_ge_init ys F hF _)
    · exact ih _ hmem

lemma upd_grows (s : ℚ) (v : Q2) :
    s ≤ (if qnorm2 v > s then qnorm2 v else s) := by
  split
  · exact le_of_lt (by assumption)
  · exact le_rfl

lemma upd_dominates (s : ℚ) (v : Q2) :
    qnorm2 v ≤ (if qnorm2 v > s then qnorm2 v else s) := by
  split
  · exact le_rfl
  · exact le_of_not_gt (by assumption)

/-- The A/B cumulative fold in the simp-normal form appearing inside
`familyMaxNorm2` after loop conversion. -/
lemma cumFold_norm_getD (g : ℕ → Q2) (cnt : ℕ) {i : ℕ} (hi : i ≤ cnt) :
    ((List.range' 0 cnt).foldl
        (fun (A : Array Q2) j => A.push (A[j]?.getD (0, 0) + g j))
        #[(0, 0)])[i]?.getD (0, 0) = psum g i := by
  have hfun : (fun (A : Array Q2) j => A.push (A[j]?.getD (0, 0) + g j))
      = (fun (A : Array Q2) j => A.push (qadd (A.getD j (0, 0)) (g j))) := by
    funext A j
    rw [qadd_eq, array_getD_eq]
  have hinit : ((Array.mkEmpty (cnt + 1) : Array Q2).push (0, 0)) = #[(0, 0)] := by
    simp
  have h := (cumFold_spec g cnt (cnt + 1)).2 i hi
  rw [array_getD_eq] at h
  unfold cumFold at h
  rw [hfun, ← hinit]
  exact h

/-- Abbreviations for the goal-side partial sums. -/
def psumL (C : Forces) (k : ℕ) : ℕ → Q2 := psum (fun i => C[3 + k + i]?.getD (0,0))
def psumR (C : Forces) : ℕ → Q2 := psum (fun i => C[3 + i]?.getD (0,0))

/-- Family (i): left middle runs. -/
lemma fm_i (T : LabelTables) (C : Forces) (pLo pHi qLo qHi : ℕ)
    {a b : ℕ} (ha : qLo ≤ a) (hab : a ≤ b) (hb : b < T.kL) :
    qnorm2 (psumL C T.kR (b+1) - psumL C T.kR a)
      ≤ familyMaxNorm2 T C pLo pHi qLo qHi := by
  unfold familyMaxNorm2
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [tsub_zero, add_tsub_cancel_right, Nat.div_one, Array.mkEmpty_eq,
    List.push_toArray, List.nil_append, Array.getD_eq_getD_getElem?, qadd_eq,
    List.forIn_pure_yield_eq_foldl, qsub_eq, gt_iff_lt, bind_pure_comp,
    map_pure, bind_pure, Id.run_pure]
  refine le_trans ?_ (foldl_ge_init _ _
    (fun s x => foldl_ge_init _ _ (fun s' v => upd_grows s' _) s) _)
  refine le_trans ?_ (foldl_ge_init _ _ (fun s v => upd_grows s _) _)
  refine le_trans ?_ (foldl_ge_init _ _ (fun s v => upd_grows s _) _)
  refine foldl_ge_of_mem _ _
    (fun s x => foldl_ge_init _ _ (fun s' v => upd_grows s' _) s) _
    (x := a) (by rw [List.mem_range'_1]; omega) _ (fun s => ?_)
  refine foldl_ge_of_mem _ _ (fun s' v => upd_grows s' _) s
    (x := b) (by rw [List.mem_range'_1]; omega) _ (fun s' => ?_)
  rw [cumFold_norm_getD _ _ (show b + 1 ≤ T.kL by omega),
    cumFold_norm_getD _ _ (show a ≤ T.kL by omega)]
  exact upd_dominates s' _

/-- Family (ii): left runs to the end together with F-. -/
lemma fm_ii (T : LabelTables) (C : Forces) (pLo pHi qLo qHi : ℕ)
    {j : ℕ} (hj : j ≤ min qHi T.kL) :
    qnorm2 (psumL C T.kR T.kL - psumL C T.kR j + C[0]?.getD (0,0))
      ≤ familyMaxNorm2 T C pLo pHi qLo qHi := by
  unfold familyMaxNorm2
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [tsub_zero, add_tsub_cancel_right, Nat.div_one, Array.mkEmpty_eq,
    List.push_toArray, List.nil_append, Array.getD_eq_getD_getElem?, qadd_eq,
    List.forIn_pure_yield_eq_foldl, qsub_eq, gt_iff_lt, bind_pure_comp,
    map_pure, bind_pure, Id.run_pure]
  refine le_trans ?_ (foldl_ge_init _ _
    (fun s x => foldl_ge_init _ _ (fun s' v => upd_grows s' _) s) _)
  refine le_trans ?_ (foldl_ge_init _ _ (fun s v => upd_grows s _) _)
  refine foldl_ge_of_mem _ _ (fun s v => upd_grows s _) _
    (x := j) (by rw [List.mem_range'_1]; omega) _ (fun s => ?_)
  rw [cumFold_norm_getD _ _ (le_refl T.kL),
    cumFold_norm_getD _ _ (show j ≤ T.kL by omega)]
  exact upd_dominates s _

/-- Family (iii): P₊ and a right prefix. -/
lemma fm_iii (T : LabelTables) (C : Forces) (pLo pHi qLo qHi : ℕ)
    {j : ℕ} (hjl : pLo ≤ j) (hj : j ≤ T.kR) :
    qnorm2 (C[1]?.getD (0,0) + psumR C j)
      ≤ familyMaxNorm2 T C pLo pHi qLo qHi := by
  unfold familyMaxNorm2
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [tsub_zero, add_tsub_cancel_right, Nat.div_one, Array.mkEmpty_eq,
    List.push_toArray, List.nil_append, Array.getD_eq_getD_getElem?, qadd_eq,
    List.forIn_pure_yield_eq_foldl, qsub_eq, gt_iff_lt, bind_pure_comp,
    map_pure, bind_pure, Id.run_pure]
  refine le_trans ?_ (foldl_ge_init _ _
    (fun s x => foldl_ge_init _ _ (fun s' v => upd_grows s' _) s) _)
  refine foldl_ge_of_mem _ _ (fun s v => upd_grows s _) _
    (x := j) (by rw [List.mem_range'_1]; omega) _ (fun s => ?_)
  rw [cumFold_norm_getD _ _ hj]
  exact upd_dominates s _

/-- Family (iv): right blocks, including the empty block. -/
lemma fm_iv (T : LabelTables) (C : Forces) (pLo pHi qLo qHi : ℕ)
    (hpHi : pHi ≤ T.kR) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ pHi) :
    qnorm2 (psumR C b - psumR C a)
      ≤ familyMaxNorm2 T C pLo pHi qLo qHi := by
  unfold familyMaxNorm2
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [tsub_zero, add_tsub_cancel_right, Nat.div_one, Array.mkEmpty_eq,
    List.push_toArray, List.nil_append, Array.getD_eq_getD_getElem?, qadd_eq,
    List.forIn_pure_yield_eq_foldl, qsub_eq, gt_iff_lt, bind_pure_comp,
    map_pure, bind_pure, Id.run_pure]
  refine foldl_ge_of_mem _ _
    (fun s x => foldl_ge_init _ _ (fun s' v => upd_grows s' _) s) _
    (x := a) (by rw [List.mem_range'_1]; omega) _ (fun s => ?_)
  refine foldl_ge_of_mem _ _ (fun s' v => upd_grows s' _) s
    (x := b) (by rw [List.mem_range'_1]; omega) _ (fun s' => ?_)
  rw [cumFold_norm_getD _ _ (show b ≤ T.kR by omega),
    cumFold_norm_getD _ _ (show a ≤ T.kR by omega)]
  exact upd_dominates s' _


end MoserWorm.UpperBound.Certificate
