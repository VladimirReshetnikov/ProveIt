import MoserWorm.UpperBound.Certificate.Coverage

namespace MoserWorm.UpperBound.Certificate

/-! ### Leaf extraction from an accepted tree (checker side of Lemma 4.7) -/

/-- Walking an accepted tree towards the split `(P, Q)` along a branch `β`
reaches a leaf that `checkLeaf` accepts, whose path assignment is consistent
with `β` and whose rectangle contains `(P, Q)` and lies inside the root
rectangle. -/
lemma checkTree_leaf_extract (ctx : Ctx) :
    ∀ (fuel : ℕ) (node : CTree) (assign : List (ℕ × Fin 2))
      (rect : ℕ × ℕ × ℕ × ℕ),
    checkTree ctx fuel node assign rect = true →
    ∀ (β : ℕ → Fin 2), (∀ mr ∈ assign, β mr.1 = mr.2) →
    (∀ mr ∈ assign, 2 * mr.1 + 1 < ctx.eRows.size) →
    ∀ P Q : ℕ, (rect.1 ≤ P ∧ P ≤ rect.2.1) → (rect.2.2.1 ≤ Q ∧ Q ≤ rect.2.2.2) →
    ∃ (assign' : List (ℕ × Fin 2)) (rect' : ℕ × ℕ × ℕ × ℕ)
      (mu : List (RowKey × ℚ)),
      (∀ mr ∈ assign', β mr.1 = mr.2) ∧
      (∀ mr ∈ assign', 2 * mr.1 + 1 < ctx.eRows.size) ∧
      (rect'.1 ≤ P ∧ P ≤ rect'.2.1) ∧ (rect'.2.2.1 ≤ Q ∧ Q ≤ rect'.2.2.2) ∧
      (rect.1 ≤ rect'.1 ∧ rect'.2.1 ≤ rect.2.1 ∧
       rect.2.2.1 ≤ rect'.2.2.1 ∧ rect'.2.2.2 ≤ rect.2.2.2) ∧
      checkLeaf ctx assign' rect' mu = true := by
  intro fuel
  induction fuel with
  | zero => intro node assign rect h; exact absurd h (by simp [checkTree])
  | succ fuel ih =>
    intro node assign rect h β hβ hbnd P Q hP hQ
    match node with
    | .leaf mu =>
      refine ⟨assign, rect, mu, hβ, hbnd, hP, hQ, ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩, ?_⟩
      rw [checkTree] at h
      exact h
    | .pl m c0 c1 =>
      rw [checkTree] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
      obtain ⟨⟨⟨hm, _⟩, h0⟩, h1⟩ := h
      by_cases hr : β m = 0
      · obtain ⟨a', r', mu, H⟩ := ih c0 ((m, 0) :: assign) rect h0 β
          (by rintro mr hmr
              rcases List.mem_cons.mp hmr with rfl | hmr2
              · exact hr
              · exact hβ mr hmr2)
          (by rintro mr hmr
              rcases List.mem_cons.mp hmr with rfl | hmr2
              · exact hm
              · exact hbnd mr hmr2) P Q hP hQ
        exact ⟨a', r', mu, H⟩
      · have hr1 : β m = 1 := by omega
        obtain ⟨a', r', mu, H⟩ := ih c1 ((m, 1) :: assign) rect h1 β
          (by rintro mr hmr
              rcases List.mem_cons.mp hmr with rfl | hmr2
              · exact hr1
              · exact hβ mr hmr2)
          (by rintro mr hmr
              rcases List.mem_cons.mp hmr with rfl | hmr2
              · exact hm
              · exact hbnd mr hmr2) P Q hP hQ
        exact ⟨a', r', mu, H⟩
    | .split cells =>
      rw [Partition.checkTree_split_eq] at h
      simp only [Partition.splitStruct, Bool.and_eq_true, List.all_eq_true,
        beq_iff_eq] at h
      obtain ⟨⟨⟨hin, hpw⟩, harea⟩, hch⟩ := h
      obtain ⟨r0, hr0, hr0P⟩ := exists_cell_of_cover (cells.map (·.1)) rect
        (by intro r hr
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
            exact hin x hx)
        (pairwiseOk_pairwise _ hpw) harea hP hQ
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr0
      have hins := hin x hx
      simp only [Partition.insideOK, Bool.and_eq_true, decide_eq_true_eq] at hins
      obtain ⟨a', r', mu, hc1, hc2, hc3, hc4, hc5, hc6⟩ :=
        ih x.2 assign x.1 (hch x hx) β hβ hbnd P Q
          ⟨hr0P.1, hr0P.2.1⟩ ⟨hr0P.2.2.1, hr0P.2.2.2⟩
      exact ⟨a', r', mu, hc1, hc2, hc3, hc4,
        ⟨by omega, by omega, by omega, by omega⟩, hc6⟩


/-! ### Full leaf extraction -/

lemma foldApply_size (l : List (RowData × ℚ)) (C0 : Array Q2) :
    (l.foldl (fun C rm => applyCoeffs C rm.2 rm.1.coeffs) C0).size = C0.size := by
  induction l generalizing C0 with
  | nil => rfl
  | cons rm rws' ih => rw [List.foldl_cons, ih, applyCoeffs_size]

lemma foldApply_getD (l : List (RowData × ℚ)) (C0 : Array Q2) (lab : ℕ)
    (hl : lab < C0.size) :
    (l.foldl (fun C rm => applyCoeffs C rm.2 rm.1.coeffs) C0).getD lab ((0 : ℚ),(0 : ℚ))
      = C0.getD lab ((0 : ℚ),(0 : ℚ)) + Cfun l lab := by
  induction l generalizing C0 with
  | nil => simp
  | cons rm rws' ih =>
    rw [List.foldl_cons, ih _ (by rwa [applyCoeffs_size]),
      applyCoeffs_getD _ _ _ _ hl, Cfun_cons, rowCoeff]
    abel

lemma checkLeafTail_true (ctx : Ctx) (rect : ℕ × ℕ × ℕ × ℕ)
    (C : Array Q2) (LB : ℚ) (h : checkLeafTail ctx rect C LB = true) :
    C.foldl qadd (0, 0) = ((0 : ℚ), (0 : ℚ)) ∧
    familyMaxNorm2 ctx.T C rect.1 rect.2.1 rect.2.2.1 rect.2.2.2 ≤ 1 ∧
    ctx.target ≤ LB := by
  unfold checkLeafTail at h
  split at h
  · simp at h
  · rename_i hz
    refine ⟨by simpa using hz, ?_⟩
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using h

/-- Everything an accepted leaf provides, at the functional level. -/
lemma checkLeaf_extract (ctx : Ctx) (assign : List (ℕ × Fin 2))
    (rect : ℕ × ℕ × ℕ × ℕ) (mu : List (RowKey × ℚ))
    (h : checkLeaf ctx assign rect mu = true) :
    ∃ rws : List (RowData × ℚ),
      (∀ rm ∈ rws, 0 ≤ rm.2 ∧ AllowedRow ctx assign rm.1) ∧
      ((List.range ctx.T.nLab).map (Cfun rws)).sum = 0 ∧
      ctx.target ≤ lbOf rws ∧
      (∀ a b, rect.2.2.1 ≤ a → a ≤ b → b < ctx.T.kL →
        qnorm2 (psum (fun i => Cfun rws (3 + ctx.T.kR + i)) (b+1)
          - psum (fun i => Cfun rws (3 + ctx.T.kR + i)) a) ≤ 1) ∧
      (∀ j, j ≤ min rect.2.2.2 ctx.T.kL →
        qnorm2 (psum (fun i => Cfun rws (3 + ctx.T.kR + i)) ctx.T.kL
          - psum (fun i => Cfun rws (3 + ctx.T.kR + i)) j + Cfun rws 0) ≤ 1) ∧
      (∀ j, rect.1 ≤ j → j ≤ ctx.T.kR →
        qnorm2 (Cfun rws 1 + psum (fun i => Cfun rws (3 + i)) j) ≤ 1) ∧
      (∀ a b, a ≤ b → b ≤ rect.2.1 → rect.2.1 ≤ ctx.T.kR →
        qnorm2 (psum (fun i => Cfun rws (3 + i)) b
          - psum (fun i => Cfun rws (3 + i)) a) ≤ 1) := by
  rw [checkLeaf_eq_gen, checkLeafGen_eq] at h
  cases hfold : muFold ctx assign mu
      (Array.replicate ctx.T.nLab ((0 : ℚ), (0 : ℚ)), (0 : ℚ)) with
  | none => rw [hfold] at h; exact absurd h (by simp)
  | some out =>
    rw [hfold] at h
    obtain ⟨C, LB⟩ := out
    obtain ⟨rws, hrws, hC, hLB⟩ := muFold_some _ _ _ _ _ hfold
    obtain ⟨hzero, hNorm, hst⟩ := checkLeafTail_true _ _ _ _ h
    simp only at hC hLB
    have hCsz : C.size = ctx.T.nLab := by
      rw [hC, foldApply_size, Array.size_replicate]
    have hCget : ∀ l, l < ctx.T.nLab → C.getD l ((0 : ℚ),(0 : ℚ)) = Cfun rws l := by
      intro l hl
      rw [hC, foldApply_getD _ _ _ (by rwa [Array.size_replicate]),
        array_getD_eq, Array.getElem?_replicate, if_pos hl]
      simp
    have hLBv : LB = lbOf rws := by rw [hLB]; simp
    -- psum bridges
    have hpsL : ∀ i, i ≤ ctx.T.kL →
        psum (fun j => C[3 + ctx.T.kR + j]?.getD ((0 : ℚ),(0 : ℚ))) i
          = psum (fun j => Cfun rws (3 + ctx.T.kR + j)) i := by
      intro i hi
      unfold psum
      congr 1
      refine List.map_congr_left (fun j hj => ?_)
      have hj' : j < i := List.mem_range.mp hj
      have := hCget (3 + ctx.T.kR + j)
        (by unfold LabelTables.nLab; omega)
      rw [array_getD_eq] at this
      exact this
    have hpsR : ∀ i, i ≤ ctx.T.kR →
        psum (fun j => C[3 + j]?.getD ((0 : ℚ),(0 : ℚ))) i
          = psum (fun j => Cfun rws (3 + j)) i := by
      intro i hi
      unfold psum
      congr 1
      refine List.map_congr_left (fun j hj => ?_)
      have hj' : j < i := List.mem_range.mp hj
      have := hCget (3 + j) (by unfold LabelTables.nLab; omega)
      rw [array_getD_eq] at this
      exact this
    have hc012 : ∀ l, l < 3 → C[l]?.getD ((0 : ℚ),(0 : ℚ)) = Cfun rws l := by
      intro l hl
      have := hCget l (lt_of_lt_of_le hl (nLab_ge_three ctx.T))
      rw [array_getD_eq] at this
      exact this
    refine ⟨rws, hrws, ?_, by rwa [← hLBv], ?_, ?_, ?_, ?_⟩
    · -- force sum zero
      have h1 : C.foldl qadd (0,0) = C.toList.foldl qadd (0,0) :=
        (Array.foldl_toList ..).symm
      have h2 : C.toList = (List.range ctx.T.nLab).map (fun l => Cfun rws l) := by
        refine List.ext_getElem? (fun i => ?_)
        rcases Nat.lt_or_ge i ctx.T.nLab with hi | hi
        · rw [List.getElem?_map, List.getElem?_range hi,
            Array.getElem?_toList, Array.getElem?_eq_getElem (by omega)]
          have := hCget i hi
          rw [array_getD_eq, Array.getElem?_eq_getElem (by omega)] at this
          simpa using this
        · rw [Array.getElem?_toList,
            Array.getElem?_eq_none (by rw [hCsz]; exact hi),
            List.getElem?_map,
            List.getElem?_eq_none (l := List.range ctx.T.nLab) (by simpa using hi)]
          rfl
      have h3 : ∀ (l : List Q2) (a : Q2), l.foldl qadd a = a + l.sum := by
        intro l
        induction l with
        | nil => intro a; simp
        | cons x xs ihl =>
          intro a
          rw [List.foldl_cons, ihl, List.sum_cons, qadd_eq, add_assoc]
      rw [h1, h2, h3] at hzero
      simpa using hzero
    · intro a b h1 h2 h3
      refine le_trans ?_ hNorm
      have := fm_i ctx.T C rect.1 rect.2.1 rect.2.2.1 rect.2.2.2
        (a := a) (b := b) h1 h2 h3
      unfold psumL at this
      rw [hpsL _ (by omega), hpsL _ (by omega)] at this
      exact this
    · intro j h1
      refine le_trans ?_ hNorm
      have := fm_ii ctx.T C rect.1 rect.2.1 rect.2.2.1 rect.2.2.2 (j := j) h1
      unfold psumL at this
      rw [hpsL _ le_rfl, hpsL _ (by omega), hc012 0 (by omega)] at this
      exact this
    · intro j h1 h2
      refine le_trans ?_ hNorm
      have := fm_iii ctx.T C rect.1 rect.2.1 rect.2.2.1 rect.2.2.2
        (j := j) h1 h2
      unfold psumR at this
      rw [hpsR _ h2, hc012 1 (by omega)] at this
      exact this
    · intro a b h1 h2 h3
      refine le_trans ?_ hNorm
      have := fm_iv ctx.T C rect.1 rect.2.1 rect.2.2.1 rect.2.2.2
        h3 (a := a) (b := b) h1 h2
      unfold psumR at this
      rw [hpsR _ (by omega), hpsR _ (by omega)] at this
      exact this

/-! ### Label bounds for rows -/

/-- The content of `labelsOK`. -/
lemma labelsOK_props (T : LabelTables) (h : labelsOK T = true) :
    T.right.size = T.kR ∧ T.left.size = T.kL ∧
    (∀ i < T.kR, 0 < (T.right.getD i (0,0)).1 ∧ qnorm2 (T.right.getD i (0,0)) = 1) ∧
    (∀ i, i + 1 < T.kR → (T.right.getD i (0,0)).2 < (T.right.getD (i+1) (0,0)).2) ∧
    (∀ j < T.kL, (T.left.getD j (0,0)).1 < 0 ∧ qnorm2 (T.left.getD j (0,0)) = 1) ∧
    (∀ j, j + 1 < T.kL → (T.left.getD (j+1) (0,0)).2 < (T.left.getD j (0,0)).2) := by
  unfold labelsOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h3, h6, fun i hi => h1 i hi, fun i hi => h2 i (by omega),
    fun j hj => h4 j hj, fun j hj => h5 j (by omega)⟩

lemma labOf_lt (T : LabelTables) (hr : T.right.size = T.kR)
    (hl : T.left.size = T.kL) {u : Q2} {l : ℕ} (h : T.labOf u = some l) :
    l < T.nLab := by
  unfold LabelTables.labOf at h
  have h3 := nLab_ge_three T
  split at h
  · injection h with h; omega
  · split at h
    · injection h with h; omega
    · split at h
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨i, hi, rfl⟩ := h
        rw [Array.findIdx?_eq_some_iff_findIdx_eq] at hi
        have := hi.1
        unfold LabelTables.nLab
        omega
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨i, hi, rfl⟩ := h
        rw [Array.findIdx?_eq_some_iff_findIdx_eq] at hi
        have := hi.1
        unfold LabelTables.nLab
        omega

/-- Membership extraction from `mapM` in `Option`. -/
lemma mapM_mem {α β : Type*} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys →
    ∀ y ∈ ys, ∃ x ∈ xs, f x = some y := by
  intro xs
  induction xs with
  | nil =>
    intro ys h y hy
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp at hy
  | cons x xs' ih =>
    intro ys h y hy
    rw [List.mapM_cons] at h
    cases hfx : f x with
    | none => rw [hfx] at h; simp at h
    | some b =>
      rw [hfx] at h
      cases hrest : xs'.mapM f with
      | none => rw [hrest] at h; simp at h
      | some bs =>
        rw [hrest] at h
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy2
        · exact ⟨x, by simp, hfx⟩
        · obtain ⟨x', hx', hfx'⟩ := ih bs hrest y hy2
          exact ⟨x', by simp [hx'], hfx'⟩

/-- Every coefficient label of a built E-row is a valid label. -/
lemma rowE_labels (T : LabelTables) (named : Array Q2) (p : PSpec) (r : Fin 2)
    (row : RowData) (hrow : rowE T named p r = some row)
    (hr : T.right.size = T.kR) (hl : T.left.size = T.kL) :
    RowLabelsLt T.nLab row := by
  intro lc hlc
  unfold rowE at hrow
  cases hpieces : (raySupp r).mapM (rowEPieces T named p r) with
  | none => rw [hpieces] at hrow; simp at hrow
  | some pieces =>
    rw [hpieces] at hrow
    simp only [Option.bind_some] at hrow
    split at hrow
    · injection hrow with hrow
      subst hrow
      simp only [List.mem_flatten] at hlc
      obtain ⟨piece, hpmem, hlcmem⟩ := hlc
      obtain ⟨i, _, hpi⟩ := mapM_mem _ _ _ hpieces piece hpmem
      unfold rowEPieces at hpi
      split at hpi
      · rw [Option.bind_eq_some_iff] at hpi
        obtain ⟨parts, _, hparts⟩ := hpi
        obtain ⟨wc, _, hwc⟩ := mapM_mem _ _ _ hparts lc hlcmem
        rw [Option.map_eq_some_iff] at hwc
        obtain ⟨l, hli, rfl⟩ := hwc
        exact labOf_lt T hr hl hli
      · rw [Option.map_eq_some_iff] at hpi
        obtain ⟨l, hli, rfl⟩ := hpi
        rw [List.mem_singleton] at hlcmem
        subst hlcmem
        exact labOf_lt T hr hl hli
    · simp at hrow

/-! ### Extraction of `checkCert` -/

lemma array_getD_gen {α : Type*} (a : Array α) (i : ℕ) (d : α) :
    a.getD i d = a[i]?.getD d := by
  unfold Array.getD
  split
  · rw [Array.getElem?_eq_getElem (by assumption)]; rfl
  · rw [Array.getElem?_eq_none (by omega)]; rfl

/-- Everything `checkCert c = true` provides, relative to the label tables. -/
lemma checkCert_extract (c : Cert) (hc : checkCert c = true)
    (T : LabelTables) (hT : buildLabels c.specs.toList = some T) :
    T.kR = c.kR ∧ T.kL = c.kL ∧ labelsOK T = true ∧
    (∀ k, k < 2 * c.specs.size →
      ((eRowsArr c T (namedByAngle T)).getD k none).isSome) ∧
    checkTree (⟨T, eRowsArr c T (namedByAngle T), c.target⟩ : Ctx)
      1000 c.tree [] (0, T.kR, 0, T.kL) = true := by
  unfold checkCert at hc
  rw [hT] at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨_, ⟨⟨⟨⟨hkR, hkL⟩, hOK⟩, hall⟩, htree⟩⟩ := hc
  refine ⟨hkR, hkL, hOK, ?_, htree⟩
  intro k hk
  rw [array_getD_gen, Array.getElem?_eq_getElem
    (by rw [eRowsArr, Array.size_ofFn]; exact hk)]
  have := (Array.all_eq_true.mp hall) k
    (by rw [eRowsArr, Array.size_ofFn]; exact hk)
  simpa using this

/-- The E-rows array evaluated at `2m + r`. -/
lemma eRowsArr_getD (c : Cert) (T : LabelTables) (named : Array Q2)
    (m : ℕ) (r : Fin 2) (hm : m < c.specs.size) :
    (eRowsArr c T named).getD (2 * m + r.val) none
      = rowE T named (c.specs[m]'hm) r := by
  have hk : 2 * m + r.val < 2 * c.specs.size := by
    have := r.isLt
    omega
  rw [array_getD_gen, eRowsArr, Array.getElem?_ofFn]
  rw [dif_pos hk]
  have hdiv : (2 * m + r.val) / 2 = m := by
    have := r.isLt
    omega
  have hmod : (2 * m + r.val) % 2 = r.val := by
    have := r.isLt
    omega
  simp only [Option.getD_some]
  congr 1
  · rw [hdiv]
    rw [array_getD_gen, Array.getElem?_eq_getElem hm]
    rfl
  · apply Fin.ext
    exact hmod


lemma checkCert_target (c : Cert) (h : checkCert c = true) : c.target = 1 := by
  have hlit : checkLiterals c = true := by
    unfold checkCert at h
    simp only [Bool.and_eq_true] at h
    tauto
  unfold checkLiterals at hlit
  simp only [Bool.and_eq_true, beq_iff_eq] at hlit
  tauto

end MoserWorm.UpperBound.Certificate
