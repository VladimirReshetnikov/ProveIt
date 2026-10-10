import GowersSzemeredi.Proofs16SinglePieceSpectrum
import GowersSzemeredi.Proofs16EmbeddedLift
import GowersSzemeredi.Proofs16Translations
import GowersSzemeredi.Proofs16SingletonPartition

/-! A calculus of local piece providers (the single-piece lift, Notes L.1,
toward the remainder half of Lemma 16.9).

`LocalPieceFor c w Dom g` says that one function `g` on a domain has local
pieces everywhere. Take a set `H ⊆ Dom` of density `θ` in a proper box `P`.
Then some proper sub-box `R`, of width `≥ w θ (width P)`, and one
multilinear map agree with `g` on `c θ·|R|` points of `H ∩ R`.

It mirrors the corpus's cover calculus (`MultiplyLinearFunction.lift_last`,
`lift_prefix`, `lift_embedding`, `translate`), with pieces in place of
covers:
* `LocalMultilinearPieceAt.localPieceFor`: the dimension-`d` input gives a
  provider for every function with the hereditary product property.
* `LocalPieceFor.transport`, `.translate`, `.reindex`: providers move along
  translations and coordinate permutations, with the same parameters.
* `LocalPieceFor.lift_last`: an unused final coordinate costs density
  `c ↦ (θ/2)·c(θ/2)` and width `L ↦ ⌊√(w(θ/2)⌈L/8⌉ − 1)⌋ − 1`. The proof:
  - short-parent cells, then a dense cell;
  - popular fibres, then the provider on the base;
  - synchronized retiling (`box_product_tiling_of_contained_axis`), then a
    dense retiled cell.
  For pieces this step is simpler than for covers: there is no union over
  graphs.
* `local_piece_trivial`: the single-point fallback used when boxes are
  too narrow. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A local piece provider for one function on a domain. -/
def LocalPieceFor {N d : Nat} [NeZero N] (c : Real → Real) (w : Real → Nat → Nat)
    (Dom : Finset (Point N d)) (g : Point N d → ZMod N) : Prop :=
  ∀ theta : Real, 0 < theta → theta ≤ 1 →
    ∀ (P : Box N d) (H : Finset (Point N d)), P.IsProper → H ⊆ P.carrier → H ⊆ Dom →
      theta * P.carrier.card ≤ H.card →
      ∃ (R : Box N d) (mu : Point N d → ZMod N),
        R.IsProper ∧ R.carrier ⊆ P.carrier ∧ w theta P.width ≤ R.width ∧ IsMultilinear mu ∧
        c theta * R.carrier.card ≤ (H.filter fun x => x ∈ R.carrier ∧ g x = mu x).card

/-- **The input gives providers.** -/
theorem LocalMultilinearPieceAt.localPieceFor {d : Nat} {gamma : Real} {c : Real → Real}
    {w : Real → Nat → Nat} (hprov : LocalMultilinearPieceAt d gamma c w)
    {N : Nat} [NeZero N] [Fact N.Prime] {Dom : Finset (Point N d)} {g : Point N d → ZMod N}
    (hprod : ∀ B ⊆ Dom, HasProductProperty B g gamma) : LocalPieceFor c w Dom g :=
  fun theta hθ hθ1 P H hP hHP hHD hHc =>
    hprov N theta hθ hθ1 P H g hP hHP hHc (hprod H hHD)

/-- The single-point fallback: a piece of width at most one always exists. -/
theorem local_piece_trivial {N d : Nat} [NeZero N] {c : Real} (hc1 : c ≤ 1)
    {theta : Real} (hθ : 0 < theta) (P : Box N d) (hP : P.IsProper) (H : Finset (Point N d))
    (hHP : H ⊆ P.carrier) (hHc : theta * P.carrier.card ≤ H.card) (g : Point N d → ZMod N) :
    ∃ (R : Box N d) (mu : Point N d → ZMod N),
      R.IsProper ∧ R.carrier ⊆ P.carrier ∧ IsMultilinear mu ∧
      c * R.carrier.card ≤ (H.filter fun x => x ∈ R.carrier ∧ g x = mu x).card := by
  rcases H.eq_empty_or_nonempty with hH | ⟨z, hz⟩
  · subst hH
    have hP0 : (P.carrier.card : Real) ≤ 0 := by
      have : theta * P.carrier.card ≤ 0 := by simpa using hHc
      by_contra hpos
      have hpos' : (0 : Real) < P.carrier.card := lt_of_not_ge hpos
      linarith [mul_pos hθ hpos']
    refine ⟨P, fun _ => 0, hP, Finset.Subset.refl _, isMultilinear_constant 0, ?_⟩
    have : (P.carrier.card : Real) = 0 := le_antisymm hP0 (Nat.cast_nonneg _)
    rw [this, mul_zero]
    exact Nat.cast_nonneg _
  · refine ⟨pointSingletonBox z, fun _ => g z, pointSingletonBox_isProper z, ?_,
      isMultilinear_constant (g z), ?_⟩
    · rw [pointSingletonBox_carrier]
      exact Finset.singleton_subset_iff.mpr (hHP hz)
    · rw [pointSingletonBox_carrier, Finset.card_singleton, Nat.cast_one, mul_one]
      have hmem : z ∈ H.filter fun x => x ∈ ({z} : Finset (Point N d)) ∧ g x = g z :=
        Finset.mem_filter.mpr ⟨hz, Finset.mem_singleton_self z, rfl⟩
      have : (1 : Real) ≤ (H.filter fun x => x ∈ ({z} : Finset (Point N d)) ∧ g x = g z).card := by
        exact_mod_cast Finset.card_pos.mpr ⟨z, hmem⟩
      linarith

/-- **Transport along a point equivalence that carries boxes to boxes.** -/
theorem LocalPieceFor.transport {N d : Nat} [NeZero N] {c : Real → Real}
    {w : Real → Nat → Nat} {Dom : Finset (Point N d)} {g : Point N d → ZMod N}
    (h : LocalPieceFor c w Dom g) (T : Point N d ≃ Point N d) (β β' : Box N d → Box N d)
    (hβ : ∀ P, (β P).carrier = P.carrier.image T)
    (hβ' : ∀ R, (β' R).carrier = R.carrier.image T.symm)
    (hprop : ∀ P, P.IsProper → (β P).IsProper) (hprop' : ∀ R, R.IsProper → (β' R).IsProper)
    (hwidth : ∀ P, (β P).width = P.width) (hwidth' : ∀ R, (β' R).width = R.width)
    (hmult : ∀ mu, IsMultilinear mu → IsMultilinear (fun x => mu (T x))) :
    LocalPieceFor c w (Finset.univ.filter fun x => T x ∈ Dom) (fun x => g (T x)) := by
  intro theta hθ hθ1 P H hP hHP hHD hHc
  have hH1P : H.image T ⊆ (β P).carrier := by
    rw [hβ]; exact Finset.image_subset_image hHP
  have hH1D : H.image T ⊆ Dom := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp (hHD hx)).2
  have hcardβ : (β P).carrier.card = P.carrier.card := by
    rw [hβ, Finset.card_image_of_injective _ T.injective]
  have hcardH : (H.image T).card = H.card := Finset.card_image_of_injective _ T.injective
  obtain ⟨R, mu, hR, hRP, hRw, hmu, hcount⟩ := h theta hθ hθ1 (β P) (H.image T) (hprop P hP)
    hH1P hH1D (by rw [hcardβ, hcardH]; exact hHc)
  have hmemR : ∀ x, x ∈ (β' R).carrier ↔ T x ∈ R.carrier := by
    intro x
    rw [hβ']
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
      rw [← hxy, Equiv.apply_symm_apply]; exact hy
    · intro hx
      exact Finset.mem_image.mpr ⟨T x, hx, Equiv.symm_apply_apply T x⟩
  refine ⟨β' R, fun x => mu (T x), hprop' R hR, ?_, ?_, hmult mu hmu, ?_⟩
  · intro x hx
    have hTx := hRP ((hmemR x).mp hx)
    rw [hβ] at hTx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hTx
    rw [← T.injective hyx]; exact hy
  · rw [hwidth', ← hwidth P]; exact hRw
  · have hcardR : (β' R).carrier.card = R.carrier.card := by
      rw [hβ', Finset.card_image_of_injective _ T.symm.injective]
    have hcnt : (H.filter fun x => x ∈ (β' R).carrier ∧ g (T x) = mu (T x)).card =
        ((H.image T).filter fun y => y ∈ R.carrier ∧ g y = mu y).card := by
      rw [Finset.filter_image, Finset.card_image_of_injective _ T.injective]
      congr 1
      exact Finset.filter_congr fun x _ => by rw [hmemR]
    calc c theta * ((β' R).carrier.card : Real) = c theta * R.carrier.card := by rw [hcardR]
      _ ≤ _ := hcount
      _ = _ := by rw [hcnt]

/-- Providers move along translations. -/
theorem LocalPieceFor.translate {N d : Nat} [NeZero N] [Fact N.Prime] {c : Real → Real}
    {w : Real → Nat → Nat} {Dom : Finset (Point N d)} {g : Point N d → ZMod N}
    (h : LocalPieceFor c w Dom g) (t : Point N d) :
    LocalPieceFor c w (Finset.univ.filter fun x => x + t ∈ Dom) (fun x => g (x + t)) := by
  have := h.transport (Equiv.addRight t) (fun P => P.translate t) (fun R => R.translate (-t))
    (fun P => P.translate_carrier t)
    (fun R => by
      rw [R.translate_carrier (-t)]
      congr 1)
    (fun P hP => hP.translate t) (fun R hR => hR.translate (-t))
    (fun P => P.translate_width t) (fun R => R.translate_width (-t))
    (fun mu hmu => hmu.translate t)
  simpa only [Equiv.coe_addRight] using this

/-- Providers move along coordinate permutations. -/
theorem LocalPieceFor.reindex {N d : Nat} [NeZero N] {c : Real → Real}
    {w : Real → Nat → Nat} {Dom : Finset (Point N d)} {g : Point N d → ZMod N}
    (h : LocalPieceFor c w Dom g) (e : Fin d ≃ Fin d) :
    LocalPieceFor c w (Finset.univ.filter fun x => coordinateReindex e x ∈ Dom)
      (fun x => g (coordinateReindex e x)) :=
  h.transport (coordinateReindex e) (fun P => P.coordinateReindex e)
    (fun R => R.coordinateReindex e.symm)
    (fun P => P.coordinateReindex_carrier e)
    (fun R => by rw [R.coordinateReindex_carrier e.symm]; rfl)
    (fun P hP => hP.coordinateReindex e) (fun R hR => hR.coordinateReindex e.symm)
    (fun P => P.coordinateReindex_width e) (fun R => R.coordinateReindex_width e.symm)
    (fun mu hmu => hmu.coordinateReindex e)

/-- The density after one unused coordinate. -/
def liftLastC (c : Real → Real) (theta : Real) : Real :=
  theta / 2 * c (theta / 2)

/-- The width after one unused coordinate. -/
def liftLastW (w : Real → Nat → Nat) (theta : Real) (L : Nat) : Nat :=
  if 4 ≤ L then Nat.sqrt (w (theta / 2) ⌈(L : Real) / 8⌉₊ - 1) - 1 else 0

theorem liftLastC_pos_le {c : Real → Real} (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) :
    ∀ t, 0 < t → t ≤ 1 → 0 < liftLastC c t ∧ liftLastC c t ≤ 1 := by
  intro t ht ht1
  obtain ⟨h1, h2⟩ := hc (t / 2) (by positivity) (by linarith)
  refine ⟨by unfold liftLastC; positivity, ?_⟩
  unfold liftLastC
  calc t / 2 * c (t / 2) ≤ 1 * 1 := mul_le_mul (by linarith) h2 h1.le zero_le_one
    _ = 1 := one_mul 1

theorem liftLastW_mono {w : Real → Nat → Nat} (hw : ∀ t, Monotone (w t)) :
    ∀ t, Monotone (liftLastW w t) := by
  intro t L L' hLL'
  unfold liftLastW
  by_cases h4 : 4 ≤ L
  · rw [if_pos h4, if_pos (h4.trans hLL')]
    have hceil : ⌈(L : Real) / 8⌉₊ ≤ ⌈(L' : Real) / 8⌉₊ :=
      Nat.ceil_mono (div_le_div_of_nonneg_right (by exact_mod_cast hLL') (by norm_num))
    exact Nat.sub_le_sub_right (Nat.sqrt_le_sqrt (Nat.sub_le_sub_right (hw _ hceil) 1)) 1
  · rw [if_neg h4]; exact Nat.zero_le _

/-- The points-to-pairs map is injective. -/
theorem initLast_injective {N d : Nat} :
    Function.Injective fun z : Point N (d + 1) => (section16Init z, section16Last z) := by
  intro z z' h
  simp only [Prod.mk.injEq] at h
  have hz : z = Fin.snoc (section16Init z) (section16Last z) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [section16Last]
    · simp [section16Init]
  have hz' : z' = Fin.snoc (section16Init z') (section16Last z') := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [section16Last]
    · simp [section16Init]
  rw [hz, hz', h.1, h.2]

/-- **An unused final coordinate.** -/
theorem LocalPieceFor.lift_last {N d : Nat} [NeZero N] [Fact N.Prime] (hd : 0 < d)
    {c : Real → Real} {w : Real → Nat → Nat} {Dom : Finset (Point N d)} {g : Point N d → ZMod N}
    (h : LocalPieceFor c w Dom g)
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t)) :
    LocalPieceFor (liftLastC c) (liftLastW w)
      (Finset.univ.filter fun z : Point N (d + 1) => section16Init z ∈ Dom)
      (fun z => g (section16Init z)) := by
  intro theta hθ hθ1 P H hP hHP hHD hHc
  obtain ⟨hc'pos, hc'le⟩ := liftLastC_pos_le hc theta hθ hθ1
  -- the fallback, used whenever the target width is zero
  have hfallback : liftLastW w theta P.width = 0 →
      ∃ (R : Box N (d + 1)) (mu : Point N (d + 1) → ZMod N),
        R.IsProper ∧ R.carrier ⊆ P.carrier ∧ liftLastW w theta P.width ≤ R.width ∧
        IsMultilinear mu ∧ liftLastC c theta * R.carrier.card ≤
          (H.filter fun x => x ∈ R.carrier ∧ g (section16Init x) = mu x).card := by
    intro h0
    obtain ⟨R, mu, hR, hRP, hmu, hcount⟩ :=
      local_piece_trivial hc'le hθ P hP H hHP hHc _
    exact ⟨R, mu, hR, hRP, by rw [h0]; exact Nat.zero_le _, hmu, hcount⟩
  by_cases hL : 4 ≤ P.width
  swap
  · exact hfallback (by unfold liftLastW; rw [if_neg hL])
  -- 1. short-parent cells and a dense cell
  set I := P.axis (Fin.last d) with hIdef
  have hI : I.IsProper := hP (Fin.last d)
  have hIlen : P.width ≤ I.length := P.width_le_axis_length (Fin.last d)
  obtain ⟨L, Q, hQpart, hQprop, hQaxes, hQstep⟩ :=
    (boxInit P).short_parent_partition I (boxInit_isProper P hP) hI hd hL
      (boxInit_width P hd) hIlen
  have hPcarrier : P.carrier = lastProductSet (boxInit P).carrier I.carrier :=
    (boxInit_last_product P).1
  have hPne : P.carrier.Nonempty :=
    P.carrier_nonempty_of_axis_pos fun z => lt_of_lt_of_le (by omega) (P.width_le_axis_length z)
  have hPcard : (0 : Real) < P.carrier.card := by exact_mod_cast hPne.card_pos
  have hHne : H.Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.cast_pos.mp (lt_of_lt_of_le (mul_pos hθ hPcard) hHc)
  obtain ⟨l, hl⟩ := exists_dense_cell (fun l => lastProductSet (Q l).carrier I.carrier)
    _ (lastProductSet_partition _ _ _ hQpart) H id
    (fun z hz => by rw [← hPcarrier]; exact hHP hz) hHne
    (by rw [← hPcarrier]; exact hHc)
  set Hl := H.filter fun z => id z ∈ lastProductSet (Q l).carrier I.carrier with hHldef
  -- 2. pairs, popular fibres and the provider on the base
  set Hp := Hl.image fun z => (section16Init z, section16Last z) with hHpdef
  have hHpcard : Hp.card = Hl.card := Finset.card_image_of_injective _ initLast_injective
  have hHpsub : Hp ⊆ (Q l).carrier ×ˢ I.carrier := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    have hz' := (Finset.mem_filter.mp hz).2
    simp only [id, lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
    exact Finset.mem_product.mpr hz'
  have hIcard : (I.carrier.card : Real) = I.length := by rw [hI]
  have hIpos : (0 : Real) < I.carrier.card := by
    rw [hIcard]; exact_mod_cast (show 0 < I.length by omega)
  have hQcard : ((lastProductSet (Q l).carrier I.carrier).card : Real) =
      (Q l).carrier.card * I.carrier.card := by
    rw [lastProductSet_card]; push_cast; ring
  set H1 := (Q l).carrier.filter fun x =>
    theta / 2 * I.carrier.card ≤ ((Hp.filter fun p => p.1 = x).card : Real) with hH1def
  have hH1 : theta / 2 * (Q l).carrier.card ≤ H1.card :=
    popular_fibres (Q l).carrier I.carrier Hp hHpsub (by exact_mod_cast hIpos)
      (by positivity) (by
        rw [hHpcard]
        calc 2 * (theta / 2) * ((Q l).carrier.card : Real) * I.carrier.card =
            theta * ((lastProductSet (Q l).carrier I.carrier).card : Real) := by
              rw [hQcard]; ring
          _ ≤ _ := hl)
  have hH1D : H1 ⊆ Dom := by
    intro x hx
    have h1 := (Finset.mem_filter.mp hx).2
    have hpos : 0 < (Hp.filter fun p => p.1 = x).card :=
      Nat.cast_pos.mp (lt_of_lt_of_le (by positivity) h1)
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    obtain ⟨hpHp, rfl⟩ := Finset.mem_filter.mp hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hpHp
    exact (Finset.mem_filter.mp (hHD (Finset.mem_filter.mp hz).1)).2
  obtain ⟨hcpos, hcle⟩ := hc (theta / 2) (by positivity) (by linarith)
  obtain ⟨R, mu, hR, hRQ, hRw, hmu, hRc⟩ := h (theta / 2) (by positivity) (by linarith)
    (Q l) H1 (hQprop l).1 (Finset.filter_subset _ _) hH1D hH1
  set G := H1.filter fun x => x ∈ R.carrier ∧ g x = mu x with hGdef
  have hQw : ⌈(P.width : Real) / 8⌉₊ ≤ (Q l).width := Nat.ceil_le.mpr (hQprop l).2
  have hRwP : w (theta / 2) ⌈(P.width : Real) / 8⌉₊ ≤ R.width := (hw _ hQw).trans hRw
  by_cases hR2 : 2 ≤ R.width
  swap
  · apply hfallback
    unfold liftLastW
    rw [if_pos hL]
    have : w (theta / 2) ⌈(P.width : Real) / 8⌉₊ - 1 = 0 := by omega
    rw [this]; rfl
  -- 3. retile `R × I` and pick a dense cell
  set i0 : Fin d := ⟨0, hd⟩
  have hRne : R.carrier.Nonempty :=
    R.carrier_nonempty_of_axis_pos fun z => lt_of_lt_of_le (by omega) (R.width_le_axis_length z)
  have hsub : (R.axis i0).carrier ⊆ ((Q l).axis i0).carrier :=
    R.axis_carrier_subset_of_carrier_subset (Q l) hRne hRQ i0
  have hIstep : I.step = P.commonDiff := P.axis_step (Fin.last d)
  obtain ⟨u, hu⟩ := I.step_isUnit_of_prime hI (by omega)
  have hQaxstep : ((Q l).axis i0).step = P.commonDiff := by
    rw [(Q l).axis_step, hQstep l]; rfl
  set v := Nat.sqrt (R.width - 1) with hvdef
  have hv : 1 ≤ v := Nat.le_sqrt.mpr (by omega)
  have hfit : v ^ 2 ≤ R.width - 1 := Nat.sqrt_le' _
  obtain ⟨M, S, J, hSpart, hSprop, hSprod, -⟩ :=
    box_product_tiling_of_contained_axis R ((Q l).axis i0) I i0 u hR hI
      (by rw [hQaxstep, hu, hIstep]) (by rw [hQaxstep, hIstep]) hsub (hQaxes l i0).2.1
      (hQaxes l i0).2.2 hv hfit
  set Z := Hl.filter fun z => section16Init z ∈ G with hZdef
  have hZin : ∀ z ∈ Z, z ∈ lastProductSet R.carrier I.carrier := by
    intro z hz
    obtain ⟨hzHl, hzG⟩ := Finset.mem_filter.mp hz
    have hz' := (Finset.mem_filter.mp hzHl).2
    simp only [id, lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz' ⊢
    exact ⟨(Finset.mem_filter.mp hzG).2.1, hz'.2⟩
  have hZcard : liftLastC c theta * (lastProductSet R.carrier I.carrier).card ≤ Z.card := by
    have hpairs : (Hp.filter fun p => p.1 ∈ G) = Z.image fun z =>
        (section16Init z, section16Last z) := by
      rw [hHpdef, Finset.filter_image, hZdef]
    have hfib := fibre_sum_ge Hp G (s := theta / 2 * I.carrier.card) fun x hx =>
      (Finset.mem_filter.mp (Finset.filter_subset _ _ hx)).2
    rw [hpairs, Finset.card_image_of_injective _ initLast_injective] at hfib
    rw [lastProductSet_card]
    push_cast
    calc liftLastC c theta * ((R.carrier.card : Real) * I.carrier.card) =
        c (theta / 2) * R.carrier.card * (theta / 2 * I.carrier.card) := by
          unfold liftLastC; ring
      _ ≤ G.card * (theta / 2 * I.carrier.card) :=
          mul_le_mul_of_nonneg_right hRc (by positivity)
      _ ≤ _ := hfib
  have hZne : Z.Nonempty := by
    rw [← Finset.card_pos]
    have hRpos : (0 : Real) < R.carrier.card := by exact_mod_cast hRne.card_pos
    have : (0 : Real) < liftLastC c theta * (lastProductSet R.carrier I.carrier).card := by
      rw [lastProductSet_card]; push_cast; exact mul_pos hc'pos (mul_pos hRpos hIpos)
    exact Nat.cast_pos.mp (lt_of_lt_of_le this hZcard)
  obtain ⟨j, hj⟩ := exists_dense_cell (fun j => (S j).carrier) _ hSpart Z id hZin hZne hZcard
  refine ⟨S j, fun z => mu (section16Init z), (hSprop j).1, ?_, ?_, hmu.lift_last, ?_⟩
  · intro z hz
    have hz' := IsPartition.cell_subset hSpart j hz
    rw [hPcarrier]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz'
    simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨IsPartition.cell_subset hQpart l (hRQ hz'.1), hz'.2⟩
  · unfold liftLastW
    rw [if_pos hL]
    have hsq : Nat.sqrt (w (theta / 2) ⌈(P.width : Real) / 8⌉₊ - 1) ≤ v :=
      Nat.sqrt_le_sqrt (Nat.sub_le_sub_right hRwP 1)
    have := (hSprop j).2
    omega
  · refine hj.trans ?_
    exact_mod_cast Finset.card_le_card fun z hz => by
      obtain ⟨hzZ, hzS⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzHl, hzG⟩ := Finset.mem_filter.mp hzZ
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzHl).1, hzS,
        (Finset.mem_filter.mp hzG).2.2⟩


/-- Providers respect equal domains and agreeing functions. -/
theorem LocalPieceFor.congr {N d : Nat} [NeZero N] {c : Real → Real} {w : Real → Nat → Nat}
    {Dom Dom' : Finset (Point N d)} {g g' : Point N d → ZMod N}
    (h : LocalPieceFor c w Dom g) (hDom : Dom' = Dom) (hg : ∀ x, g' x = g x) :
    LocalPieceFor c w Dom' g' := by
  subst hDom
  have hfun : g' = g := funext hg
  subst hfun
  exact h

theorem liftLastC_iterate_pos_le {c : Real → Real}
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (m : Nat) :
    ∀ t, 0 < t → t ≤ 1 → 0 < (liftLastC^[m] c) t ∧ (liftLastC^[m] c) t ≤ 1 := by
  induction m with
  | zero => simpa using hc
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact liftLastC_pos_le ih

theorem liftLastW_iterate_mono {w : Real → Nat → Nat} (hw : ∀ t, Monotone (w t)) (m : Nat) :
    ∀ t, Monotone ((liftLastW^[m] w) t) := by
  induction m with
  | zero => simpa using hw
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact liftLastW_mono ih

/-- **Unused final coordinates**, any number of them. -/
theorem LocalPieceFor.lift_prefix {N l : Nat} [NeZero N] [Fact N.Prime] (hl : 0 < l)
    {c : Real → Real} {w : Real → Nat → Nat} {Dom : Finset (Point N l)} {g : Point N l → ZMod N}
    (h : LocalPieceFor c w Dom g)
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t)) (m : Nat) :
    LocalPieceFor (liftLastC^[m] c) (liftLastW^[m] w)
      (prefixDomain (Nat.le_add_right l m) Dom)
      (fun z => g (coordinatePrefix (Nat.le_add_right l m) z)) := by
  induction m with
  | zero =>
    refine h.congr ?_ (fun z => by rw [coordinatePrefix_self])
    ext z
    rw [mem_prefixDomain, coordinatePrefix_self]
  | succ m ih =>
    have h1 := ih.lift_last (Nat.add_pos_left hl m) (liftLastC_iterate_pos_le hc m)
      (liftLastW_iterate_mono hw m)
    have hpre : ∀ z : Point N (l + (m + 1)),
        coordinatePrefix (Nat.le_add_right l m) (section16Init z) =
          coordinatePrefix (Nat.le_add_right l (m + 1)) z := by
      intro z
      funext i
      exact congrArg z (Fin.ext rfl)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine h1.congr ?_ (fun z => by rw [hpre])
    ext z
    simp only [mem_prefixDomain, Finset.mem_filter, Finset.mem_univ, true_and, hpre]

/-- **Any embedded set of active coordinates.** -/
theorem LocalPieceFor.lift_embedding {N l d : Nat} [NeZero N] [Fact N.Prime] (hl : 0 < l)
    {c : Real → Real} {w : Real → Nat → Nat} {Dom : Finset (Point N l)} {g : Point N l → ZMod N}
    (h : LocalPieceFor c w Dom g)
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    (f : Fin l ↪ Fin d) :
    LocalPieceFor (liftLastC^[d - l] c) (liftLastW^[d - l] w) (selectedDomain f Dom)
      (fun z => g (selectedCoordinates f z)) := by
  have hld : l ≤ d := by simpa using Fintype.card_le_of_injective f f.injective
  obtain ⟨m, rfl⟩ : ∃ m, d = l + m := ⟨d - l, by omega⟩
  rw [Nat.add_sub_cancel_left]
  obtain ⟨sigma, hsigma⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin l => i.castLE (Nat.le_add_right l m)) f (Fin.castLE_injective _) f.injective
  have hp := (h.lift_prefix hl hc hw m).reindex sigma
  have hinv : ∀ z : Point N (l + m),
      coordinatePrefix (Nat.le_add_right l m) (coordinateReindex sigma z) =
        selectedCoordinates f z := by
    intro z
    funext i
    exact congrArg z (hsigma i)
  refine hp.congr ?_ (fun z => by rw [hinv])
  ext z
  simp only [mem_selectedDomain, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_prefixDomain, hinv]

/-- The density after nesting `r` providers. -/
def nestC (c : Nat → Real → Real) : Nat → Real → Real
  | 0 => id
  | r + 1 => fun t => c r (nestC c r t)

/-- The width after nesting `r` providers. -/
def nestW (c : Nat → Real → Real) (w : Nat → Real → Nat → Nat) : Nat → Real → Nat → Nat
  | 0 => fun _ L => L
  | r + 1 => fun t L => w r (nestC c r t) (nestW c w r t L)

theorem nestC_pos_le {c : Nat → Real → Real}
    (hc : ∀ i t, 0 < t → t ≤ 1 → 0 < c i t ∧ c i t ≤ 1) (r : Nat) :
    ∀ t, 0 < t → t ≤ 1 → 0 < nestC c r t ∧ nestC c r t ≤ 1 := by
  induction r with
  | zero => intro t ht ht1; exact ⟨ht, ht1⟩
  | succ r ih =>
    intro t ht ht1
    obtain ⟨h1, h2⟩ := ih t ht ht1
    exact hc r _ h1 h2

/-- **Simultaneous pieces.** Nesting providers for `g 0, …, g (r−1)` gives
one sub-box on which all of them agree with multilinear maps at once. -/
theorem LocalPieceFor.simultaneous {N n : Nat} [NeZero N] {c : Nat → Real → Real}
    {w : Nat → Real → Nat → Nat} {Dom : Nat → Finset (Point N n)}
    {g : Nat → Point N n → ZMod N} (r : Nat)
    (h : ∀ i < r, LocalPieceFor (c i) (w i) (Dom i) (g i))
    (hc : ∀ i t, 0 < t → t ≤ 1 → 0 < c i t ∧ c i t ≤ 1) (hw : ∀ i t, Monotone (w i t))
    {theta : Real} (hθ : 0 < theta) (hθ1 : theta ≤ 1)
    (P : Box N n) (H : Finset (Point N n)) (hP : P.IsProper) (hHP : H ⊆ P.carrier)
    (hHD : ∀ i < r, H ⊆ Dom i) (hHc : theta * P.carrier.card ≤ H.card) :
    ∃ (R : Box N n) (mu : Nat → Point N n → ZMod N),
      R.IsProper ∧ R.carrier ⊆ P.carrier ∧ nestW c w r theta P.width ≤ R.width ∧
      (∀ i < r, IsMultilinear (mu i)) ∧
      nestC c r theta * R.carrier.card ≤
        (H.filter fun x => x ∈ R.carrier ∧ ∀ i < r, g i x = mu i x).card := by
  induction r with
  | zero =>
    refine ⟨P, fun _ _ => 0, hP, Finset.Subset.refl _, le_rfl, fun i hi => absurd hi
      (Nat.not_lt_zero i), ?_⟩
    rw [Finset.filter_true_of_mem fun x hx => ⟨hHP hx, fun i hi => absurd hi (Nat.not_lt_zero i)⟩]
    exact hHc
  | succ r ih =>
    obtain ⟨R, mu, hR, hRP, hRw, hmu, hRc⟩ := ih (fun i hi => h i (by omega))
      (fun i hi => hHD i (by omega))
    set Hr := H.filter fun x => x ∈ R.carrier ∧ ∀ i < r, g i x = mu i x with hHrdef
    obtain ⟨hcpos, hcle⟩ := nestC_pos_le hc r theta hθ hθ1
    obtain ⟨R2, nu, hR2, hR2R, hR2w, hnu, hR2c⟩ := h r (by omega) (nestC c r theta) hcpos hcle
      R Hr hR (fun x hx => (Finset.mem_filter.mp hx).2.1)
      (fun x hx => hHD r (by omega) (Finset.mem_filter.mp hx).1) hRc
    refine ⟨R2, fun i => if i = r then nu else mu i, hR2, hR2R.trans hRP, ?_, ?_, ?_⟩
    · exact (hw r _ hRw).trans hR2w
    · intro i hi
      dsimp only
      split_ifs with hir
      · exact hnu
      · exact hmu i (by omega)
    · refine hR2c.trans ?_
      exact_mod_cast Finset.card_le_card fun x hx => by
        obtain ⟨hxHr, hxR2, hxg⟩ := Finset.mem_filter.mp hx
        obtain ⟨hxH, -, hxmu⟩ := Finset.mem_filter.mp hxHr
        refine Finset.mem_filter.mpr ⟨hxH, hxR2, fun i hi => ?_⟩
        dsimp only
        split_ifs with hir
        · subst hir; exact hxg
        · exact hxmu i (by omega)

/-- Finite sums of multilinear maps are multilinear. -/
theorem IsMultilinear.finset_sum {N n : Nat} {ι : Type*} (s : Finset ι)
    (f : ι → Point N n → ZMod N) (hf : ∀ i ∈ s, IsMultilinear (f i)) :
    IsMultilinear (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isMultilinear_constant (N := N) (d := n) 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end LeanProofs.GowersSzemeredi
