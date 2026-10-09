import GowersSzemeredi.Proofs16Lemma19TwoNew

/-! One step of [49] Corollary 20 in `ℤ/N`.

arXiv:2109.03093, Corollary 20, builds Freiman maps `L_i` by iterating
Lemma 19 from the zero map. A family `(E_i, L_i)` covers the values
`cov(x) = {0} ∪ {L_i x : x ∈ E_i, L_i x ∈ U_x}`. A triple `(y, z, w)` is *bad*
when some witness `h = a − b = c − d`, with `a ∈ U_{y+z}`, `b ∈ U_z`,
`c ∈ U_{y+w}`, `d ∈ U_w`, lies outside
`(cov(y+z) − cov(z)) + (cov(y+w) − cov(w))`. Only triples with four
distinct points are counted. The others number `O(N²)`, and excluding them
makes witness values consistent.

`corollary20_step`: if at least `εN³` triples are bad, a new Freiman piece
`(E′, f)` exists, with `f x ∈ U_x ∖ cov(x)` on `E′` and
`|E′| ≥ corollary20Kappa ε K · N`. The proof:
* in a bad witness, `0 ∈ cov` forces one of `a, b` and one of `c, d` to be
  new (`bad_witness_new`);
* pigeonhole into the four cases (b,d), (a,c), (a,d), (b,c);
* each case maps its triples injectively to quadruples, with the triple
  recovered from the quadruple;
* (b,d) and (a,c) use `lemma19_two_new_piece`; (a,d) and (b,c) use
  `lemma19_mixed_piece`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

variable {N : Nat} [NeZero N]

/-- The values covered by a family of maps at `x`. -/
def covSet (U : ZMod N → Finset (ZMod N)) {m : Nat} (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (x : ZMod N) : Finset (ZMod N) :=
  insert 0 ((Finset.univ.filter fun i => x ∈ E i ∧ L i x ∈ U x).image fun i => L i x)

/-- `h` lies in `(cov(y+z) − cov(z)) + (cov(y+w) − cov(w))`. -/
def InCovSum (U : ZMod N → Finset (ZMod N)) {m : Nat} (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (y z w h : ZMod N) : Prop :=
  ∃ a' ∈ covSet U E L (y + z), ∃ b' ∈ covSet U E L z, ∃ c' ∈ covSet U E L (y + w),
    ∃ d' ∈ covSet U E L w, h = (a' - b') + (c' - d')

/-- The four points of a triple are distinct. -/
def DistinctTriple (t : ZMod N × ZMod N × ZMod N) : Prop :=
  t.2.1 ≠ t.2.2 ∧ t.1 ≠ 0 ∧ t.1 + t.2.1 ≠ t.2.2 ∧ t.2.1 ≠ t.1 + t.2.2

/-- A bad witness for a triple. -/
def BadWitness (U : ZMod N → Finset (ZMod N)) {m : Nat} (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (t : ZMod N × ZMod N × ZMod N) (v : Fin 4 → ZMod N) : Prop :=
  v 0 ∈ U (t.1 + t.2.1) ∧ v 1 ∈ U t.2.1 ∧ v 2 ∈ U (t.1 + t.2.2) ∧ v 3 ∈ U t.2.2 ∧
    v 0 - v 1 = v 2 - v 3 ∧ ¬ InCovSum U E L t.1 t.2.1 t.2.2 (v 0 - v 1)

/-- A bad triple: distinct points with a bad witness. -/
def IsBadTriple (U : ZMod N → Finset (ZMod N)) {m : Nat} (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (t : ZMod N × ZMod N × ZMod N) : Prop :=
  DistinctTriple t ∧ ∃ v, BadWitness U E L t v

omit [NeZero N] in
theorem zero_mem_covSet (U : ZMod N → Finset (ZMod N)) {m : Nat} (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (x : ZMod N) : (0 : ZMod N) ∈ covSet U E L x :=
  Finset.mem_insert_self _ _

omit [NeZero N] in
/-- In a bad witness, one of each pair is new. -/
theorem bad_witness_new (U : ZMod N → Finset (ZMod N)) {m : Nat} (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) {t : ZMod N × ZMod N × ZMod N} {v : Fin 4 → ZMod N}
    (h : BadWitness U E L t v) :
    (v 0 ∉ covSet U E L (t.1 + t.2.1) ∨ v 1 ∉ covSet U E L t.2.1) ∧
      (v 2 ∉ covSet U E L (t.1 + t.2.2) ∨ v 3 ∉ covSet U E L t.2.2) := by
  obtain ⟨_, _, _, _, hrel, hnot⟩ := h
  constructor
  · by_contra hc
    push Not at hc
    exact hnot ⟨v 0, hc.1, v 1, hc.2, 0, zero_mem_covSet U E L _, 0, zero_mem_covSet U E L _,
      by ring⟩
  · by_contra hc
    push Not at hc
    exact hnot ⟨0, zero_mem_covSet U E L _, 0, zero_mem_covSet U E L _, v 2, hc.1, v 3, hc.2,
      by rw [hrel]; ring⟩

/-- The constant of one step. -/
def corollary20Kappa (ε : Real) (K : Nat) : Real :=
  (2 : Real) ^ (-(1882 : Real)) * ((ε / (1024 * K ^ 4)) ^ 2) ^ 1164

/-- The new-value sets. -/
def newValues (U : ZMod N → Finset (ZMod N)) {m : Nat} (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (x : ZMod N) : Finset (ZMod N) :=
  (U x).filter fun u => u ∉ covSet U E L x

omit [NeZero N] in
/-- Four distinct points of a distinct triple. -/
theorem distinct_points {t : ZMod N × ZMod N × ZMod N} (h : DistinctTriple t) :
    t.1 + t.2.1 ≠ t.2.1 ∧ t.1 + t.2.1 ≠ t.1 + t.2.2 ∧ t.1 + t.2.1 ≠ t.2.2 ∧
      t.2.1 ≠ t.1 + t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ t.1 + t.2.2 ≠ t.2.2 := by
  obtain ⟨hzw, hy, hyzw, hzyw⟩ := h
  refine ⟨fun e => hy ?_, fun e => hzw (add_left_cancel e), hyzw, hzyw, hzw, fun e => hy ?_⟩
  · have := congrArg (· - t.2.1) e; simpa using this
  · have := congrArg (· - t.2.2) e; simpa using this

omit [NeZero N] in
/-- Injectivity of a quadruple from six pairwise inequalities. -/
theorem quad_injective {p₀ p₁ p₂ p₃ : ZMod N}
    (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂) (h03 : p₀ ≠ p₃) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃)
    (h23 : p₂ ≠ p₃) {v : Fin 4 → ZMod N} :
    ∀ i j, (![p₀, p₁, p₂, p₃] : Fin 4 → ZMod N) i = ![p₀, p₁, p₂, p₃] j → v i = v j := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

omit [NeZero N] in
/-- The scaling `δ = ε/(1024K⁴)` used in every case. -/
theorem corollary20_scaling {ε : Real} {K : Nat} (hK1 : 1 ≤ K) :
    ε / (1024 * K ^ 4) * (N : Real) ^ 3 * (256 * K ^ 4) = ε / 4 * (N : Real) ^ 3 := by
  have hK : (K : Real) ^ 4 ≠ 0 := by
    have : (1 : Real) ≤ K := by exact_mod_cast hK1
    positivity
  field_simp
  ring

/-- A case handled by `lemma19_two_new_piece`. -/
theorem case_two_new [Fact N.Prime] (U : ZMod N → Finset (ZMod N)) (hne : ∀ x, (U x).Nonempty)
    {K : Nat} (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K)
    {m : Nat} (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N) {ε : Real} (hε : 0 < ε)
    (T : Finset (Fin 4 → ZMod N)) (val : (Fin 4 → ZMod N) → Fin 4 → ZMod N)
    (hadd : ∀ q ∈ T, q 0 - q 2 = q 1 - q 3 ∧ val q 0 - val q 2 = val q 1 - val q 3)
    (hU : ∀ q ∈ T, ∀ i, val q i ∈ U (q i))
    (hW : ∀ q ∈ T, val q 1 ∈ newValues U E L (q 1) ∧ val q 3 ∈ newValues U E L (q 3))
    (hcons : ∀ q ∈ T, ∀ i j, q i = q j → val q i = val q j)
    (hT : ε / 4 * (N : Real) ^ 3 ≤ T.card) :
    ∃ (f : ZMod N → ZMod N) (E' : Finset (ZMod N)),
      (∀ x ∈ E', f x ∈ U x ∧ f x ∉ covSet U E L x) ∧
      corollary20Kappa ε K * N ≤ E'.card ∧ IsFreimanLinearOn E' f := by
  have hδ : 0 < ε / (1024 * K ^ 4) := by
    have : (1 : Real) ≤ K := by exact_mod_cast hK1
    positivity
  obtain ⟨f, _, E', hE'W, hcard, hF⟩ := lemma19_two_new_piece U (newValues U E L) hne hK1 hK T val
    hadd hU hW hcons hδ (by rw [corollary20_scaling hK1]; exact hT)
  exact ⟨f, E', fun x hx => Finset.mem_filter.mp (hE'W x hx), hcard, hF⟩

/-- A case handled by `lemma19_mixed_piece`. -/
theorem case_mixed [Fact N.Prime] (U : ZMod N → Finset (ZMod N)) (hne : ∀ x, (U x).Nonempty)
    {K : Nat} (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K)
    {m : Nat} (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N) {ε : Real} (hε : 0 < ε)
    (T : Finset (Fin 4 → ZMod N)) (val : (Fin 4 → ZMod N) → Fin 4 → ZMod N)
    (hadd : ∀ q ∈ T, q 0 - q 1 = q 2 - q 3 ∧ val q 0 - val q 1 = val q 2 - val q 3)
    (hU : ∀ q ∈ T, ∀ i, val q i ∈ U (q i))
    (hW : ∀ q ∈ T, val q 0 ∈ newValues U E L (q 0) ∧ val q 3 ∈ newValues U E L (q 3))
    (hcons : ∀ q ∈ T, ∀ i j, q i = q j → val q i = val q j)
    (hT : ε / 4 * (N : Real) ^ 3 ≤ T.card) :
    ∃ (f : ZMod N → ZMod N) (E' : Finset (ZMod N)),
      (∀ x ∈ E', f x ∈ U x ∧ f x ∉ covSet U E L x) ∧
      corollary20Kappa ε K * N ≤ E'.card ∧ IsFreimanLinearOn E' f := by
  have hδ : 0 < ε / (1024 * K ^ 4) := by
    have : (1 : Real) ≤ K := by exact_mod_cast hK1
    positivity
  obtain ⟨f, _, E', hE'W, hcard, hF⟩ := lemma19_mixed_piece U (newValues U E L) hne hK1 hK T val
    hadd hU hW hcons hδ (by rw [corollary20_scaling hK1]; exact hT)
  exact ⟨f, E', fun x hx => Finset.mem_filter.mp (hE'W x hx), hcard, hF⟩

/-- **One step of [49] Corollary 20.** -/
theorem corollary20_step [Fact N.Prime] (U : ZMod N → Finset (ZMod N))
    (h0 : ∀ x, (0 : ZMod N) ∈ U x) {K : Nat} (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K)
    {m : Nat} (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N)
    {ε : Real} (hε : 0 < ε)
    (hbad : ε * (N : Real) ^ 3 ≤ ((Finset.univ.filter (IsBadTriple U E L)).card : Real)) :
    ∃ (f : ZMod N → ZMod N) (E' : Finset (ZMod N)),
      (∀ x ∈ E', f x ∈ U x ∧ f x ∉ covSet U E L x) ∧
      corollary20Kappa ε K * N ≤ E'.card ∧ IsFreimanLinearOn E' f := by
  have hne : ∀ x, (U x).Nonempty := fun x => ⟨0, h0 x⟩
  set bad := Finset.univ.filter (IsBadTriple U E L) with hbaddef
  let wit : ZMod N × ZMod N × ZMod N → Fin 4 → ZMod N := fun t =>
    if h : ∃ v, BadWitness U E L t v then h.choose else 0
  have hwit : ∀ t ∈ bad, BadWitness U E L t (wit t) := by
    intro t ht
    have h := (Finset.mem_filter.mp ht).2.2
    simp only [wit, dif_pos h]
    exact h.choose_spec
  have hdist : ∀ t ∈ bad, DistinctTriple t := fun t ht => (Finset.mem_filter.mp ht).2.1
  let B₁ := bad.filter fun t => wit t 1 ∉ covSet U E L t.2.1 ∧ wit t 3 ∉ covSet U E L t.2.2
  let B₂ := bad.filter fun t =>
    wit t 0 ∉ covSet U E L (t.1 + t.2.1) ∧ wit t 2 ∉ covSet U E L (t.1 + t.2.2)
  let B₃ := bad.filter fun t => wit t 0 ∉ covSet U E L (t.1 + t.2.1) ∧ wit t 3 ∉ covSet U E L t.2.2
  let B₄ := bad.filter fun t => wit t 1 ∉ covSet U E L t.2.1 ∧ wit t 2 ∉ covSet U E L (t.1 + t.2.2)
  have hcover : bad ⊆ B₁ ∪ B₂ ∪ B₃ ∪ B₄ := by
    intro t ht
    obtain ⟨hab, hcd⟩ := bad_witness_new U E L (hwit t ht)
    simp only [Finset.mem_union, B₁, B₂, B₃, B₄, Finset.mem_filter]
    rcases hab with ha | hb <;> rcases hcd with hc | hd
    · exact Or.inl (Or.inl (Or.inr ⟨ht, ha, hc⟩))
    · exact Or.inl (Or.inr ⟨ht, ha, hd⟩)
    · exact Or.inr ⟨ht, hb, hc⟩
    · exact Or.inl (Or.inl (Or.inl ⟨ht, hb, hd⟩))
  -- pigeonhole: one case carries a quarter of the bad triples
  have hsum : (bad.card : Real) ≤ B₁.card + B₂.card + B₃.card + B₄.card := by
    have h1 := Finset.card_le_card hcover
    have h2 : (B₁ ∪ B₂ ∪ B₃ ∪ B₄).card ≤ B₁.card + B₂.card + B₃.card + B₄.card := by
      calc (B₁ ∪ B₂ ∪ B₃ ∪ B₄).card ≤ (B₁ ∪ B₂ ∪ B₃).card + B₄.card := Finset.card_union_le _ _
        _ ≤ (B₁ ∪ B₂).card + B₃.card + B₄.card := by
            have := Finset.card_union_le (B₁ ∪ B₂) B₃; omega
        _ ≤ B₁.card + B₂.card + B₃.card + B₄.card := by
            have := Finset.card_union_le B₁ B₂; omega
    exact_mod_cast h1.trans h2
  -- encoders and decoders
  let enc₁ : ZMod N × ZMod N × ZMod N → Fin 4 → ZMod N := fun t => ![t.1 + t.2.1, t.2.1, t.1 + t.2.2, t.2.2]
  let dec₁ : (Fin 4 → ZMod N) → ZMod N × ZMod N × ZMod N := fun q => (q 0 - q 1, q 1, q 3)
  have hdec₁ : ∀ t, dec₁ (enc₁ t) = t := by intro t; ext <;> simp [dec₁, enc₁]
  let enc₂ : ZMod N × ZMod N × ZMod N → Fin 4 → ZMod N := fun t => ![t.2.1, t.1 + t.2.1, t.2.2, t.1 + t.2.2]
  let dec₂ : (Fin 4 → ZMod N) → ZMod N × ZMod N × ZMod N := fun q => (q 1 - q 0, q 0, q 2)
  have hdec₂ : ∀ t, dec₂ (enc₂ t) = t := by intro t; ext <;> simp [dec₂, enc₂]
  let enc₄ : ZMod N × ZMod N × ZMod N → Fin 4 → ZMod N := fun t => ![t.1 + t.2.2, t.2.2, t.1 + t.2.1, t.2.1]
  let dec₄ : (Fin 4 → ZMod N) → ZMod N × ZMod N × ZMod N := fun q => (q 0 - q 1, q 3, q 1)
  have hdec₄ : ∀ t, dec₄ (enc₄ t) = t := by intro t; ext <;> simp [dec₄, enc₄]
  have hcardimg : ∀ (B : Finset (ZMod N × ZMod N × ZMod N)) (enc : ZMod N × ZMod N × ZMod N → Fin 4 → ZMod N)
      (dec : (Fin 4 → ZMod N) → ZMod N × ZMod N × ZMod N), (∀ t, dec (enc t) = t) →
      (B.image enc).card = B.card := by
    intro B enc dec h
    apply Finset.card_image_of_injOn
    intro a _ b _ hab
    have := congrArg dec hab
    rwa [h, h] at this
  have hq : ε / 4 * (N : Real) ^ 3 ≤ B₁.card ∨ ε / 4 * (N : Real) ^ 3 ≤ B₂.card ∨
      ε / 4 * (N : Real) ^ 3 ≤ B₃.card ∨ ε / 4 * (N : Real) ^ 3 ≤ B₄.card := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3, h4⟩ := hcon
    linarith
  rcases hq with h1 | h2 | h3 | h4
  · -- case (b, d): `lemma19_two_new_piece` on `(y+z, z, y+w, w)`
    refine case_two_new U hne hK1 hK E L hε (B₁.image enc₁) (fun q => wit (dec₁ q)) ?_ ?_ ?_ ?_
      (by rw [hcardimg B₁ enc₁ dec₁ hdec₁]; exact h1)
    · intro q hq'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      simp only [hdec₁]
      obtain ⟨_, _, _, _, hrel, _⟩ := hwit t (Finset.mem_filter.mp ht).1
      exact ⟨by simp [enc₁], by linear_combination hrel⟩
    · intro q hq' i
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      simp only [hdec₁]
      obtain ⟨h0', h1', h2', h3', _, _⟩ := hwit t (Finset.mem_filter.mp ht).1
      fin_cases i <;> simpa [enc₁]
    · intro q hq'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      simp only [hdec₁]
      obtain ⟨htb, hn1, hn3⟩ := Finset.mem_filter.mp ht
      obtain ⟨_, h1', _, h3', _, _⟩ := hwit t htb
      exact ⟨Finset.mem_filter.mpr ⟨by simpa [enc₁], by simpa [enc₁]⟩,
        Finset.mem_filter.mpr ⟨by simpa [enc₁], by simpa [enc₁]⟩⟩
    · intro q hq'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := distinct_points (hdist t (Finset.mem_filter.mp ht).1)
      exact quad_injective d1 d2 d3 d4 d5 d6
  · -- case (a, c): `lemma19_two_new_piece` on `(z, y+z, w, y+w)`
    refine case_two_new U hne hK1 hK E L hε (B₂.image enc₂)
      (fun q => ![wit (dec₂ q) 1, wit (dec₂ q) 0, wit (dec₂ q) 3, wit (dec₂ q) 2]) ?_ ?_ ?_ ?_
      (by rw [hcardimg B₂ enc₂ dec₂ hdec₂]; exact h2)
    · intro q hq'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      simp only [hdec₂]
      obtain ⟨_, _, _, _, hrel, _⟩ := hwit t (Finset.mem_filter.mp ht).1
      exact ⟨by simp [enc₂], by simp; linear_combination -hrel⟩
    · intro q hq' i
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      simp only [hdec₂]
      obtain ⟨h0', h1', h2', h3', _, _⟩ := hwit t (Finset.mem_filter.mp ht).1
      fin_cases i <;> simpa [enc₂]
    · intro q hq'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      simp only [hdec₂]
      obtain ⟨htb, hn0, hn2⟩ := Finset.mem_filter.mp ht
      obtain ⟨h0', _, h2', _, _, _⟩ := hwit t htb
      exact ⟨Finset.mem_filter.mpr ⟨by simpa [enc₂], by simpa [enc₂]⟩,
        Finset.mem_filter.mpr ⟨by simpa [enc₂], by simpa [enc₂]⟩⟩
    · intro q hq'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := distinct_points (hdist t (Finset.mem_filter.mp ht).1)
      exact quad_injective (Ne.symm d1) d5 d4 d3 d2 (Ne.symm d6)
  · -- case (a, d): `lemma19_mixed_piece` on `(y+z, z, y+w, w)`
    refine case_mixed U hne hK1 hK E L hε (B₃.image enc₁) (fun q => wit (dec₁ q)) ?_ ?_ ?_ ?_
      (by rw [hcardimg B₃ enc₁ dec₁ hdec₁]; exact h3)
    · intro q hq'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      simp only [hdec₁]
      obtain ⟨_, _, _, _, hrel, _⟩ := hwit t (Finset.mem_filter.mp ht).1
      exact ⟨by simp [enc₁], hrel⟩
    · intro q hq' i
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      simp only [hdec₁]
      obtain ⟨h0', h1', h2', h3', _, _⟩ := hwit t (Finset.mem_filter.mp ht).1
      fin_cases i <;> simpa [enc₁]
    · intro q hq'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      simp only [hdec₁]
      obtain ⟨htb, hn0, hn3⟩ := Finset.mem_filter.mp ht
      obtain ⟨h0', _, _, h3', _, _⟩ := hwit t htb
      exact ⟨Finset.mem_filter.mpr ⟨by simpa [enc₁], by simpa [enc₁]⟩,
        Finset.mem_filter.mpr ⟨by simpa [enc₁], by simpa [enc₁]⟩⟩
    · intro q hq'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := distinct_points (hdist t (Finset.mem_filter.mp ht).1)
      exact quad_injective d1 d2 d3 d4 d5 d6
  · -- case (b, c): `lemma19_mixed_piece` on `(y+w, w, y+z, z)`
    refine case_mixed U hne hK1 hK E L hε (B₄.image enc₄)
      (fun q => ![wit (dec₄ q) 2, wit (dec₄ q) 3, wit (dec₄ q) 0, wit (dec₄ q) 1]) ?_ ?_ ?_ ?_
      (by rw [hcardimg B₄ enc₄ dec₄ hdec₄]; exact h4)
    · intro q hq'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      simp only [hdec₄]
      obtain ⟨_, _, _, _, hrel, _⟩ := hwit t (Finset.mem_filter.mp ht).1
      exact ⟨by simp [enc₄], by simp; linear_combination -hrel⟩
    · intro q hq' i
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      simp only [hdec₄]
      obtain ⟨h0', h1', h2', h3', _, _⟩ := hwit t (Finset.mem_filter.mp ht).1
      fin_cases i <;> simpa [enc₄]
    · intro q hq'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      simp only [hdec₄]
      obtain ⟨htb, hn1, hn2⟩ := Finset.mem_filter.mp ht
      obtain ⟨_, h1', h2', _, _, _⟩ := hwit t htb
      exact ⟨Finset.mem_filter.mpr ⟨by simpa [enc₄], by simpa [enc₄]⟩,
        Finset.mem_filter.mpr ⟨by simpa [enc₄], by simpa [enc₄]⟩⟩
    · intro q hq'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := distinct_points (hdist t (Finset.mem_filter.mp ht).1)
      exact quad_injective d6 (Ne.symm d2) (Ne.symm d4) (Ne.symm d3) (Ne.symm d5) d1

end LeanProofs.GowersSzemeredi
