import GowersSzemeredi.Proofs16AbstractBSGWords
import GowersSzemeredi.Proofs16ColumnListSpectrum

/-! Bounded-image quadruple relations propagate through compatible words.
The image bound costs two relation factors per splice. It is independent
of the number of words and requires no packing of local linear models. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Restricting a domain and replacing a function by an equal function
cannot increase its finite image cardinality. -/
theorem image_card_le_of_eq_on_subset {V H : Type*} [DecidableEq H]
    (S U : Finset V) (f g : V → H) (hSU : S ⊆ U) (he : ∀ x ∈ S, f x = g x) :
    (S.image f).card ≤ (U.image g).card := by
  apply Finset.card_le_card
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨x, hSU hx, (he x hx).symm⟩

/-- A sum of three defects takes at most the product of their image sizes. -/
theorem image_three_defects_card_le {V H : Type*} [AddCommGroup H] [DecidableEq H]
    (S : Finset V) (f g h t : V → H) (he : ∀ x ∈ S, f x = g x - h x - t x)
    {m1 m2 m3 : Nat} (hg : (S.image g).card ≤ m1)
    (hh : (S.image h).card ≤ m2) (ht : (S.image t).card ≤ m3) :
    (S.image f).card ≤ m1*m2*m3 := by
  let P := S.image g ×ˢ S.image h ×ˢ S.image t
  have hsub : S.image f ⊆ P.image (fun p => p.1-p.2.1-p.2.2) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨(g x, h x, t x), Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem g hx, Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem h hx, Finset.mem_image_of_mem t hx⟩⟩, (he x hx).symm⟩
  calc (S.image f).card ≤ (P.image (fun p => p.1-p.2.1-p.2.2)).card := Finset.card_le_card hsub
    _ ≤ P.card := Finset.card_image_le
    _ = (S.image g).card*(S.image h).card*(S.image t).card := by
      simp only [P, Finset.card_product, Nat.mul_assoc]
    _ ≤ _ := by gcongr

def columnQuadDefect {N : Nat} (L : ZMod N → ZMod N → ZMod N)
    (a b c d y : ZMod N) : ZMod N := L a y-L b y-L c y+L d y

def columnQuadCommonDomain {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (r : Real) (a b c d : ZMod N) : Finset (ZMod N) :=
  Finset.univ.filter fun y => y ∈ bohr (T a) r ∧ y ∈ bohr (T b) r ∧
    y ∈ bohr (T c) r ∧ y ∈ bohr (T d) r

/-- A quadruple relation can be bounded image instead of exact vanishing. -/
def ColumnQuadImageRelation {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (M : Nat) (a b c d : ZMod N) : Prop :=
  ((columnQuadCommonDomain T r a b c d).image (columnQuadDefect L a b c d)).card ≤ M

def relationWordCommonDomain {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (r : Real) (as : List (ZMod N))
    (w : ColumnWord N as.length) : Finset (ZMod N) :=
  Finset.univ.filter fun y => columnWordDomain T r as w y

abbrev relationWordDefect {N : Nat} (L : ZMod N → ZMod N → ZMod N)
    (as : List (ZMod N)) (w : ColumnWord N as.length) (y : ZMod N) : ZMod N :=
  columnRepresentationDefect L as w y

/-- Every compatible word of `ell` triples has defect image at most
`M^(2*ell-1)` on its actual recursive common domain. -/
theorem relation_word_defect_image_card_le {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (M : Nat)
    (a : ZMod N) (as : List (ZMod N)) (w : ColumnWord N (a::as).length)
    (hw : w ∈ relationWordRepresentations B (ColumnQuadImageRelation T L r M) (a::as)) :
    ((relationWordCommonDomain T r (a::as) w).image
      (relationWordDefect L (a::as) w)).card ≤ M^(2*as.length+1) := by
  induction as generalizing a with
  | nil =>
    have hR := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).2).2.2
    change ((columnQuadCommonDomain T r a w.1.1 w.1.2.2 w.1.2.1).image
      (columnQuadDefect L a w.1.1 w.1.2.2 w.1.2.1)).card ≤ M at hR
    have hle := image_card_le_of_eq_on_subset
      (relationWordCommonDomain T r [a] w)
      (columnQuadCommonDomain T r a w.1.1 w.1.2.2 w.1.2.1)
      (relationWordDefect L [a] w) (columnQuadDefect L a w.1.1 w.1.2.2 w.1.2.1)
      (by
        intro y hy
        have hd := (Finset.mem_filter.mp hy).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd.1, hd.2.1, hd.2.2.2, hd.2.2.1⟩)
      (by intro y _; simp only [relationWordDefect, columnRepresentationDefect, columnAnchorEval, columnWordEval,
          columnQuadDefect]; ring)
    simpa using hle.trans hR
  | cons b as ih =>
    let p := columnWordUnsplice a (columnAnchorEval id (b::as)) w
    obtain ⟨_, hyrep, hzrep, hqrep⟩ := Finset.mem_filter.mp hw
    have hRt := (Finset.mem_filter.mp hyrep).2.2
    have hRq := (Finset.mem_filter.mp hqrep).2.2.2.2.2.2
    have htail := ih b p.2.2 hzrep
    let D := relationWordCommonDomain T r (a::b::as) w
    let f := relationWordDefect L (a::b::as) w
    let g := columnQuadDefect L a p.2.1.1 p.2.1.2.2 p.2.1.2.1
    let h := relationWordDefect L (b::as) p.2.2
    let t := columnQuadDefect L (p.1 0) (p.1 2) (p.1 3) (p.1 1)
    have hg : (D.image g).card ≤ M := by
      apply (image_card_le_of_eq_on_subset D
        (columnQuadCommonDomain T r a p.2.1.1 p.2.1.2.2 p.2.1.2.1) g g ?_
        (fun _ _ => rfl)).trans hRt
      intro y hy
      have hd := (Finset.mem_filter.mp hy).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd.1.1, hd.1.2.1,
        hd.1.2.2.2, hd.1.2.2.1⟩
    have hh : (D.image h).card ≤ M^(2*as.length+1) := by
      apply (image_card_le_of_eq_on_subset D (relationWordCommonDomain T r (b::as) p.2.2)
        h h ?_ (fun _ _ => rfl)).trans htail
      intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2.2.1⟩
    have ht : (D.image t).card ≤ M := by
      apply (image_card_le_of_eq_on_subset D
        (columnQuadCommonDomain T r (p.1 0) (p.1 2) (p.1 3) (p.1 1)) t t ?_
        (fun _ _ => rfl)).trans hRq
      intro y hy
      have hd := (Finset.mem_filter.mp hy).2.2.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd 0, hd 2, hd 3, hd 1⟩
    have he : ∀ y ∈ D, f y = g y-h y-t y := by
      intro y _
      change (L a y-columnAnchorEval (fun x => L x y) (b::as)) -
        (L w.1.1 y-L w.1.2.1 y+L w.1.2.2 y-
          (L w.2.1.1 y-L w.2.1.2.1 y+L w.2.1.2.2 y-columnWordEval (fun x => L x y) w.2.2)) =
        (L a y-L w.1.1 y-L p.2.1.2.2 y+L w.1.2.1 y) -
        (columnAnchorEval (fun x => L x y) (b::as) -
          (L p.2.2.1.1 y-L w.2.1.2.1 y+L w.2.1.2.2 y-columnWordEval (fun x => L x y) w.2.2)) -
        (L w.1.2.2 y-L p.2.1.2.2 y-L w.2.1.1 y+L p.2.2.1.1 y)
      ring
    have hcount := image_three_defects_card_le D f g h t he hg hh ht
    have hpow : M*M^(2*as.length+1)*M = M^(2*(b::as).length+1) := by
      simp only [List.length_cons]
      rw [Nat.mul_comm M (M^(2*as.length+1)), ←pow_succ, ←pow_succ]
      congr 1
    simpa only [D, f, hpow] using hcount

/-- Strengthening the permitted relation preserves every compatible word. -/
theorem relationWordRepresentations_mono {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (R S : ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    (hRS : ∀ a b c d, R a b c d → S a b c d) :
    ∀ as : List (ZMod N), relationWordRepresentations B R as ⊆ relationWordRepresentations B S as := by
  intro as
  induction as with
  | nil => intro w _; exact Finset.mem_univ w
  | cons a as ih =>
    cases as with
    | nil =>
      intro w hw
      obtain ⟨hm, he, hr⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hw).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hm, he, hRS _ _ _ _ hr⟩⟩
    | cons b as =>
      intro w hw
      obtain ⟨_, hy, hz, hq⟩ := Finset.mem_filter.mp hw
      obtain ⟨hym, hye, hyr⟩ := Finset.mem_filter.mp hy
      obtain ⟨_, h0, h2, h1, h3, hqe, hqr⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hym, hye, hRS _ _ _ _ hyr⟩, ih hz,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0, h2, h1, h3, hqe, hRS _ _ _ _ hqr⟩⟩

/-- The image estimate applies to any relation implying the image bound. -/
theorem relation_word_defect_image_card_le_of_relation {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (M : Nat)
    (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    (hR : ∀ a b c d, R a b c d → ColumnQuadImageRelation T L r M a b c d)
    (a : ZMod N) (as : List (ZMod N)) (w : ColumnWord N (a::as).length)
    (hw : w ∈ relationWordRepresentations B R (a::as)) :
    ((relationWordCommonDomain T r (a::as) w).image
      (relationWordDefect L (a::as) w)).card ≤ M^(2*as.length+1) :=
  relation_word_defect_image_card_le B T L r M a as w
    (relationWordRepresentations_mono B R (ColumnQuadImageRelation T L r M) hR (a::as) hw)

end LeanProofs.GowersSzemeredi
