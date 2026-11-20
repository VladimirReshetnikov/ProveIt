import FrameRelations
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/- The canonical-frame arithmetic proof and its Cartesian instance.
   The determinant and two squared-distance comparisons are shown to
   define inclusive affine betweenness over every linearly ordered field. -/
namespace PlanarIPRA.FrameRelations

section

variable {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

abbrev Plane (F : Type) := F × F

def orig : Plane F := (0, 0)
def unitX : Plane F := (1, 0)
def unitY : Plane F := (0, 1)
def onX (a : F) : Plane F := (a, 0)
def onY (a : F) : Plane F := (0, a)

structure CartesianCriteria (g : Geometry (Plane F)) : Prop where
  col : ∀ a b c, g.col a b c ↔
    (b.1-a.1)*(c.2-a.2) = (b.2-a.2)*(c.1-a.1)
  mid : ∀ a m b, g.mid a m b ↔
    2*m.1 = a.1+b.1 ∧ 2*m.2 = a.2+b.2

namespace CartesianCriteria

variable {g : Geometry (Plane F)} (h : CartesianCriteria g)
include h

theorem displacement_iff (a b c d : Plane F) :
    g.displacement a b c d ↔
      b.1-a.1 = d.1-c.1 ∧ b.2-a.2 = d.2-c.2 := by
  constructor
  · rintro ⟨m, h₁, h₂⟩
    obtain ⟨hx₁, hy₁⟩ := (h.mid ..).mp h₁
    obtain ⟨hx₂, hy₂⟩ := (h.mid ..).mp h₂
    constructor <;> linarith
  · rintro ⟨hx, hy⟩
    refine ⟨((a.1+d.1)/2, (a.2+d.2)/2), (h.mid ..).mpr ?_, (h.mid ..).mpr ?_⟩
    all_goals constructor <;> dsimp <;> linarith

theorem direction_iff (p q c d : Plane F) :
    g.direction p q c d ↔ c ≠ d ∧
      (d.1-c.1)*(q.2-p.2) = (d.2-c.2)*(q.1-p.1) := by
  constructor
  · rintro ⟨hne, e, he, hc⟩
    obtain ⟨hx, hy⟩ := (h.displacement_iff ..).mp he
    exact ⟨hne, by rw [hx, hy]; exact (h.col ..).mp hc⟩
  · rintro ⟨hne, hdet⟩
    refine ⟨hne, (p.1+(d.1-c.1), p.2+(d.2-c.2)),
      (h.displacement_iff ..).mpr ?_, (h.col ..).mpr ?_⟩
    · simp
    · simpa using hdet

def axis (a : F) : g.Axis orig unitX :=
  ⟨onX a, (h.col ..).mpr (by simp [onX, orig, unitX])⟩

theorem transfer_iff (a : F) (v : Plane F) :
    g.transfer orig unitX unitY (h.axis a) v ↔ v = onY a := by
  rcases v with ⟨x,y⟩
  unfold Geometry.transfer
  rw [h.col, h.direction_iff]
  change ((0-0)*(y-0) = (1-0)*(x-0) ∧
    ((1,0) : F × F) ≠ (0,1) ∧
    (0-1)*(y-0) = (1-0)*(x-a)) ↔ (x,y) = (0,a)
  constructor
  · rintro ⟨hx, _, hy⟩
    apply Prod.ext <;> dsimp <;> linarith
  · intro e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    simp

theorem add_iff (a b c : F) :
    g.add orig unitX (h.axis a) (h.axis b) (h.axis c) ↔ c = a+b := by
  unfold Geometry.add
  rw [h.displacement_iff]
  change (a-0 = c-b ∧ 0-0 = (0:F)-0) ↔ _
  constructor
  · rintro ⟨e, _⟩
    linarith
  · rintro rfl
    simp

theorem mul_iff (a b c : F) :
    g.mul orig unitX unitY (h.axis a) (h.axis b) (h.axis c) ↔ c = a*b := by
  constructor
  · rintro ⟨v, w, hv, hw, hd⟩
    rw [h.transfer_iff] at hv hw
    subst v
    subst w
    have e := ((h.direction_iff ..).mp hd).2
    change (0-1)*(c-0) = (b-0)*(0-a) at e
    nlinarith [e]
  · rintro rfl
    refine ⟨onY b, onY (a*b), (h.transfer_iff ..).mpr rfl,
      (h.transfer_iff ..).mpr rfl, (h.direction_iff ..).mpr ⟨?_,?_⟩⟩
    · intro he
      have e := congrArg Prod.fst he
      exact one_ne_zero (α := F) e
    · change (0-1)*(a*b-0) = (b-0)*(0-a)
      ring

theorem coords_iff (a b : F) (p : Plane F) :
    g.coords orig unitX unitY p (h.axis a, h.axis b) ↔ p = (a,b) := by
  constructor
  · rintro ⟨v, hv, hd⟩
    rw [h.transfer_iff] at hv
    subst v
    obtain ⟨hx, hy⟩ := (h.displacement_iff ..).mp hd
    change a-0 = p.1-0 at hx
    change 0-0 = p.2-b at hy
    apply Prod.ext <;> dsimp <;> linarith
  · rintro rfl
    refine ⟨onY b, (h.transfer_iff ..).mpr rfl, (h.displacement_iff ..).mpr ?_⟩
    change a-0 = a-0 ∧ 0-0 = b-b
    simp

end CartesianCriteria

/-- The two band inequalities are equivalent to the usual closed
    parameter interval on a collinear triple, including equal endpoints. -/
def det3 (a b c : Plane F) : F :=
  (b.1-a.1)*(c.2-a.2) - (b.2-a.2)*(c.1-a.1)

def sep2 (a b : Plane F) : F := (b.1-a.1)^2 + (b.2-a.2)^2

def cartesian : Geometry (Plane F) where
  bet a b c := det3 a b c = 0 ∧ sep2 a b ≤ sep2 a c ∧ sep2 b c ≤ sep2 a c
  cong a b c d := sep2 a b = sep2 c d

omit [LinearOrder F] [IsStrictOrderedRing F] in
private theorem cyclic (a b c : Plane F) : det3 a b c = det3 b c a := by
  unfold det3
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
private theorem sep_rev (a b : Plane F) : sep2 a b = sep2 b a := by
  unfold sep2
  ring

private theorem squares_zero {x y : F} (he : x^2+y^2 = 0) : x=0 ∧ y=0 := by
  constructor <;> apply sq_eq_zero_iff.mp <;> nlinarith [sq_nonneg x, sq_nonneg y]

omit [IsStrictOrderedRing F] in
theorem cartesian_col (a b c : Plane F) :
    cartesian.col a b c ↔ det3 a b c = 0 := by
  constructor
  · rintro (h|h|h)
    · exact h.1
    · rw [cyclic]
      exact h.1
    · rw [cyclic, cyclic b c a]
      exact h.1
  · intro h
    have hb : det3 b c a = 0 := (cyclic a b c) ▸ h
    have hc : det3 c a b = 0 := (cyclic b c a) ▸ hb
    by_cases hac : sep2 a b ≤ sep2 a c
    · by_cases hbc : sep2 b c ≤ sep2 a c
      · exact Or.inl ⟨h,hac,hbc⟩
      · have hcb := le_of_not_ge hbc
        right
        right
        refine ⟨hc,?_,?_⟩
        · simpa only [sep_rev c a, sep_rev c b] using hcb
        · simpa only [sep_rev c b] using hac.trans hcb
    · have hca := le_of_not_ge hac
      by_cases hbc : sep2 b c ≤ sep2 a b
      · right
        left
        refine ⟨hb,?_,?_⟩
        · simpa only [sep_rev b a] using hbc
        · simpa only [sep_rev c a, sep_rev b a] using hca
      · have hcb := le_of_not_ge hbc
        right
        right
        refine ⟨hc,?_,?_⟩
        · simpa only [sep_rev c a, sep_rev c b] using hca.trans hcb
        · simpa only [sep_rev c b] using hcb

theorem cartesian_mid (a m b : Plane F) : cartesian.mid a m b ↔
    2*m.1 = a.1+b.1 ∧ 2*m.2 = a.2+b.2 := by
  constructor
  · rintro ⟨⟨hdet, ham, _⟩, heq⟩
    change det3 a m b = 0 at hdet
    change sep2 a m ≤ sep2 a b at ham
    change sep2 a m = sep2 m b at heq
    by_cases he : a=b
    · subst b
      simp [sep2] at ham
      obtain ⟨hx, hy⟩ := squares_zero (le_antisymm ham
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      constructor <;> linarith
    · let dx := b.1-a.1
      let dy := b.2-a.2
      let rx := 2*m.1-a.1-b.1
      let ry := 2*m.2-a.2-b.2
      have hn : dx^2+dy^2 ≠ 0 := by
        intro hzero
        obtain ⟨hx,hy⟩ := squares_zero hzero
        apply he
        apply Prod.ext <;> dsimp [dx, dy] at * <;> linarith
      have ht : dx*ry-dy*rx = 0 := by
        dsimp [dx,dy,rx,ry]
        unfold det3 at hdet
        nlinarith only [hdet]
      have hs : dx*rx+dy*ry = 0 := by
        dsimp [dx,dy,rx,ry]
        unfold sep2 at heq
        nlinarith only [heq]
      have prodzero : (dx^2+dy^2)*(rx^2+ry^2) = 0 := calc
        _ = (dx*ry-dy*rx)^2+(dx*rx+dy*ry)^2 := by ring
        _ = 0 := by rw [ht,hs]; ring
      obtain ⟨hx,hy⟩ := squares_zero ((mul_eq_zero.mp prodzero).resolve_left hn)
      dsimp [rx,ry] at hx hy
      constructor <;> linarith
  · rintro ⟨hx,hy⟩
    have hm : m = ((a.1+b.1)/2,(a.2+b.2)/2) := by
      apply Prod.ext <;> dsimp <;> linarith
    subst m
    constructor
    · refine ⟨?_,?_,?_⟩
      · unfold det3
        dsimp
        ring
      · unfold sep2
        dsimp
        nlinarith [sq_nonneg (a.1-b.1),sq_nonneg (a.2-b.2)]
      · unfold sep2
        dsimp
        nlinarith [sq_nonneg (a.1-b.1),sq_nonneg (a.2-b.2)]
    · change sep2 _ _ = sep2 _ _
      unfold sep2
      dsimp
      ring

theorem cartesianCriteria : CartesianCriteria (cartesian (F := F)) where
  col a b c := (cartesian_col a b c).trans sub_eq_zero
  mid := cartesian_mid

/-- The affine-parameter version of closed betweenness. -/
def affineClosed (a m b : Plane F) : Prop :=
  ∃ t : F, 0 ≤ t ∧ t ≤ 1 ∧
    m.1=a.1+t*(b.1-a.1) ∧ m.2=a.2+t*(b.2-a.2)

private theorem parameter {a m b : Plane F} (hne : a ≠ b)
    (hdet : det3 a m b = 0) :
    ∃ t : F, m.1=a.1+t*(b.1-a.1) ∧ m.2=a.2+t*(b.2-a.2) := by
  unfold det3 at hdet
  by_cases hx : b.1-a.1=0
  · have hy : b.2-a.2 ≠ 0 := by
      intro hy
      apply hne
      apply Prod.ext <;> linarith
    rw [hx, mul_zero, sub_zero] at hdet
    have hmx := (mul_eq_zero.mp hdet).resolve_right hy
    refine ⟨(m.2-a.2)/(b.2-a.2),?_,?_⟩
    · rw [hx, mul_zero, add_zero]
      exact sub_eq_zero.mp hmx
    · field_simp [hy]
      ring
  · refine ⟨(m.1-a.1)/(b.1-a.1),?_,?_⟩
    · field_simp [hx]
      ring
    · field_simp [hx]
      nlinarith only [hdet]

omit [LinearOrder F] [IsStrictOrderedRing F] in
private theorem lengths {a m b : Plane F} {t : F}
    (hx : m.1=a.1+t*(b.1-a.1)) (hy : m.2=a.2+t*(b.2-a.2)) :
    sep2 a m=t^2*sep2 a b ∧ sep2 m b=(1-t)^2*sep2 a b := by
  unfold sep2
  rw [hx, hy]
  constructor <;> ring

theorem cartesian_between (a m b : Plane F) : cartesian.bet a m b ↔ affineClosed a m b := by
  constructor
  · rintro ⟨hdet, ham, hmb⟩
    by_cases he : a=b
    · subst b
      simp [sep2] at ham
      obtain ⟨hx,hy⟩ := squares_zero (le_antisymm ham (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      exact ⟨0, le_rfl, zero_le_one, by linarith, by linarith⟩
    · obtain ⟨t,hx,hy⟩ := parameter he hdet
      have hnon : 0<sep2 a b := by
        refine lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) ?_
        intro hz
        obtain ⟨h₁,h₂⟩ := squares_zero hz.symm
        apply he
        apply Prod.ext <;> linarith
      obtain ⟨h1,h2⟩ := lengths hx hy
      rw [h1] at ham
      rw [h2] at hmb
      have e1 : t^2 ≤ 1 := (mul_le_mul_iff_of_pos_right hnon).mp (by simpa using ham)
      have e2 : (1-t)^2 ≤ 1 := (mul_le_mul_iff_of_pos_right hnon).mp (by simpa using hmb)
      exact ⟨t, by nlinarith [sq_nonneg t], by nlinarith [sq_nonneg (t-1)], hx,hy⟩
  · rintro ⟨t, h0, h1, hx, hy⟩
    have hn : 0≤sep2 a b := add_nonneg (sq_nonneg _) (sq_nonneg _)
    obtain ⟨hs,ht⟩ := lengths hx hy
    refine ⟨?_,?_,?_⟩
    · unfold det3
      rw [hx,hy]
      ring
    · rw [hs]
      have hb : t^2 ≤ 1 := by nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
      simpa using mul_le_mul_of_nonneg_right hb hn
    · rw [ht]
      have hb : (1-t)^2 ≤ 1 := by nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
      simpa using mul_le_mul_of_nonneg_right hb hn

namespace CartesianCriteria

variable {g : Geometry (Plane F)} (h : CartesianCriteria g)
include h

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem axis_eta (x : g.Axis orig unitX) : h.axis x.val.1 = x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · have hy := (h.col ..).mp x.property
    change (1-0)*(x.val.2-0) = (0-0)*(x.val.1-0) at hy
    change 0 = x.val.2
    simpa using hy.symm

theorem coords_generic (p : Plane F) (xy : g.Axis orig unitX × g.Axis orig unitX) :
    g.coords orig unitX unitY p xy ↔ p=(xy.1.val.1,xy.2.val.1) := by
  obtain ⟨x,y⟩ := xy
  exact (h.axis_eta x) ▸ (h.axis_eta y) ▸ h.coords_iff x.val.1 y.val.1 p

theorem coords_bigraph : BiGraph (g.coords orig unitX unitY) where
  total p := ⟨(h.axis p.1,h.axis p.2), (h.coords_iff ..).mpr rfl⟩
  onto xy := ⟨(xy.1.val.1,xy.2.val.1), (h.coords_generic ..).mpr rfl⟩
  functional := by
    intro p xy xy' hp hq
    have e := ((h.coords_generic ..).mp hp).symm.trans ((h.coords_generic ..).mp hq)
    have ex := congrArg Prod.fst e
    have ey := congrArg Prod.snd e
    apply Prod.ext
    · exact (h.axis_eta _).symm.trans ((congrArg h.axis ex).trans (h.axis_eta _))
    · exact (h.axis_eta _).symm.trans ((congrArg h.axis ey).trans (h.axis_eta _))
  injective := by
    intro p q xy hp hq
    exact ((h.coords_generic ..).mp hp).trans ((h.coords_generic ..).mp hq).symm

end CartesianCriteria

theorem nonnegative_iff (a : F) :
    cartesian.nonnegative orig unitX (cartesianCriteria.axis a) ↔ 0≤a := by
  change (cartesian.bet orig (onX a) unitX ∨ cartesian.bet orig unitX (onX a)) ↔ _
  rw [cartesian_between, cartesian_between]
  constructor
  · rintro (⟨t, h0, _, hx, _⟩ | ⟨t,h0,_,hx,_⟩)
    · change a = 0 + t*(1-0) at hx
      linarith
    · change 1 = 0+t*(a-0) at hx
      by_contra h
      have hn := mul_nonpos_of_nonneg_of_nonpos h0 (le_of_not_ge h)
      linarith
  · intro h0
    by_cases h1 : a≤1
    · exact Or.inl ⟨a,h0,h1,by simp [orig,onX,unitX],by simp [orig,onX,unitX]⟩
    · have ha : 0<a := lt_trans zero_lt_one (lt_of_not_ge h1)
      refine Or.inr ⟨1/a, div_nonneg zero_le_one h0, ?_, ?_, ?_⟩
      · apply (div_le_iff₀ ha).mpr
        simpa using le_of_not_ge h1
      · simp [orig,onX,unitX,ne_of_gt ha]
      · simp [orig,onX,unitX]

theorem le_iff (a b : F) :
    cartesian.le orig unitX (cartesianCriteria.axis a) (cartesianCriteria.axis b) ↔ a≤b := by
  constructor
  · rintro ⟨z, hsum, hpos⟩
    have hsum' : b=a+z.val.1 :=
      (cartesianCriteria.add_iff ..).mp ((cartesianCriteria.axis_eta z).symm ▸ hsum)
    have hpos' : 0≤z.val.1 :=
      (nonnegative_iff _).mp ((cartesianCriteria.axis_eta z).symm ▸ hpos)
    linarith
  · intro hab
    refine ⟨cartesianCriteria.axis (b-a),(cartesianCriteria.add_iff ..).mpr ?_,
      (nonnegative_iff _).mpr (sub_nonneg.mpr hab)⟩
    ring

end
end PlanarIPRA.FrameRelations
