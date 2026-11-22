import Std

/-! Finite extrema, correspondences and a Lipschitz fragment of continuous logic.
Numerals measure truth values and error in a common unit. A finite rational
instance is cleared of denominators. Higher-order parameters below belong to
the Lean metatheory; the paper gives the bounded first-order instantiation. -/
namespace FiniteMetricLogic

def Near (e a b : Nat) : Prop := a ≤ b + e ∧ b ≤ a + e

theorem near_zero (a : Nat) : Near 0 a a := by simp [Near]

theorem near_comp {e d a b c : Nat} (h : Near e a b) (k : Near d b c) :
    Near (e+d) a c := by unfold Near at *; omega

def high : Nat → (Nat → Nat) → Nat
  | 0, f => f 0
  | n+1, f => max (high n f) (f (n+1))

def low : Nat → (Nat → Nat) → Nat
  | 0, f => f 0
  | n+1, f => min (low n f) (f (n+1))

theorem high_bound (n : Nat) (f : Nat → Nat) :
    ∀ i ≤ n, f i ≤ high n f := by
  induction n with
  | zero =>
    intro i hi
    have : i = 0 := by omega
    simp [this, high]
  | succ n ih =>
    intro i hi
    by_cases h : i ≤ n
    · exact Nat.le_trans (ih i h) (Nat.le_max_left _ _)
    · have : i = n+1 := by omega
      rw [this]
      exact Nat.le_max_right _ _

theorem low_bound (n : Nat) (f : Nat → Nat) :
    ∀ i ≤ n, low n f ≤ f i := by
  induction n with
  | zero =>
    intro i hi
    have : i = 0 := by omega
    simp [this, low]
  | succ n ih =>
    intro i hi
    by_cases h : i ≤ n
    · exact Nat.le_trans (Nat.min_le_left _ _) (ih i h)
    · have : i = n+1 := by omega
      rw [this]
      exact Nat.min_le_right _ _

theorem high_attains (n : Nat) (f : Nat → Nat) :
    ∃ i ≤ n, high n f = f i := by
  induction n with
  | zero => exact ⟨0, by omega, rfl⟩
  | succ n ih =>
    obtain ⟨i, hi, he⟩ := ih
    by_cases h : high n f ≤ f (n+1)
    · exact ⟨n+1, by omega, by simp [high, Nat.max_eq_right h]⟩
    · exact ⟨i, by omega, by unfold high; omega⟩

theorem low_attains (n : Nat) (f : Nat → Nat) :
    ∃ i ≤ n, low n f = f i := by
  induction n with
  | zero => exact ⟨0, by omega, rfl⟩
  | succ n ih =>
    obtain ⟨i, hi, he⟩ := ih
    by_cases h : f (n+1) ≤ low n f
    · exact ⟨n+1, by omega, by simp [low, Nat.min_eq_right h]⟩
    · exact ⟨i, by omega, by unfold low; omega⟩

structure Stage where
  last : Nat  -- the nonempty domain is 0,...,last
  pred : Nat → List Nat → Nat

def Rel := Nat → Nat → Prop

inductive Related (r : Rel) : List Nat → List Nat → Prop where
  | nil : Related r [] []
  | cons {i j : Nat} {xs ys : List Nat} : r i j → Related r xs ys → Related r (i::xs) (j::ys)

structure Corr (A B : Stage) (e : Nat) (r : Rel) : Prop where
  forth : ∀ i ≤ A.last, ∃ j ≤ B.last, r i j
  back : ∀ j ≤ B.last, ∃ i ≤ A.last, r i j
  atomic : ∀ p xs ys, Related r xs ys → Near e (A.pred p xs) (B.pred p ys)

def compose (r s : Rel) : Rel := fun i k => ∃ j, r i j ∧ s j k

theorem splitTuples {r s : Rel} {xs zs : List Nat} (h : Related (compose r s) xs zs) :
    ∃ ys, Related r xs ys ∧ Related s ys zs := by
  induction h with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons h _ ih =>
    obtain ⟨j, h₁, h₂⟩ := h
    obtain ⟨ys, k₁, k₂⟩ := ih
    exact ⟨j::ys, .cons h₁ k₁, .cons h₂ k₂⟩

theorem compose_corr {A B C : Stage} {e d : Nat} {r s : Rel}
    (h : Corr A B e r) (k : Corr B C d s) : Corr A C (e+d) (compose r s) where
  forth i hi := by
    obtain ⟨j, hj, hij⟩ := h.forth i hi
    obtain ⟨u, hu, hju⟩ := k.forth j hj
    exact ⟨u, hu, j, hij, hju⟩
  back u hu := by
    obtain ⟨j, hj, hju⟩ := k.back u hu
    obtain ⟨i, hi, hij⟩ := h.back j hj
    exact ⟨i, hi, j, hij, hju⟩
  atomic p xs zs hrel := by
    obtain ⟨ys, h₁, h₂⟩ := splitTuples hrel
    exact near_comp (h.atomic p xs ys h₁) (k.atomic p ys zs h₂)

theorem compose_assoc (r s t : Rel) (a d : Nat) :
    compose (compose r s) t a d ↔ compose r (compose s t) a d := by
  constructor
  · rintro ⟨c, ⟨b, hab, hbc⟩, hcd⟩
    exact ⟨b, hab, c, hbc, hcd⟩
  · rintro ⟨b, hab, c, hbc, hcd⟩
    exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩

inductive Formula where
  | atom (p : Nat) (vars : List Nat)
  | const (c : Nat)
  | neg (u : Formula)
  | shift (c : Nat) (u : Formula)
  | meet (u v : Formula)
  | join (u v : Formula)
  | supQ (u : Formula)
  | infQ (u : Formula)

def push (i : Nat) (x : Nat → Nat) : Nat → Nat
  | 0 => i
  | k+1 => x k

def eval (A : Stage) (D : Nat) : Formula → (Nat → Nat) → Nat
  | .atom p is, x => A.pred p (is.map x)
  | .const c, _ => c
  | .neg u, x => D - eval A D u x
  | .shift c u, x => eval A D u x - c
  | .meet u v, x => min (eval A D u x) (eval A D v x)
  | .join u v, x => max (eval A D u x) (eval A D v x)
  | .supQ u, x => high A.last (fun i => eval A D u (push i x))
  | .infQ u, x => low A.last (fun i => eval A D u (push i x))

theorem relate_map {r : Rel} {x y : Nat → Nat} (h : ∀ k, r (x k) (y k)) (is : List Nat) :
    Related r (is.map x) (is.map y) := by
  induction is with
  | nil => exact .nil
  | cons i _ ih => exact .cons (h i) ih

theorem relate_push {r : Rel} {x y : Nat → Nat} (h : ∀ k, r (x k) (y k))
    {i j : Nat} (hij : r i j) : ∀ k, r (push i x k) (push j y k)
  | 0 => hij
  | k+1 => h k

theorem high_transport {A B : Stage} {e : Nat} {r : Rel} (h : Corr A B e r)
    (f g : Nat → Nat) (k : ∀ i j, r i j → Near e (f i) (g j)) :
    Near e (high A.last f) (high B.last g) := by
  obtain ⟨i, hi, he⟩ := high_attains A.last f
  obtain ⟨j, hj, hij⟩ := h.forth i hi
  obtain ⟨v, hv, h'⟩ := high_attains B.last g
  obtain ⟨u, hu, huv⟩ := h.back v hv
  have h₁ := (k i j hij).1
  have h₂ := (k u v huv).2
  have b₁ := high_bound B.last g j hj
  have b₂ := high_bound A.last f u hu
  unfold Near; omega

theorem low_transport {A B : Stage} {e : Nat} {r : Rel} (h : Corr A B e r)
    (f g : Nat → Nat) (k : ∀ i j, r i j → Near e (f i) (g j)) :
    Near e (low A.last f) (low B.last g) := by
  obtain ⟨i, hi, he⟩ := low_attains A.last f
  obtain ⟨j, hj, hij⟩ := h.forth i hi
  obtain ⟨v, hv, h'⟩ := low_attains B.last g
  obtain ⟨u, hu, huv⟩ := h.back v hv
  have h₁ := (k i j hij).2
  have h₂ := (k u v huv).1
  have b₁ := low_bound B.last g j hj
  have b₂ := low_bound A.last f u hu
  unfold Near; omega

theorem formula_transport {A B : Stage} {e : Nat} {r : Rel} (h : Corr A B e r)
    (D : Nat) (t : Formula) : ∀ x y : Nat → Nat, (∀ k, r (x k) (y k)) →
      Near e (eval A D t x) (eval B D t y) := by
  induction t with
  | atom p is => intro x y hxy; exact h.atomic p _ _ (relate_map hxy is)
  | const c => intro _ _ _; unfold Near; simp [eval]
  | neg _ ih =>
    intro x y hxy; have k := ih x y hxy; unfold Near at *; simp only [eval]; omega
  | shift c _ ih =>
    intro x y hxy; have k := ih x y hxy; unfold Near at *; simp only [eval]; omega
  | meet _ _ hu hv =>
    intro x y hxy; have k := hu x y hxy; have l := hv x y hxy
    unfold Near at *; simp only [eval]; omega
  | join _ _ hu hv =>
    intro x y hxy; have k := hu x y hxy; have l := hv x y hxy
    unfold Near at *; simp only [eval]; omega
  | supQ _ ih =>
    intro x y hxy
    exact high_transport h _ _ (fun i j hij => ih (push i x) (push j y) (relate_push hxy hij))
  | infQ _ ih =>
    intro x y hxy
    exact low_transport h _ _ (fun i j hij => ih (push i x) (push j y) (relate_push hxy hij))


theorem identity_corr (A : Stage) : Corr A A 0 Eq where
  forth i hi := ⟨i, hi, rfl⟩
  back j hj := ⟨j, hj, rfl⟩
  atomic p xs ys h := by
    have he : xs = ys := by
      induction h with
      | nil => rfl
      | cons hij _ ih => simp [hij, ih]
    rw [he]; exact near_zero _

theorem compose_left_identity (r : Rel) (a b : Nat) : compose Eq r a b ↔ r a b := by
  constructor
  · rintro ⟨_, rfl, h⟩; exact h
  · intro h; exact ⟨a, rfl, h⟩

theorem compose_right_identity (r : Rel) (a b : Nat) : compose r Eq a b ↔ r a b := by
  constructor
  · rintro ⟨_, h, rfl⟩; exact h
  · intro h; exact ⟨b, h, rfl⟩

/-- The only nontrivial symbol is distance at index zero with arity two. -/
def metricStage (last : Nat) (dist : Nat → Nat → Nat) : Stage where
  last := last
  pred
    | 0, [i,j] => dist i j
    | _, _ => 0

def gap (i j : Nat) := max (i-j) (j-i)
def line (m : Nat) := metricStage (2*m) gap
def arc (m i j : Nat) := min (gap i j) (4*m - gap i j)
def circle (m : Nat) := metricStage (4*m-1) (arc m)
def radiusFormula := Formula.infQ (.supQ (.atom 0 [1,0]))

theorem radius_eval (n D : Nat) (d : Nat → Nat → Nat) (x : Nat → Nat) :
    eval (metricStage n d) D radiusFormula x = low n (fun i => high n (d i)) := rfl

theorem line_radius (m D : Nat) (x : Nat → Nat) :
    eval (line m) D radiusFormula x = m := by
  rw [line, radius_eval]
  obtain ⟨i, hi, he⟩ := low_attains (2*m) (fun i => high (2*m) (gap i))
  have hl := high_bound (2*m) (gap i) 0 (by omega)
  have hr := high_bound (2*m) (gap i) (2*m) (by omega)
  have hm := low_bound (2*m) (fun i => high (2*m) (gap i)) m (by omega)
  obtain ⟨j, hj, hmax⟩ := high_attains (2*m) (gap m)
  change max (i-0) (0-i) ≤ high (2*m) (gap i) at hl
  change max (i-2*m) (2*m-i) ≤ high (2*m) (gap i) at hr
  change high (2*m) (gap m) = max (m-j) (j-m) at hmax
  omega

theorem circle_eccentricity {m i : Nat} (hm : 0 < m) (hi : i ≤ 4*m-1) :
    high (4*m-1) (arc m i) = 2*m := by
  obtain ⟨j, hj, he⟩ := high_attains (4*m-1) (arc m i)
  change high (4*m-1) (arc m i) = min (gap i j) (4*m-gap i j) at he
  by_cases h : i < 2*m
  · have hb := high_bound (4*m-1) (arc m i) (i+2*m) (by omega)
    have hd : arc m i (i+2*m) = 2*m := by unfold arc gap; omega
    rw [hd] at hb
    omega
  · have hb := high_bound (4*m-1) (arc m i) (i-2*m) (by omega)
    have hd : arc m i (i-2*m) = 2*m := by unfold arc gap; omega
    rw [hd] at hb
    omega

theorem circle_radius {m : Nat} (hm : 0 < m) (D : Nat) (x : Nat → Nat) :
    eval (circle m) D radiusFormula x = 2*m := by
  rw [circle, radius_eval]
  obtain ⟨i, hi, he⟩ := low_attains (4*m-1) (fun i => high (4*m-1) (arc m i))
  exact he.trans (circle_eccentricity hm hi)

theorem circle_line_obstruction {m e : Nat} (hm : 0 < m) {r : Rel}
    (h : Corr (line m) (circle m) e r) : m ≤ e := by
  obtain ⟨j, _, hj⟩ := h.forth 0 (Nat.zero_le _)
  have k := formula_transport h (2*m) radiusFormula (fun _ => 0) (fun _ => j) (fun _ => hj)
  rw [line_radius, circle_radius hm] at k
  unfold Near at k
  omega

/-! Approximate descent for a chosen finite patch selector. Coverage and
the common-patch condition are witnesses scanned for in a finite table. -/
theorem glue_close {X Y I : Type} (U : I → X → Prop) (f : I → X → Y)
    (d : Y → Y → Nat) (select : X → I) (cover : ∀ x, U (select x) x)
    (e : Nat) (agree : ∀ i j x, U i x → U j x → d (f i x) (f j x) ≤ e) :
    ∀ i x, U i x → d (f (select x) x) (f i x) ≤ e :=
  fun i x hx => agree (select x) i x (cover x) hx

theorem glue_oscillation {X Y I : Type} (U : I → X → Prop) (f : I → X → Y)
    (d : Y → Y → Nat) (tri : ∀ a b c, d a c ≤ d a b + d b c)
    (select : X → I) (cover : ∀ x, U (select x) x)
    (nearby : X → X → Prop) (lebesgue : ∀ x y, nearby x y → ∃ i, U i x ∧ U i y)
    (e w : Nat) (agree : ∀ i j x, U i x → U j x → d (f i x) (f j x) ≤ e)
    (osc : ∀ i x y, U i x → U i y → nearby x y → d (f i x) (f i y) ≤ w)
    {x y : X} (hxy : nearby x y) : d (f (select x) x) (f (select y) y) ≤ e+w+e := by
  obtain ⟨i, hx, hy⟩ := lebesgue x y hxy
  have hx' := agree (select x) i x (cover x) hx
  have hy' := agree i (select y) y hy (cover y)
  have ho := osc i x y hx hy hxy
  have ht := tri (f (select x) x) (f i x) (f (select y) y)
  have hu := tri (f i x) (f i y) (f (select y) y)
  omega

end FiniteMetricLogic
