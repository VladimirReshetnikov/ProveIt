import OAI.Combinatorics.Progressions.Estimates.ScalarDominatedSlack

namespace OAI

section

namespace Erdos3
open scoped Classical

theorem pmf_bind_toReal_point_cap {X Y : Type*} (p : PMF X) (q : X → PMF Y)
    (y : Y) {δ : ℝ} (hδ : 0 ≤ δ) (hq : ∀ x, (q x y).toReal ≤ δ) :
    (p.bind q y).toReal ≤ δ := by
  have hpoint (x : X) : q x y ≤ ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_toReal ((q x).apply_ne_top y)]
    exact ENNReal.ofReal_le_ofReal (hq x)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (pmf_bind_point_cap p q y hpoint)).trans_eq (ENNReal.toReal_ofReal hδ)

theorem shiftedSmoothProductPMF_selected_event_probability_le
    {A J : Type*} [Fintype A] [Fintype J]
    (e : A ↪ J) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S)
    (bad : (J → ℤ) → Prop) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbad : ∀ tail : SelectedCoefficientComplement e → ℤ,
      ((shiftedSmoothProductPMF (fun i => a (e i)) (fun i => S (e i))
        (fun i => hS (e i)) (shiftedSmoothProductMass_restrict_pos e a S hS hZ)).map
        (fun c => decide (bad (selectedCoefficientJoin e (0 : ℤ) tail c))) true).toReal ≤ δ) :
    ((shiftedSmoothProductPMF a S hS hZ).map (fun f => decide (bad f)) true).toReal ≤ δ := by
  rw [shiftedSmoothProductPMF_selected_factorization e a S hS hZ, PMF.map_bind]
  simp_rw [PMF.map_comp]
  exact pmf_bind_toReal_point_cap _ _ true hδ hbad

theorem shiftedSmoothProductPMF_refresh_event_probability_le
    {A J : Type*} [Fintype A] [Fintype J]
    (e : A ↪ J) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S)
    (bad : (J → ℤ) → Prop) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbad : ∀ fixed : J → ℤ,
      ((shiftedSmoothProductPMF (fun i => a (e i)) (fun i => S (e i))
        (fun i => hS (e i)) (shiftedSmoothProductMass_restrict_pos e a S hS hZ)).map
        (fun c => decide (bad (Function.extend e c fixed))) true).toReal ≤ δ) :
    ((shiftedSmoothProductPMF a S hS hZ).map (fun f => decide (bad f)) true).toReal ≤ δ := by
  apply shiftedSmoothProductPMF_selected_event_probability_le e a S hS hZ bad hδ
  intro tail
  exact hbad (selectedCoefficientComplementFill e (0 : ℤ) tail)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open FiniteProbabilityWeights

theorem pmf_pair_selected_event_cap
    {X Y TX TY SX SY : Type*} (p : PMF X) (q : PMF Y)
    (pt : PMF TX) (qt : PMF TY) (ps : PMF SX) (qs : PMF SY)
    (joinX : TX → SX → X) (joinY : TY → SY → Y)
    (hp : p = pt.bind (fun t => ps.map (joinX t)))
    (hq : q = qt.bind (fun t => qs.map (joinY t)))
    (bad : X → Y → Prop) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbad : ∀ tx ty,
      ((ps.bind (fun x => qs.map (fun y => decide (bad (joinX tx x) (joinY ty y))))) true).toReal ≤ δ) :
    ((p.bind (fun x => q.map (fun y => decide (bad x y)))) true).toReal ≤ δ := by
  rw [hp, PMF.bind_bind]
  apply pmf_bind_toReal_point_cap _ _ true hδ
  intro tx
  rw [PMF.bind_map]
  change ((ps.bind (fun x => q.map (fun y => decide (bad (joinX tx x) y)))) true).toReal ≤ δ
  have he : ps.bind (fun x => q.map (fun y => decide (bad (joinX tx x) y))) =
      qt.bind (fun ty => ps.bind (fun x => qs.map
        (fun y => decide (bad (joinX tx x) (joinY ty y))))) := by
    simp_rw [hq, PMF.map_bind, PMF.map_comp]
    exact PMF.bind_comm ps qt _
  rw [he]
  exact pmf_bind_toReal_point_cap _ _ true hδ (hbad tx)

theorem supportedPMF_event_eq_map_true {X : Type*} (p : PMF X) (T : Finset X)
    (hT : ∀ x ∉ T, (p x).toReal = 0) (bad : X → Prop) :
    (ofSupportedPMF p T hT).eventProbability (fun x => bad x.val) =
      ((p.map (fun x => decide (bad x))) true).toReal := by
  have h := ofSupportedPMF_map_event p T hT (fun x => decide (bad x)) (fun b : Bool => b = true)
  simpa [eventProbability, mean] using h

theorem uniform_weights_toPMF {Y : Type*} [Fintype Y] [Nonempty Y] :
    (uniform Y).toPMF = PMF.uniformOfFintype Y := by
  ext y
  simp only [toPMF_apply, uniform, PMF.uniformOfFintype_apply]
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]

theorem supportedPMF_prod_uniform_event_eq_bind
    {X Y : Type*} [Fintype Y] [Nonempty Y]
    (p : PMF X) (T : Finset X) (hT : ∀ x ∉ T, (p x).toReal = 0)
    (bad : X → Y → Prop) :
    ((ofSupportedPMF p T hT).prod (uniform Y)).eventProbability
      (fun z => bad z.1.val z.2) =
      ((p.bind (fun x => (PMF.uniformOfFintype Y).map (fun y => decide (bad x y)))) true).toReal := by
  have he : p.bind (fun x => (PMF.uniformOfFintype Y).map (fun y => decide (bad x y))) =
      (PMF.uniformOfFintype Y).bind (fun y => p.map (fun x => decide (bad x y))) :=
    PMF.bind_comm p (PMF.uniformOfFintype Y) (fun x y => PMF.pure (decide (bad x y)))
  rw [he, ← uniform_weights_toPMF, toPMF_bind_toReal]
  change ((ofSupportedPMF p T hT).prod (uniform Y)).mean
    (fun z => if bad z.1.val z.2 then 1 else 0) = _
  rw [mean_prod, mean_comm]
  apply congrArg (uniform Y).mean
  funext y
  exact supportedPMF_event_eq_map_true p T hT (fun x => bad x y)

theorem mixedSmoothUniformPMF_refresh_event_probability_le
    {A J B K : Type*} [Fintype A] [Fintype J] [Fintype B] [Fintype K]
    (e : A ↪ J) (d : B ↪ K) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) (N : ℕ) [NeZero N]
    (bad : (J → ℤ) → (K → ZMod N) → Prop) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbad : ∀ (fixed : J → ℤ) (fixedDeck : K → ZMod N),
      (((shiftedSmoothProductPMF (fun i => a (e i)) (fun i => S (e i))
        (fun i => hS (e i)) (shiftedSmoothProductMass_restrict_pos e a S hS hZ)).bind
        (fun c => (PMF.uniformOfFintype (B → ZMod N)).map
          (fun z => decide (bad (Function.extend e c fixed)
            (Function.extend d z fixedDeck))))) true).toReal ≤ δ) :
    (((shiftedSmoothProductPMF a S hS hZ).bind
      (fun x => (PMF.uniformOfFintype (K → ZMod N)).map
        (fun y => decide (bad x y)))) true).toReal ≤ δ := by
  let : Fintype (SelectedCoefficientComplement d) :=
    Subtype.fintype (fun column => column ∉ Set.range d)
  apply pmf_pair_selected_event_cap
    (shiftedSmoothProductPMF a S hS hZ) (PMF.uniformOfFintype (K → ZMod N))
    (shiftedSmoothProductPMF
      (fun k : SelectedCoefficientComplement e => a k.val)
      (fun k : SelectedCoefficientComplement e => S k.val)
      (fun k => hS k.val) (shiftedSmoothProductMass_restrict_pos Subtype.val a S hS hZ))
    (PMF.uniformOfFintype (SelectedCoefficientComplement d → ZMod N))
    (shiftedSmoothProductPMF (fun i => a (e i)) (fun i => S (e i))
      (fun i => hS (e i)) (shiftedSmoothProductMass_restrict_pos e a S hS hZ))
    (PMF.uniformOfFintype (B → ZMod N))
    (selectedCoefficientJoin e (0 : ℤ)) (selectedCoefficientJoin d (0 : ZMod N))
    (shiftedSmoothProductPMF_selected_factorization e a S hS hZ)
    (uniformZMod_selected_split N d) bad hδ
  intro tx ty
  exact hbad (selectedCoefficientComplementFill e (0 : ℤ) tx)
    (selectedCoefficientComplementFill d (0 : ZMod N) ty)

theorem shiftedSmoothProductFiniteWeights_prod_uniform_event_eq_bind
    {J Y : Type*} [Fintype J] [Fintype Y] [Nonempty Y]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    (bad : (J → ℤ) → Y → Prop) :
    ((shiftedSmoothProductFiniteWeights a S hS hZ).prod (uniform Y)).eventProbability
      (fun z => bad z.1.val z.2) =
      (((shiftedSmoothProductPMF a S hS hZ).bind
        (fun x => (PMF.uniformOfFintype Y).map (fun y => decide (bad x y)))) true).toReal :=
  supportedPMF_prod_uniform_event_eq_bind _ _ _ bad

theorem mixedSmoothUniform_refresh_event_probability_le
    {A J B K : Type*} [Fintype A] [Fintype J] [Fintype B] [Fintype K]
    (e : A ↪ J) (d : B ↪ K) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) (N : ℕ) [NeZero N]
    (bad : (J → ℤ) → (K → ZMod N) → Prop) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbad : ∀ (fixed : J → ℤ) (fixedDeck : K → ZMod N),
      ((shiftedSmoothProductFiniteWeights (fun i => a (e i)) (fun i => S (e i))
        (fun i => hS (e i)) (shiftedSmoothProductMass_restrict_pos e a S hS hZ)).prod
        (uniform (B → ZMod N))).eventProbability
        (fun z => bad (Function.extend e z.1.val fixed) (Function.extend d z.2 fixedDeck)) ≤ δ) :
    ((shiftedSmoothProductFiniteWeights a S hS hZ).prod (uniform (K → ZMod N))).eventProbability
      (fun z => bad z.1.val z.2) ≤ δ := by
  rw [shiftedSmoothProductFiniteWeights_prod_uniform_event_eq_bind]
  apply mixedSmoothUniformPMF_refresh_event_probability_le e d a S hS hZ N bad hδ
  intro fixed fixedDeck
  have he := shiftedSmoothProductFiniteWeights_prod_uniform_event_eq_bind
    (fun i => a (e i)) (fun i => S (e i)) (fun i => hS (e i))
    (shiftedSmoothProductMass_restrict_pos e a S hS hZ)
    (fun x y => bad (Function.extend e x fixed) (Function.extend d y fixedDeck))
  exact he.symm.trans_le (hbad fixed fixedDeck)

theorem independentProduct_uniform_refresh_event_probability_le
    {A J B K : Type*} [Fintype A] [Fintype J] [Fintype B] [Fintype K]
    (e : A ↪ J) (d : B ↪ K) (p : J → PMF ℤ)
    (a S : A → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hselected : independentProductPMF (fun i => p (e i)) = shiftedSmoothProductPMF a S hS hZ)
    (N : ℕ) [NeZero N] (bad : (J → ℤ) → (K → ZMod N) → Prop) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbad : ∀ (fixed : J → ℤ) (fixedDeck : K → ZMod N),
      (((shiftedSmoothProductPMF a S hS hZ).bind
        (fun c => (PMF.uniformOfFintype (B → ZMod N)).map
          (fun z => decide (bad (Function.extend e c fixed)
            (Function.extend d z fixedDeck))))) true).toReal ≤ δ) :
    (((independentProductPMF p).bind
      (fun x => (PMF.uniformOfFintype (K → ZMod N)).map
        (fun y => decide (bad x y)))) true).toReal ≤ δ := by
  let : Fintype (SelectedCoefficientComplement e) :=
    Subtype.fintype (fun column => column ∉ Set.range e)
  let : Fintype (SelectedCoefficientComplement d) :=
    Subtype.fintype (fun column => column ∉ Set.range d)
  have hp : independentProductPMF p =
      (independentProductPMF (fun t : SelectedCoefficientComplement e => p t.val)).bind
        (fun tail => (shiftedSmoothProductPMF a S hS hZ).map
          (selectedCoefficientJoin e (0 : ℤ) tail)) := by
    rw [independentProductPMF_selected_split e (0 : ℤ) p, hselected]
  apply pmf_pair_selected_event_cap (independentProductPMF p)
    (PMF.uniformOfFintype (K → ZMod N))
    (independentProductPMF (fun t : SelectedCoefficientComplement e => p t.val))
    (PMF.uniformOfFintype (SelectedCoefficientComplement d → ZMod N))
    (shiftedSmoothProductPMF a S hS hZ) (PMF.uniformOfFintype (B → ZMod N))
    (selectedCoefficientJoin e (0 : ℤ)) (selectedCoefficientJoin d (0 : ZMod N))
    hp (uniformZMod_selected_split N d) bad hδ
  intro tx ty
  exact hbad (selectedCoefficientComplementFill e (0 : ℤ) tx)
    (selectedCoefficientComplementFill d (0 : ZMod N) ty)

theorem independentProductPMF_selected_smooth {A J : Type*} [Fintype A]
    (e : A → J) (p : J → PMF ℤ)
    (a S : A → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hcoordinate : ∀ i, p (e i) = shiftedSmoothCoefficientPMF (a i) (S i) (hS i)
      (shiftedSmoothProductMass_coordinate_pos a S hS hZ i)) :
    independentProductPMF (fun i => p (e i)) = shiftedSmoothProductPMF a S hS hZ := by
  rw [shiftedSmoothProductPMF_eq_independent]
  exact congrArg independentProductPMF (funext hcoordinate)

theorem independentProduct_uniform_smooth_selected_event_probability_le
    {A J B K : Type*} [Fintype A] [Fintype J] [Fintype B] [Fintype K]
    (e : A ↪ J) (d : B ↪ K) (p : J → PMF ℤ)
    (a S : A → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hcoordinate : ∀ i, p (e i) = shiftedSmoothCoefficientPMF (a i) (S i) (hS i)
      (shiftedSmoothProductMass_coordinate_pos a S hS hZ i))
    (N : ℕ) [NeZero N] (bad : (J → ℤ) → (K → ZMod N) → Prop) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbad : ∀ (fixed : J → ℤ) (fixedDeck : K → ZMod N),
      ((shiftedSmoothProductFiniteWeights a S hS hZ).prod (uniform (B → ZMod N))).eventProbability
        (fun z => bad (Function.extend e z.1.val fixed) (Function.extend d z.2 fixedDeck)) ≤ δ) :
    (((independentProductPMF p).bind
      (fun x => (PMF.uniformOfFintype (K → ZMod N)).map
        (fun y => decide (bad x y)))) true).toReal ≤ δ := by
  apply independentProduct_uniform_refresh_event_probability_le e d p a S hS hZ
    (independentProductPMF_selected_smooth e p a S hS hZ hcoordinate) N bad hδ
  intro fixed fixedDeck
  have he := shiftedSmoothProductFiniteWeights_prod_uniform_event_eq_bind a S hS hZ
    (fun x y => bad (Function.extend e x fixed) (Function.extend d y fixedDeck))
  exact he.symm.trans_le (hbad fixed fixedDeck)

end Erdos3

end

end OAI
