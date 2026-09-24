import Diophantine.Paper1980.DValid93

/-!
# Row shapes of the compiled circuit (Section 1)

The compiled circuit uses a fixed repertoire of quadratic rows over the
physical coordinates.  Every logical value is a sum of three physical
coordinates (a *group* `g : Fin 3 → Fin m`), `δ` and `δ'` are single
coordinates, and the rows are

* `copyRow g h`: `(Σg)² − (Σh)²`;
* `normRow g`: `(Σg)² − x²`;
* `addRow g h k δ`: `2δ(Σg + Σh − Σk)`;
* `mulRow g h k δ`: `2(Σg · Σh − Σk · δ)`;
* `zeroRow g δ`: `2 δ Σg`;
* `oneRow g δ δ'`: `2δ(Σg − δ')`;
* `deltaRow δ δ'`: `δ'² − δ²`;
* `uRow g δ δ' u`: `2x Σg − 2δδ' − 2 δ Σu`;
* `unitRow δ`: `δ²`;

together with the negation `negRow`.  For groups of distinct coordinates the
rows are valid (`RowValid`): the *structural* validity `RowStruct` (distinct
square coordinates, distinct unordered cross pairs of distinct coordinates,
distinct `xz` coordinates, signs `±1`) implies the validity of the weight
list, by the base-three uniqueness of the weights.
-/

namespace Jones1980

namespace Iso

open Layout

section Shapes

variable {m : ℕ}

/-- The negation of a row. -/
def negRow (R : Row m) : Row m :=
  ⟨R.sq.map fun p => (p.1, -p.2), R.cross.map fun q => (q.1, q.2.1, -q.2.2),
    R.xz.map fun p => (p.1, -p.2), -R.xx⟩

theorem negRow_val (R : Row m) (x : ℤ) (z : Fin m → ℤ) :
    (negRow R).val x z = -(R.val x z) := by
  unfold negRow Row.val
  simp only [List.map_map, Function.comp_def]
  have e1 : (R.sq.map fun p => -p.2 * z p.1 ^ 2) = R.sq.map fun p => (-1) * (p.2 * z p.1 ^ 2) :=
    List.map_congr_left fun p _ => by ring
  have e2 : (R.cross.map fun p => 2 * -p.2.2 * z p.1 * z p.2.1) =
      R.cross.map fun p => (-1) * (2 * p.2.2 * z p.1 * z p.2.1) :=
    List.map_congr_left fun p _ => by ring
  have e3 : (R.xz.map fun p => 2 * -p.2 * x * z p.1) =
      R.xz.map fun p => (-1) * (2 * p.2 * x * z p.1) :=
    List.map_congr_left fun p _ => by ring
  rw [e1, e2, e3, List.sum_map_mul_left, List.sum_map_mul_left, List.sum_map_mul_left]
  ring

/-- The sum of a group. -/
def S (g : Fin 3 → Fin m) (z : Fin m → ℤ) : ℤ := z (g 0) + z (g 1) + z (g 2)

def sqTerms (g : Fin 3 → Fin m) (s : ℤ) : List (Fin m × ℤ) := [(g 0, s), (g 1, s), (g 2, s)]

def crossTerms (g : Fin 3 → Fin m) (s : ℤ) : List (Fin m × Fin m × ℤ) :=
  [(g 0, g 1, s), (g 0, g 2, s), (g 1, g 2, s)]

def prodTerms (g h : Fin 3 → Fin m) (s : ℤ) : List (Fin m × Fin m × ℤ) :=
  [(g 0, h 0, s), (g 0, h 1, s), (g 0, h 2, s), (g 1, h 0, s), (g 1, h 1, s), (g 1, h 2, s),
    (g 2, h 0, s), (g 2, h 1, s), (g 2, h 2, s)]

def dotTerms (g : Fin 3 → Fin m) (d : Fin m) (s : ℤ) : List (Fin m × Fin m × ℤ) :=
  [(g 0, d, s), (g 1, d, s), (g 2, d, s)]

def copyRow (g h : Fin 3 → Fin m) : Row m :=
  ⟨sqTerms g 1 ++ sqTerms h (-1), crossTerms g 1 ++ crossTerms h (-1), [], 0⟩

def normRow (g : Fin 3 → Fin m) : Row m := ⟨sqTerms g 1, crossTerms g 1, [], -1⟩

def addRow (g h k : Fin 3 → Fin m) (d : Fin m) : Row m :=
  ⟨[], dotTerms g d 1 ++ dotTerms h d 1 ++ dotTerms k d (-1), [], 0⟩

def mulRow (g h k : Fin 3 → Fin m) (d : Fin m) : Row m :=
  ⟨[], prodTerms g h 1 ++ dotTerms k d (-1), [], 0⟩

def zeroRow (g : Fin 3 → Fin m) (d : Fin m) : Row m := ⟨[], dotTerms g d 1, [], 0⟩

def oneRow (g : Fin 3 → Fin m) (d d' : Fin m) : Row m :=
  ⟨[], dotTerms g d 1 ++ [(d, d', -1)], [], 0⟩

def deltaRow (d d' : Fin m) : Row m := ⟨[(d', 1), (d, -1)], [], [], 0⟩

def uRow (g : Fin 3 → Fin m) (d d' : Fin m) (u : Fin 3 → Fin m) : Row m :=
  ⟨[], (d, d', -1) :: dotTerms u d (-1), sqTerms g 1, 0⟩

def unitRow (d : Fin m) : Row m := ⟨[(d, 1)], [], [], 0⟩

variable (x : ℤ) (z : Fin m → ℤ)

theorem copyRow_val (g h : Fin 3 → Fin m) :
    (copyRow g h).val x z = S g z ^ 2 - S h z ^ 2 := by
  simp [copyRow, sqTerms, crossTerms, Row.val, S]; ring

theorem normRow_val (g : Fin 3 → Fin m) : (normRow g).val x z = S g z ^ 2 - x ^ 2 := by
  simp [normRow, sqTerms, crossTerms, Row.val, S]; ring

theorem addRow_val (g h k : Fin 3 → Fin m) (d : Fin m) :
    (addRow g h k d).val x z = 2 * z d * (S g z + S h z - S k z) := by
  simp [addRow, dotTerms, Row.val, S]; ring

theorem mulRow_val (g h k : Fin 3 → Fin m) (d : Fin m) :
    (mulRow g h k d).val x z = 2 * (S g z * S h z - S k z * z d) := by
  simp [mulRow, prodTerms, dotTerms, Row.val, S]; ring

theorem zeroRow_val (g : Fin 3 → Fin m) (d : Fin m) :
    (zeroRow g d).val x z = 2 * z d * S g z := by
  simp [zeroRow, dotTerms, Row.val, S]; ring

theorem oneRow_val (g : Fin 3 → Fin m) (d d' : Fin m) :
    (oneRow g d d').val x z = 2 * z d * (S g z - z d') := by
  simp [oneRow, dotTerms, Row.val, S]; ring

theorem deltaRow_val (d d' : Fin m) : (deltaRow d d').val x z = z d' ^ 2 - z d ^ 2 := by
  simp [deltaRow, Row.val]; ring

theorem uRow_val (g : Fin 3 → Fin m) (d d' : Fin m) (u : Fin 3 → Fin m) :
    (uRow g d d' u).val x z = 2 * x * S g z - 2 * z d * z d' - 2 * z d * S u z := by
  simp [uRow, dotTerms, sqTerms, Row.val, S]; ring

theorem unitRow_val (d : Fin m) : (unitRow d).val x z = z d ^ 2 := by
  simp [unitRow, Row.val]

end Shapes

section Struct

variable {m : ℕ}

/-- Structural validity of a row: distinct square coordinates, distinct unordered cross
pairs of distinct coordinates, distinct `xz` coordinates, all signs of absolute value
at most one. -/
structure RowStruct (R : Row m) : Prop where
  sq_nodup : (R.sq.map Prod.fst).Nodup
  cross_pw : R.cross.Pairwise fun p q =>
    ¬ (p.1 = q.1 ∧ p.2.1 = q.2.1) ∧ ¬ (p.1 = q.2.1 ∧ p.2.1 = q.1)
  cross_ne : ∀ q ∈ R.cross, q.1 ≠ q.2.1
  xz_nodup : (R.xz.map Prod.fst).Nodup
  sq_sign : ∀ p ∈ R.sq, |p.2| ≤ 1
  cross_sign : ∀ q ∈ R.cross, |q.2.2| ≤ 1
  xz_sign : ∀ p ∈ R.xz, |p.2| ≤ 1
  xx_sign : |R.xx| ≤ 1

theorem v_inj {i k : Fin m} (h : v i = v k) : i = k := Fin.ext (v_strictMono.injective h)

/-- Structural validity implies validity. -/
theorem RowStruct.valid {R : Row m} (h : RowStruct R) : RowValid R := by
  refine ⟨?_, ?_, h.cross_ne⟩
  · intro p hp
    unfold Row.terms at hp
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hp
    rcases hp with ((⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩) | rfl
    · exact h.sq_sign q hq
    · exact h.cross_sign q hq
    · exact h.xz_sign q hq
    · exact h.xx_sign
  · unfold Row.terms
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def]
    -- the four parts
    have hA : (R.sq.map fun p => 2 * v p.1).Nodup := by
      have e : (R.sq.map fun p => 2 * v p.1) =
          (R.sq.map Prod.fst).map (fun i : Fin m => 2 * v i) := by
        rw [List.map_map]; rfl
      rw [e]
      exact h.sq_nodup.map (fun i k (hik : 2 * v i = 2 * v k) => v_inj (by omega))
    have hB : (R.cross.map fun q => v q.1 + v q.2.1).Nodup := by
      rw [List.Nodup, List.pairwise_map]
      refine h.cross_pw.imp ?_
      intro p q ⟨h1, h2⟩ heq
      unfold v at heq
      rcases Weights.add_pow_eq_add p.1 p.2.1 q.1 q.2.1 (by omega) with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact h1 ⟨Fin.ext e1, Fin.ext e2⟩
      · exact h2 ⟨Fin.ext e1, Fin.ext e2⟩
    have hC : (R.xz.map fun p => v p.1).Nodup := by
      have e : (R.xz.map fun p => v p.1) = (R.xz.map Prod.fst).map (fun i : Fin m => v i) := by
        rw [List.map_map]; rfl
      rw [e]
      exact h.xz_nodup.map (fun i k (hik : v i = v k) => v_inj hik)
    rw [List.nodup_append, List.nodup_append, List.nodup_append]
    refine ⟨⟨⟨hA, hB, ?_⟩, hC, ?_⟩, List.nodup_singleton 0, ?_⟩
    · -- squares versus cross terms
      intro a ha b hb
      rw [List.mem_map] at ha hb
      obtain ⟨p, hp, rfl⟩ := ha
      obtain ⟨q, hq, rfl⟩ := hb
      intro heq
      unfold v at heq
      have := Weights.two_mul_pow_eq_add p.1 q.1 q.2.1 (by omega)
      exact h.cross_ne q hq (Fin.ext (this.1.trans this.2.symm))
    · -- squares and cross terms versus `xz` terms
      intro a ha b hb
      rw [List.mem_append] at ha
      rw [List.mem_map] at hb
      obtain ⟨r, _, rfl⟩ := hb
      rcases ha with ha | ha <;> rw [List.mem_map] at ha <;> obtain ⟨p, _, rfl⟩ := ha
      · intro heq; unfold v at heq
        exact Weights.pow_ne_two_mul r.1 p.1 (by omega)
      · intro heq; unfold v at heq
        exact Weights.pow_ne_add r.1 p.1 p.2.1 (by omega)
    · -- everything versus the constant term
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      simp only [List.mem_append, List.mem_map] at ha
      rcases ha with (⟨p, _, rfl⟩ | ⟨p, _, rfl⟩) | ⟨p, _, rfl⟩
      · have := v_pos p.1; omega
      · have := v_pos p.1; omega
      · have := v_pos p.1; omega

theorem negRow_struct {R : Row m} (h : RowStruct R) : RowStruct (negRow R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [negRow, List.map_map, Function.comp_def] using h.sq_nodup
  · unfold negRow; simp only
    rw [List.pairwise_map]
    exact h.cross_pw.imp fun {p q} hpq => hpq
  · intro q hq
    unfold negRow at hq
    simp only [List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact h.cross_ne q' hq'
  · simpa [negRow, List.map_map, Function.comp_def] using h.xz_nodup
  · intro p hp
    unfold negRow at hp
    simp only [List.mem_map] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    simpa using h.sq_sign p' hp'
  · intro q hq
    unfold negRow at hq
    simp only [List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    simpa using h.cross_sign q' hq'
  · intro p hp
    unfold negRow at hp
    simp only [List.mem_map] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    simpa using h.xz_sign p' hp'
  · simpa [negRow] using h.xx_sign

end Struct

section ShapeStruct

variable {m : ℕ}

/-- Distinct groups: no coordinate in common. -/
def Disj (g h : Fin 3 → Fin m) : Prop := ∀ a b, g a ≠ h b

theorem Disj.symm {g h : Fin 3 → Fin m} (hgh : Disj g h) : Disj h g := fun a b => (hgh b a).symm

/-- A group avoids a coordinate. -/
def Avoids (g : Fin 3 → Fin m) (d : Fin m) : Prop := ∀ a, g a ≠ d

theorem copyRow_struct {g h : Fin 3 → Fin m} (hg : Function.Injective g)
    (hh : Function.Injective h) (hgh : Disj g h) : RowStruct (copyRow g h) := by
  have hhg := hgh.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [copyRow, sqTerms, crossTerms, hg.eq_iff, hh.eq_iff, hgh _ _, hhg _ _]

theorem normRow_struct {g : Fin 3 → Fin m} (hg : Function.Injective g) :
    RowStruct (normRow g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [normRow, sqTerms, crossTerms, hg.eq_iff]

theorem addRow_struct {g h k : Fin 3 → Fin m} {d : Fin m} (hg : Function.Injective g)
    (hh : Function.Injective h) (hk : Function.Injective k) (hgh : Disj g h) (hgk : Disj g k)
    (hhk : Disj h k) (hgd : Avoids g d) (hhd : Avoids h d) (hkd : Avoids k d) :
    RowStruct (addRow g h k d) := by
  have hhg := hgh.symm; have hkg := hgk.symm; have hkh := hhk.symm
  have hdg : ∀ a, d ≠ g a := fun a => (hgd a).symm
  have hdh : ∀ a, d ≠ h a := fun a => (hhd a).symm
  have hdk : ∀ a, d ≠ k a := fun a => (hkd a).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [addRow, dotTerms, hg.eq_iff, hh.eq_iff, hk.eq_iff, hgh _ _, hgk _ _, hhk _ _, hhg _ _,
      hkg _ _, hkh _ _, hgd _, hhd _, hkd _, hdg _, hdh _, hdk _]

theorem mulRow_struct {g h k : Fin 3 → Fin m} {d : Fin m} (hg : Function.Injective g)
    (hh : Function.Injective h) (hk : Function.Injective k) (hgh : Disj g h) (hgk : Disj g k)
    (hhk : Disj h k) (hgd : Avoids g d) (hhd : Avoids h d) (hkd : Avoids k d) :
    RowStruct (mulRow g h k d) := by
  have hhg := hgh.symm; have hkg := hgk.symm; have hkh := hhk.symm
  have hdg : ∀ a, d ≠ g a := fun a => (hgd a).symm
  have hdh : ∀ a, d ≠ h a := fun a => (hhd a).symm
  have hdk : ∀ a, d ≠ k a := fun a => (hkd a).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [mulRow, prodTerms, dotTerms, hg.eq_iff, hh.eq_iff, hk.eq_iff, hgh _ _, hgk _ _,
      hhk _ _, hhg _ _, hkg _ _, hkh _ _, hgd _, hhd _, hkd _, hdg _, hdh _, hdk _]

theorem zeroRow_struct {g : Fin 3 → Fin m} {d : Fin m} (hg : Function.Injective g)
    (hgd : Avoids g d) : RowStruct (zeroRow g d) := by
  have hdg : ∀ a, d ≠ g a := fun a => (hgd a).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [zeroRow, dotTerms, hg.eq_iff, hgd _, hdg _]

theorem oneRow_struct {g : Fin 3 → Fin m} {d d' : Fin m} (hg : Function.Injective g)
    (hgd : Avoids g d) (hgd' : Avoids g d') (hdd : d ≠ d') : RowStruct (oneRow g d d') := by
  have hdg : ∀ a, d ≠ g a := fun a => (hgd a).symm
  have hd'g : ∀ a, d' ≠ g a := fun a => (hgd' a).symm
  have hd'd : d' ≠ d := hdd.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [oneRow, dotTerms, hg.eq_iff, hgd _, hdg _, hgd' _, hd'g _, hdd, hd'd]

theorem deltaRow_struct {d d' : Fin m} (hdd : d ≠ d') : RowStruct (deltaRow d d') := by
  have hd'd : d' ≠ d := hdd.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [deltaRow, hdd, hd'd]

theorem uRow_struct {g u : Fin 3 → Fin m} {d d' : Fin m} (hg : Function.Injective g)
    (hu : Function.Injective u) (hud : Avoids u d) (hud' : Avoids u d') (hdd : d ≠ d') :
    RowStruct (uRow g d d' u) := by
  have hdu : ∀ a, d ≠ u a := fun a => (hud a).symm
  have hd'u : ∀ a, d' ≠ u a := fun a => (hud' a).symm
  have hd'd : d' ≠ d := hdd.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [uRow, dotTerms, sqTerms, hg.eq_iff, hu.eq_iff, hud _, hud' _, hdu _, hd'u _, hdd, hd'd]

theorem unitRow_struct (d : Fin m) : RowStruct (unitRow d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [unitRow]

end ShapeStruct

end Iso

end Jones1980
