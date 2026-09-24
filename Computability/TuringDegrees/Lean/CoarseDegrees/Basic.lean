import CoarseDegrees.Density
import TuringDegrees

/-!
# Coarse descriptions, coarse reducibility, and the statement C1

Total functions `ℕ → ℕ` are used as oracles through `oracle f = fun n => Part.some (f n)` and
Mathlib's `TuringReducible` (`≤ᵀ`) on partial functions.  Uniform reductions use the finite
oracle-program syntax `TuringDegrees.OracleProgram` of the sibling repository
`C:\ProveIt` (`Computability/TuringDegrees/Lean/TuringDegrees/Cardinality.lean`).

The definitions follow Section 2 of `Computability/TuringDegrees/Research/CoarseDegrees/research-synthesis/Turing_Degrees_Synthesis.tex`
(which follows Gerdes, arXiv:2508.06925v1, Definitions 2.3--2.4, and
Hirschfeldt--Jockusch--Kuyper--Schupp, *Coarse reducibility and algorithmic randomness*,
J. Symb. Log. 81 (2016), Definitions 1.2--1.3).  Everything in this file is proved.
-/

noncomputable section

open scoped Classical Computability
open TuringDegrees

namespace CoarseDegrees

/-- The total oracle given by a function `ℕ → ℕ`. -/
def oracle (f : ℕ → ℕ) : ℕ →. ℕ := fun n => Part.some (f n)

/-- Turing reducibility of total functions. -/
def TRed (f g : ℕ → ℕ) : Prop := oracle f ≤ᵀ oracle g

@[inherit_doc] scoped infix:50 " ≤ₜ " => TRed

theorem TRed.refl (f : ℕ → ℕ) : f ≤ₜ f := TuringReducible.refl _

theorem TRed.trans {f g h : ℕ → ℕ} (hfg : f ≤ₜ g) (hgh : g ≤ₜ h) : f ≤ₜ h :=
  TuringReducible.trans hfg hgh

theorem computable_iff_partrec_oracle {f : ℕ → ℕ} : Computable f ↔ Partrec (oracle f) :=
  Iff.rfl

/-- A function reducible to a computable function is computable. -/
theorem TRed.computable {f g : ℕ → ℕ} (h : f ≤ₜ g) (hg : Computable g) : Computable f := by
  refine RecursiveIn.partrec_of_oracle (O := {oracle g}) ?_ h
  intro o ho
  rw [Set.mem_singleton_iff.mp ho]
  exact hg

/-- A computable function is reducible to everything. -/
theorem TRed.of_computable {f : ℕ → ℕ} (hf : Computable f) (g : ℕ → ℕ) : f ≤ₜ g :=
  Partrec.turingReducible (f := oracle f) hf

/-! ## Coarse descriptions -/

/-- The set on which two functions disagree. -/
def disagree (f g : ℕ → ℕ) : Set ℕ := {n | f n ≠ g n}

/-- `f ≈ g`: the functions agree off a set of density zero.  Then `f` is a *coarse description*
of `g`. -/
def CoarseEq (f g : ℕ → ℕ) : Prop := DensityZero (disagree f g)

theorem CoarseEq.refl (f : ℕ → ℕ) : CoarseEq f f := by
  have : disagree f f = ∅ := by
    ext n
    simp [disagree]
  unfold CoarseEq
  rw [this]
  exact densityZero_empty

theorem CoarseEq.symm {f g : ℕ → ℕ} (h : CoarseEq f g) : CoarseEq g f := by
  have : disagree g f = disagree f g := by
    ext n
    simp [disagree, ne_comm]
  unfold CoarseEq
  rw [this]
  exact h

theorem CoarseEq.trans {f g h : ℕ → ℕ} (hfg : CoarseEq f g) (hgh : CoarseEq g h) :
    CoarseEq f h := by
  refine (DensityZero.union hfg hgh).mono ?_
  intro n hn
  simp only [disagree, Set.mem_setOf_eq, Set.mem_union] at hn ⊢
  by_contra hcon
  have hboth := not_or.mp hcon
  exact hn ((not_not.mp hboth.1).trans (not_not.mp hboth.2))

/-- `f` is coarsely computable: it has a computable coarse description. -/
def CoarselyComputable (f : ℕ → ℕ) : Prop := ∃ D, Computable D ∧ CoarseEq D f

/-! ## Coarse reducibilities -/

/-- Nonuniform coarse reducibility: every coarse description of `g` computes a coarse
description of `f`. -/
def NCRed (f g : ℕ → ℕ) : Prop :=
  ∀ D, CoarseEq D g → ∃ E, CoarseEq E f ∧ E ≤ₜ D

/-- Uniform coarse reducibility: one oracle program maps every coarse description of `g` to a
coarse description of `f`. -/
def UCRed (f g : ℕ → ℕ) : Prop :=
  ∃ p : OracleProgram, ∀ D, CoarseEq D g → ∃ E, CoarseEq E f ∧ p.eval (oracle D) = oracle E

/-- Nonuniform coarse equivalence. -/
def NCEquiv (f g : ℕ → ℕ) : Prop := NCRed f g ∧ NCRed g f

/-- Uniform coarse equivalence. -/
def UCEquiv (f g : ℕ → ℕ) : Prop := UCRed f g ∧ UCRed g f

@[inherit_doc] scoped infix:50 " ≤ₙ " => NCRed
@[inherit_doc] scoped infix:50 " ≡ₙ " => NCEquiv
@[inherit_doc] scoped infix:50 " ≤ᵤ " => UCRed
@[inherit_doc] scoped infix:50 " ≡ᵤ " => UCEquiv

/-- A uniform coarse reduction is a nonuniform one. -/
theorem UCRed.ncRed {f g : ℕ → ℕ} (h : f ≤ᵤ g) : f ≤ₙ g := by
  obtain ⟨p, hp⟩ := h
  intro D hD
  obtain ⟨E, hE, hpE⟩ := hp D hD
  refine ⟨E, hE, ?_⟩
  have := OracleProgram.eval_recursiveIn (oracle D) p
  rw [hpE] at this
  exact RecursiveIn.iff_nat.mpr this

theorem UCEquiv.ncEquiv {f g : ℕ → ℕ} (h : f ≡ᵤ g) : f ≡ₙ g :=
  ⟨h.1.ncRed, h.2.ncRed⟩

theorem NCEquiv.symm {f g : ℕ → ℕ} (h : f ≡ₙ g) : g ≡ₙ f := ⟨h.2, h.1⟩

/-- Synthesis, Lemma 2.1: functions that agree off a density-zero set have the same coarse
descriptions, and the identity program is a uniform reduction in both directions. -/
theorem CoarseEq.ucRed {f g : ℕ → ℕ} (h : CoarseEq f g) : f ≤ᵤ g :=
  ⟨.oracle, fun D hD => ⟨D, hD.trans h.symm, rfl⟩⟩

theorem CoarseEq.ucEquiv {f g : ℕ → ℕ} (h : CoarseEq f g) : f ≡ᵤ g :=
  ⟨h.ucRed, h.symm.ucRed⟩

theorem CoarseEq.ncEquiv {f g : ℕ → ℕ} (h : CoarseEq f g) : f ≡ₙ g :=
  h.ucEquiv.ncEquiv

/-- Synthesis, Lemma 2.3 (self-application): a representative of the coarse class of `f`
computes a coarse description of `f`. -/
theorem NCEquiv.exists_description {g f : ℕ → ℕ} (h : g ≡ₙ f) :
    ∃ E, CoarseEq E f ∧ E ≤ₜ g :=
  h.2 g (CoarseEq.refl g)

/-- Synthesis, Lemma 2.3: the nonuniform coarse class of `f` contains a computable function
exactly when `f` is coarsely computable. -/
theorem exists_computable_ncEquiv_iff {f : ℕ → ℕ} :
    (∃ g, Computable g ∧ g ≡ₙ f) ↔ CoarselyComputable f := by
  constructor
  · rintro ⟨g, hg, hgf⟩
    obtain ⟨E, hE, hEg⟩ := hgf.exists_description
    exact ⟨E, hEg.computable hg, hE⟩
  · rintro ⟨D, hD, hDf⟩
    exact ⟨D, hD, hDf.ncEquiv⟩

/-! ## The statement C1 and its uniform analogue -/

/-- `g` is a representative of least Turing degree in the nonuniform coarse class of `f`. -/
def IsLeastNC (f g : ℕ → ℕ) : Prop := g ≡ₙ f ∧ ∀ h, h ≡ₙ f → g ≤ₜ h

/-- `g` is a representative of least Turing degree in the uniform coarse class of `f`. -/
def IsLeastUC (f g : ℕ → ℕ) : Prop := g ≡ᵤ f ∧ ∀ h, h ≡ᵤ f → g ≤ₜ h

/-- **C1** (research plan; the coarse instance of Gerdes, arXiv:2508.06925v1, Question 7):
every nonuniform coarse-equivalence class contains a representative of least Turing degree. -/
def C1 : Prop := ∀ f : ℕ → ℕ, ∃ g, IsLeastNC f g

/-- The analogue of C1 for uniform coarse equivalence. -/
def C1Uniform : Prop := ∀ f : ℕ → ℕ, ∃ g, IsLeastUC f g

/-- A least representative, uniform or not, is computable from every coarse description. -/
theorem IsLeastNC.tRed_description {f g D : ℕ → ℕ} (h : IsLeastNC f g) (hD : CoarseEq D f) :
    g ≤ₜ D :=
  h.2 D hD.ncEquiv

theorem IsLeastUC.tRed_description {f g D : ℕ → ℕ} (h : IsLeastUC f g) (hD : CoarseEq D f) :
    g ≤ₜ D :=
  h.2 D hD.ucEquiv

/-- Synthesis, Lemma 2.4 (two-witness obstruction).  If `f` is not coarsely computable and two
coarse descriptions of `f` have only computable common Turing lower bounds, then neither
coarse class of `f` has a representative of least Turing degree. -/
theorem no_least_of_two_witnesses {f D E : ℕ → ℕ} (hf : ¬ CoarselyComputable f)
    (hD : CoarseEq D f) (hE : CoarseEq E f)
    (hmin : ∀ h, h ≤ₜ D → h ≤ₜ E → Computable h) :
    (¬ ∃ g, IsLeastNC f g) ∧ (¬ ∃ g, IsLeastUC f g) := by
  constructor
  · rintro ⟨g, hg⟩
    have hcomp : Computable g := hmin g (hg.tRed_description hD) (hg.tRed_description hE)
    exact hf (exists_computable_ncEquiv_iff.mp ⟨g, hcomp, hg.1⟩)
  · rintro ⟨g, hg⟩
    have hcomp : Computable g := hmin g (hg.tRed_description hD) (hg.tRed_description hE)
    exact hf (exists_computable_ncEquiv_iff.mp ⟨g, hcomp, hg.1.ncEquiv⟩)

/-- The obstruction in the form used for the literature route: if every function computable
from *all* coarse descriptions of `f` is computable (trivial core) and `f` is not coarsely
computable, then neither coarse class of `f` has a least Turing degree. -/
theorem no_least_of_trivial_core {f : ℕ → ℕ} (hf : ¬ CoarselyComputable f)
    (hcore : ∀ g, (∀ D, CoarseEq D f → g ≤ₜ D) → Computable g) :
    (¬ ∃ g, IsLeastNC f g) ∧ (¬ ∃ g, IsLeastUC f g) := by
  constructor
  · rintro ⟨g, hg⟩
    have hcomp : Computable g := hcore g fun D hD => hg.tRed_description hD
    exact hf (exists_computable_ncEquiv_iff.mp ⟨g, hcomp, hg.1⟩)
  · rintro ⟨g, hg⟩
    have hcomp : Computable g := hcore g fun D hD => hg.tRed_description hD
    exact hf (exists_computable_ncEquiv_iff.mp ⟨g, hcomp, hg.1.ncEquiv⟩)

end CoarseDegrees
