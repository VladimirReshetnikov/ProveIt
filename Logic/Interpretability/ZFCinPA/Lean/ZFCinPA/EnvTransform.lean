import ZFCinPA.ConstructibleInterpretation
import ZFCinPA.NumeralOmega

/-!
# The constructible environment transform

The separation and replacement obligations of
`ConstructibleInterpretation.provable_falsum_ZF_of_ZFC` concern internal
formula codes `K` that may be nonstandard, with nonstandardly many free
variables. The reflection argument that discharges them (design:
`Computability/BusyBeaver/Research/ZFC/pa_internalization.md`) reads *every*
variable of `K` from one assignment `t : ω → V`, an internal environment in the
sense of `BoundedZFCConsistency.InternalSat` (`IsEnvOn`, `econs`, `applyV`), so
that one set-theoretic variable stands for all of them.

`envForm d K` is that transform, relativized to `L`, as one represented
`UformulaRec1` construction whose parameter is the binder depth `d`:

* a bound variable `#k` reads slot `k` of the environment and a free
  variable `&i` reads slot `d + i` (`idx`); an atom `u R v` becomes
  `∃x ∃y (t(⌜idx u⌝) = x ∧ t(⌜idx v⌝) = y ∧ x R y)`, the slots being read
  through the von Neumann numeral formulas `UniformStatement.numChainCode`;
* `∃⁰ q` becomes `∃y ∃t' (t' = econs y t ∧ y ∈ L ∧ q')` and `∀⁰ q` its dual,
  where `q'` is the transform of `q` at depth `d + 1`.

Every output is a semiformula in exactly one variable, the environment
(`isSemiformula_envForm`): no free variable of `K` survives. The fixed pieces
are BusyBeaver's named formulas (`pmemF`, `econsAtomF`) and `domL`, so their
semantics is available in every model of ZF through the `nsat_*` lemmas.
-/

set_option autoImplicit false

namespace LeanProofs.ZFCinPA.EnvTransform

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ConstructibleInterpretation

/-! ## Fixed pieces -/

section Fixed

open SetTheory.BusyBeaver.ZFC.NamedZF SetTheory.BusyBeaver.ZFC.InternalRank
  SetTheory.BusyBeaver.ZFC.ConstructibleDef

/-- A named formula with free names among `0, …, n`, as a semisentence in
`n + 1` variables (name `i` is bound variable `#i`). -/
def piece (n : ℕ) (φ : NForm) : SetTheorySemisentence (n + 1) :=
  Rew.rewrite (fun _ => (#0 : Semiterm ℒₛₑₜ Empty (n + 1))) ▹ toSet (n + 1) (toForm id φ)

/-- `⟨m, x⟩ ∈ t`, with `t = #3`, `m = #0`, `x = #2`. -/
def appXS : SetTheorySemisentence 4 := piece 3 (pmemF 3 0 2)

/-- `⟨m, y⟩ ∈ t`, with `t = #3`, `m = #0`, `y = #1`. -/
def appYS : SetTheorySemisentence 4 := piece 3 (pmemF 3 0 1)

/-- `x ∈ y`, with `x = #1`, `y = #0`. -/
def memXYS : SetTheorySemisentence 3 := .rel Language.Mem.mem ![#1, #0]

/-- `x = y`, with `x = #1`, `y = #0`. -/
def eqXYS : SetTheorySemisentence 3 := .rel Language.Eq.eq ![#1, #0]

/-- `t' = econs y t`, with `t' = #0`, `y = #1`, `t = #2`. -/
def econsS : SetTheorySemisentence 3 := piece 2 (econsAtomF 0 1 2)

/-- `y ∈ L`, with `y = #1`. -/
noncomputable def domYS : SetTheorySemisentence 3 := domL ⇜ ![#1]

/-- The pieces as formulas (their codes are the codes of the semisentences). -/
def appXP : SetTheorySemiproposition 4 := Rewriting.emb appXS
def appYP : SetTheorySemiproposition 4 := Rewriting.emb appYS
def memXYP : SetTheorySemiproposition 3 := Rewriting.emb memXYS
def eqXYP : SetTheorySemiproposition 3 := Rewriting.emb eqXYS
def econsP : SetTheorySemiproposition 3 := Rewriting.emb econsS
noncomputable def domYP : SetTheorySemiproposition 3 := Rewriting.emb domYS

@[irreducible] def appXCode : ℕ := appXP.toNat
@[irreducible] def appYCode : ℕ := appYP.toNat
@[irreducible] def memXYCode : ℕ := memXYP.toNat
@[irreducible] def eqXYCode : ℕ := eqXYP.toNat

end Fixed

/-! ## The represented transform

The quantifier clauses embed the codes of `econsP` and `domYP`. These are
deep formulas, so their codes are far too large to appear as numeral terms
inside an arithmetic formula (the numeral term of a code is its binary
expansion). They therefore enter the construction through its *parameter*,
`⟪d, ⟪⌜econsP⌝, ⟪⌜∼econsP⌝, ⟪⌜domYP⌝, ⌜∼domYP⌝⟫⟫⟫⟫`, of which only the depth
`d` changes under binders. The small atom codes stay numerals. -/

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The environment slot read by a variable term at binder depth `d`: `#k`
reads slot `k`, `&i` reads slot `d + i`. -/
noncomputable def idx (d t : V) : V :=
  if π₁ (t - 1) = 0 then π₂ (t - 1) else d + π₂ (t - 1)

@[simp] lemma idx_bvar (d k : V) : idx d (^#k) = k := by
  simp [idx, qqBvar]

@[simp] lemma idx_fvar (d i : V) : idx d (^&i) = d + i := by
  simp [idx, qqFvar]

noncomputable def idxGraph : 𝚺₀.Semisentence 3 := .mkSigma
  “y d t. ∃ p <⁺ t, !subDef p t 1 ∧ ∃ a <⁺ p, !pi₁Def a p ∧ ∃ b <⁺ p, !pi₂Def b p ∧
    ((a = 0 ∧ y = b) ∨ (a ≠ 0 ∧ y = d + b))”

instance idx_defined : 𝚺₀-Function₂ (idx : V → V → V) via idxGraph := .mk fun v ↦ by
  simp only [idxGraph, idx]
  by_cases h : π₁ (v 2 - 1) = 0 <;> simp [h]

instance idx_definable : 𝚺₀-Function₂ (idx : V → V → V) := idx_defined.to_definable

/-- The transformed atom `t(⌜a⌝) R t(⌜b⌝)`; `R = 0` is equality, anything else
membership (the codes of `ℒₛₑₜ`'s two relation symbols are `0` and `1`). -/
noncomputable def atomCode (R a b : V) : V :=
  ^∃ ^∃ ((^∃ (numChainCode a ^⋏ ↑appXCode)) ^⋏
    ((^∃ (numChainCode b ^⋏ ↑appYCode)) ^⋏ (if R = 0 then ↑eqXYCode else ↑memXYCode)))

noncomputable def atomGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y R a b. ∃ na, !numChainGraph na a ∧ ∃ nb, !numChainGraph nb b ∧
    ∃ c₁, !qqAndDef c₁ na ↑appXCode ∧ ∃ e₁, !qqExsDef e₁ c₁ ∧
    ∃ c₂, !qqAndDef c₂ nb ↑appYCode ∧ ∃ e₂, !qqExsDef e₂ c₂ ∧
    ∃ r, ((R = 0 ∧ r = ↑eqXYCode) ∨ (R ≠ 0 ∧ r = ↑memXYCode)) ∧
    ∃ c₃, !qqAndDef c₃ e₂ r ∧ ∃ c₄, !qqAndDef c₄ e₁ c₃ ∧
    ∃ x₁, !qqExsDef x₁ c₄ ∧ !qqExsDef y x₁”

instance atomCode_defined : 𝚺₁-Function₃ (atomCode : V → V → V → V) via atomGraph :=
  .mk fun v ↦ by
    simp only [atomGraph, atomCode]
    by_cases h : v 1 = 0 <;> simp [h, numeral_eq_natCast]

/-- The transformed atom of the term vector `v` at depth `d`. -/
noncomputable def atomOf (d R v : V) : V := atomCode R (idx d v.[0]) (idx d v.[1])

noncomputable def atomOfGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y d R v. ∃ t₀, !nthDef t₀ v 0 ∧ ∃ t₁, !nthDef t₁ v 1 ∧
    ∃ a, !idxGraph a d t₀ ∧ ∃ b, !idxGraph b d t₁ ∧ !atomGraph y R a b”

instance atomOf_defined : 𝚺₁-Function₃ (atomOf : V → V → V → V) via atomOfGraph :=
  .mk fun v ↦ by simp [atomOfGraph, atomOf]

/-- `∀y ∀t' (¬E ∨ (¬D ∨ q))` for the negated econs and domain codes `a`, `b`. -/
noncomputable def allWrap (a b q : V) : V := ^∀ ^∀ (a ^⋎ (b ^⋎ q))

/-- `∃y ∃t' (E ∧ (D ∧ q))` for the econs and domain codes `a`, `b`. -/
noncomputable def exsWrap (a b q : V) : V := ^∃ ^∃ (a ^⋏ (b ^⋏ q))

noncomputable def allWrapGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y a b q. ∃ x, !qqOrDef x b q ∧ ∃ z, !qqOrDef z a x ∧ ∃ w, !qqAllDef w z ∧ !qqAllDef y w”

noncomputable def exsWrapGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y a b q. ∃ x, !qqAndDef x b q ∧ ∃ z, !qqAndDef z a x ∧ ∃ w, !qqExsDef w z ∧ !qqExsDef y w”

instance allWrap_defined : 𝚺₁-Function₃ (allWrap : V → V → V → V) via allWrapGraph :=
  .mk fun v ↦ by simp [allWrapGraph, allWrap]

instance exsWrap_defined : 𝚺₁-Function₃ (exsWrap : V → V → V → V) via exsWrapGraph :=
  .mk fun v ↦ by simp [exsWrapGraph, exsWrap]

/-! ### The parameter -/

/-- The depth carried by a parameter. -/
noncomputable abbrev depthOf (c : V) : V := π₁ c
/-- The code of `econsP` carried by a parameter. -/
noncomputable abbrev econsOf (c : V) : V := π₁ (π₂ c)
/-- The code of `∼econsP` carried by a parameter. -/
noncomputable abbrev negEconsOf (c : V) : V := π₁ (π₂ (π₂ c))
/-- The code of `domYP` carried by a parameter. -/
noncomputable abbrev domOf (c : V) : V := π₁ (π₂ (π₂ (π₂ c)))
/-- The code of `∼domYP` carried by a parameter. -/
noncomputable abbrev negDomOf (c : V) : V := π₂ (π₂ (π₂ (π₂ c)))

namespace EnvForm

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y c k R v. ∃ d <⁺ c, !pi₁Def d c ∧ !atomOfGraph y d R v”
  nrel := .mkSigma “y c k R v. ∃ d <⁺ c, !pi₁Def d c ∧ ∃ z, !atomOfGraph z d R v ∧
    !(negGraph ℒₛₑₜ) y z”
  verum := .mkSigma “y c. !qqVerumDef y”
  falsum := .mkSigma “y c. !qqFalsumDef y”
  and := .mkSigma “y c p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or := .mkSigma “y c p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all := .mkSigma “y c p₁ y₁. ∃ c₁ <⁺ c, !pi₂Def c₁ c ∧ ∃ c₂ <⁺ c₁, !pi₂Def c₂ c₁ ∧
    ∃ a <⁺ c₂, !pi₁Def a c₂ ∧ ∃ c₃ <⁺ c₂, !pi₂Def c₃ c₂ ∧ ∃ b <⁺ c₃, !pi₂Def b c₃ ∧
    !allWrapGraph y a b y₁”
  exs := .mkSigma “y c p₁ y₁. ∃ c₁ <⁺ c, !pi₂Def c₁ c ∧ ∃ a <⁺ c₁, !pi₁Def a c₁ ∧
    ∃ c₂ <⁺ c₁, !pi₂Def c₂ c₁ ∧ ∃ c₃ <⁺ c₂, !pi₂Def c₃ c₂ ∧ ∃ b <⁺ c₃, !pi₁Def b c₃ ∧
    !exsWrapGraph y a b y₁”
  allChanges := .mkSigma “c' c. ∃ d <⁺ c, !pi₁Def d c ∧ ∃ e <⁺ c, !pi₂Def e c ∧ !pairDef c' (d + 1) e”
  exsChanges := .mkSigma “c' c. ∃ d <⁺ c, !pi₁Def d c ∧ ∃ e <⁺ c, !pi₂Def e c ∧ !pairDef c' (d + 1) e”

noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel := fun c _ R v ↦ atomOf (depthOf c) R v
  nrel := fun c _ R v ↦ neg ℒₛₑₜ (atomOf (depthOf c) R v)
  verum := fun _ ↦ ^⊤
  falsum := fun _ ↦ ^⊥
  and := fun _ _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or := fun _ _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all := fun c _ y₁ ↦ allWrap (negEconsOf c) (negDomOf c) y₁
  exs := fun c _ y₁ ↦ exsWrap (econsOf c) (domOf c) y₁
  allChanges := fun c ↦ ⟪π₁ c + 1, π₂ c⟫
  exsChanges := fun c ↦ ⟪π₁ c + 1, π₂ c⟫
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]

end EnvForm

open EnvForm

/-- The environment transform with explicit parameter `c` (depth and the four
fixed codes). -/
noncomputable def envFormP (c p : V) : V := construction.result ℒₛₑₜ c p

noncomputable def envFormPGraph : 𝚺₁.Semisentence 3 := blueprint.result ℒₛₑₜ

instance envFormP.defined : 𝚺₁-Function₂[V] envFormP via envFormPGraph :=
  construction.result_defined

instance envFormP.definable : 𝚺₁-Function₂[V] envFormP := envFormP.defined.to_definable

/-- The four fixed codes. -/
noncomputable def envConsts : V :=
  ⟪(⌜econsP⌝ : V), ⟪(⌜∼econsP⌝ : V), ⟪(⌜domYP⌝ : V), (⌜∼domYP⌝ : V)⟫⟫⟫

/-- **The `L`-relativized environment transform** of `p` at binder depth `d`. -/
noncomputable def envForm (d p : V) : V := envFormP ⟪d, envConsts⟫ p

instance envForm.definable : 𝚺₁-Function₂[V] envForm := by
  unfold envForm
  definability

section Equations

variable {d : V}

@[simp] lemma envForm_rel {k R v : V} (hR : (ℒₛₑₜ).IsRel k R) (hv : IsUTermVec ℒₛₑₜ k v) :
    envForm d (^rel k R v) = atomOf d R v := by
  simp [envForm, envFormP, hR, hv, construction, depthOf]

@[simp] lemma envForm_nrel {k R v : V} (hR : (ℒₛₑₜ).IsRel k R) (hv : IsUTermVec ℒₛₑₜ k v) :
    envForm d (^nrel k R v) = neg ℒₛₑₜ (atomOf d R v) := by
  simp [envForm, envFormP, hR, hv, construction, depthOf]

@[simp] lemma envForm_verum : envForm d (^⊤ : V) = ^⊤ := by
  simp [envForm, envFormP, construction]

@[simp] lemma envForm_falsum : envForm d (^⊥ : V) = ^⊥ := by
  simp [envForm, envFormP, construction]

@[simp] lemma envForm_and {p q : V} (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    envForm d (p ^⋏ q) = envForm d p ^⋏ envForm d q := by
  simp [envForm, envFormP, hp, hq, construction]

@[simp] lemma envForm_or {p q : V} (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    envForm d (p ^⋎ q) = envForm d p ^⋎ envForm d q := by
  simp [envForm, envFormP, hp, hq, construction]

@[simp] lemma envForm_all {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    envForm d (^∀ p) = ^∀ ^∀ ((⌜∼econsP⌝ : V) ^⋎ ((⌜∼domYP⌝ : V) ^⋎ envForm (d + 1) p)) := by
  simp [envForm, envFormP, hp, construction, allWrap, envConsts, negEconsOf, negDomOf]

@[simp] lemma envForm_exs {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    envForm d (^∃ p) = ^∃ ^∃ ((⌜econsP⌝ : V) ^⋏ ((⌜domYP⌝ : V) ^⋏ envForm (d + 1) p)) := by
  simp [envForm, envFormP, hp, construction, exsWrap, envConsts, econsOf, domOf]

end Equations

/-! ## Well-formedness: one variable, the environment -/

section WellFormed

private lemma wf_appX : IsSemiformula ℒₛₑₜ ((4 : ℕ) : V) ((appXCode : ℕ) : V) := by
  unfold appXCode; exact leafArity appXP

private lemma wf_appY : IsSemiformula ℒₛₑₜ ((4 : ℕ) : V) ((appYCode : ℕ) : V) := by
  unfold appYCode; exact leafArity appYP

private lemma wf_memXY : IsSemiformula ℒₛₑₜ ((3 : ℕ) : V) ((memXYCode : ℕ) : V) := by
  unfold memXYCode; exact leafArity memXYP

private lemma wf_eqXY : IsSemiformula ℒₛₑₜ ((3 : ℕ) : V) ((eqXYCode : ℕ) : V) := by
  unfold eqXYCode; exact leafArity eqXYP

/-- A transformed atom mentions only the environment. -/
lemma isSemiformula_atomCode (R a b : V) : IsSemiformula ℒₛₑₜ 1 (atomCode R a b) := by
  have hN : ∀ x : V, IsSemiformula ℒₛₑₜ ((4 : ℕ) : V) (numChainCode x) := fun x =>
    isSemiformula_of_le (isSemiformula_numChainCode x) (by norm_num)
  have hR : IsSemiformula ℒₛₑₜ ((3 : ℕ) : V)
      (if R = 0 then ((eqXYCode : ℕ) : V) else ((memXYCode : ℕ) : V)) := by
    split
    · exact wf_eqXY
    · exact wf_memXY
  have h4 : ((4 : ℕ) : V) = 1 + 1 + 1 + 1 := by norm_num
  have h3 : ((3 : ℕ) : V) = 1 + 1 + 1 := by norm_num
  rw [h4] at hN
  rw [h3] at hR
  have hX := wf_appX (V := V)
  have hY := wf_appY (V := V)
  rw [h4] at hX hY
  unfold atomCode
  simp only [IsSemiformula.exs, IsSemiformula.and]
  exact ⟨⟨hN a, hX⟩, ⟨hN b, hY⟩, hR⟩

lemma isSemiformula_atomOf (d R v : V) : IsSemiformula ℒₛₑₜ 1 (atomOf d R v) :=
  isSemiformula_atomCode _ _ _

/-- **Every transform is a formula in the environment variable alone.** -/
theorem isSemiformula_envForm {d p n : V} (hp : IsSemiformula ℒₛₑₜ n p) :
    IsSemiformula ℒₛₑₜ 1 (envForm d p) := by
  have hE : IsSemiformula ℒₛₑₜ 3 (⌜econsP⌝ : V) := by
    simpa using LO.FirstOrder.Semiformula.quote_isSemiformula (V := V) econsP
  have hNE : IsSemiformula ℒₛₑₜ 3 (⌜∼econsP⌝ : V) := by
    simpa using LO.FirstOrder.Semiformula.quote_isSemiformula (V := V) (∼econsP)
  have hD : IsSemiformula ℒₛₑₜ 3 (⌜domYP⌝ : V) := by
    simpa using LO.FirstOrder.Semiformula.quote_isSemiformula (V := V) domYP
  have hND : IsSemiformula ℒₛₑₜ 3 (⌜∼domYP⌝ : V) := by
    simpa using LO.FirstOrder.Semiformula.quote_isSemiformula (V := V) (∼domYP)
  have h13 : ∀ q : V, IsSemiformula ℒₛₑₜ 1 q → IsSemiformula ℒₛₑₜ 3 q :=
    fun q hq => isSemiformula_of_le hq (by norm_num)
  have h111 : (1 + 1 + 1 : V) = 3 := by norm_num
  have key := construction.semiformula_result_induction (L := ℒₛₑₜ)
    (P := fun c _ _ y => π₂ c = envConsts → IsSemiformula ℒₛₑₜ 1 y)
    (by definability)
    (fun _ c _ R v _ _ _ => isSemiformula_atomOf _ R v)
    (fun _ c _ R v _ _ _ => (isSemiformula_atomOf _ R v).neg)
    (fun _ _ _ => by simp [construction])
    (fun _ _ _ => by simp [construction])
    (fun _ _ _ _ _ _ ih₁ ih₂ hc => by
      change IsSemiformula ℒₛₑₜ 1 (_ ^⋏ _)
      exact IsSemiformula.and.mpr ⟨ih₁ hc, ih₂ hc⟩)
    (fun _ _ _ _ _ _ ih₁ ih₂ hc => by
      change IsSemiformula ℒₛₑₜ 1 (_ ^⋎ _)
      exact IsSemiformula.or.mpr ⟨ih₁ hc, ih₂ hc⟩)
    (fun _ c p _ ih hc => by
      have hy := ih (by simp [construction, hc])
      change IsSemiformula ℒₛₑₜ 1 (allWrap (negEconsOf c) (negDomOf c)
        (construction.result ℒₛₑₜ (construction.allChanges c) p))
      have h1 : negEconsOf c = ⌜∼econsP⌝ := by simp [negEconsOf, hc, envConsts]
      have h2 : negDomOf c = ⌜∼domYP⌝ := by simp [negDomOf, hc, envConsts]
      rw [h1, h2, allWrap, IsSemiformula.all, IsSemiformula.all, h111]
      simp only [IsSemiformula.or]
      exact ⟨hNE, hND, h13 _ hy⟩)
    (fun _ c p _ ih hc => by
      have hy := ih (by simp [construction, hc])
      change IsSemiformula ℒₛₑₜ 1 (exsWrap (econsOf c) (domOf c)
        (construction.result ℒₛₑₜ (construction.exsChanges c) p))
      have h1 : econsOf c = ⌜econsP⌝ := by simp [econsOf, hc, envConsts]
      have h2 : domOf c = ⌜domYP⌝ := by simp [domOf, hc, envConsts]
      rw [h1, h2, exsWrap, IsSemiformula.exs, IsSemiformula.exs, h111]
      simp only [IsSemiformula.and]
      exact ⟨hE, hD, h13 _ hy⟩)
    (param := ⟪d, envConsts⟫) hp
  exact key (by simp)

end WellFormed

end LeanProofs.ZFCinPA.EnvTransform
