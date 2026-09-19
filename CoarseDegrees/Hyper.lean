import CoarseDegrees.BudgetForcing
import CoarseDegrees.GenericDensity
import Mathlib.Analysis.Real.Sqrt

/-!
# Coarse classes without least hyperdegree

Formalization of Theorem 1.1 and Corollary 1.2 of research report 10
(`docs/research-reports/10/coarse_hyperdegrees.tex`), for the oracle `Z = ∅`.

* `Sigma11In Y X`, `HypIn Y X`: `X` is `Σ¹₁`, respectively `Δ¹₁`, in `Y`, by the Kleene normal
  form `n ∈ X ↔ ∃ f, ∀ k, T n (f ↾ k)` with `T` decidable in `Y`.
* The new mathematics, namely the budget forcing, the bridge lemma in forcing form and the
  construction of the generic pair, is proved in `CoarseDegrees.BudgetForcing` with nothing
  admitted.  What is admitted here is classical: two closure properties of `Δ¹₁`-reducibility,
  and one package of facts about Cohen forcing over `L_{ω₁^CK}` (facts (H2)--(H5) of the report).
  They are closed by `admit` and carry their references.
* `exists_hyp_minimal_pair`: for every budget there are `A`, `B` with `A △ B` obeying the budget,
  `Δ¹₁(A) ∩ Δ¹₁(B) = Δ¹₁`, and neither with a hyperarithmetic coarse description.
* `exists_no_least_hyperdegree`: a coarse class with no representative of least hyperdegree.
-/

noncomputable section

open Filter Topology
open scoped Classical Computability
open TuringDegrees
open scoped SetTuring

namespace CoarseDegrees

/-! ## Hyperarithmetic reducibility -/

/-- The set of codes `⟨n, ⌜s⌝⟩` of a relation between numbers and finite sequences. -/
def codeSet (T : ℕ → List ℕ → Prop) : Set ℕ :=
  {m | ∃ n s, m = Nat.pair n (Encodable.encode s) ∧ T n s}

/-- `X` is `Σ¹₁` in `Y` (Kleene normal form). -/
def Sigma11In (Y X : Set ℕ) : Prop :=
  ∃ T : ℕ → List ℕ → Prop, codeSet T ≤ᵀₛ Y ∧
    ∀ n, n ∈ X ↔ ∃ f : ℕ → ℕ, ∀ k, T n (List.ofFn fun i : Fin k => f i)

/-- `X` is hyperarithmetic (`Δ¹₁`) in `Y`. -/
def HypIn (Y X : Set ℕ) : Prop := Sigma11In Y X ∧ Sigma11In Y Xᶜ

/-- `X` is hyperarithmetic. -/
def Hyp (X : Set ℕ) : Prop := HypIn ∅ X

/-- `g ≤ₕ h` for total functions, through their graphs. -/
def HRed (g h : ℕ → ℕ) : Prop := HypIn (graph h) (graph g)

/-! ## Admitted classical facts -/

/-- A set Turing reducible to `Y` is `Σ¹₁` in `Y` (the function quantifier is vacuous). -/
theorem Sigma11In.of_setTuringReducible {X Y : Set ℕ} (h : X ≤ᵀₛ Y) : Sigma11In Y X := by
  refine ⟨fun n _ => n ∈ X, ?_, fun n => ⟨fun hn => ⟨fun _ => 0, fun _ => hn⟩, fun ⟨_, hf⟩ => hf 0⟩⟩
  have hcs : codeSet (fun n _ => n ∈ X) = {m | (Nat.unpair m).1 ∈ X} := by
    ext m
    constructor
    · rintro ⟨n, s, rfl, hn⟩
      simpa using hn
    · intro hm
      refine ⟨(Nat.unpair m).1, Denumerable.ofNat (List ℕ) (Nat.unpair m).2, ?_, hm⟩
      rw [Denumerable.encode_ofNat, Nat.pair_unpair]
  rw [hcs]
  have hred : ({m | (Nat.unpair m).1 ∈ X} : Set ℕ) ≤ᵀₛ X :=
    recursiveIn_precomp (RecursiveIn.oracle (characteristic X) (Set.mem_singleton _))
      (Computable.fst.comp Computable.unpair)
  exact hred.trans h

/-- Turing reducibility implies hyperarithmetic reducibility. -/
theorem HypIn.of_setTuringReducible {X Y : Set ℕ} (h : X ≤ᵀₛ Y) : HypIn Y X :=
  ⟨Sigma11In.of_setTuringReducible h,
    Sigma11In.of_setTuringReducible ((compl_reducible X).trans h)⟩

/-- Hyperarithmetic reducibility is transitive.
Rogers (1967), §16.8; Sacks (1990), Chapter II, Section 1. -/
theorem HypIn.trans {X Y Z : Set ℕ} (hXY : HypIn Y X) (hYZ : HypIn Z Y) : HypIn Z X := by
  admit

/-- **Cohen forcing over `L_{ω₁^CK}`** (facts (H2)--(H5) of report 10, Section 2.2).
S. Feferman, *Some applications of the notions of forcing and generic sets*, Fund. Math. 56
(1965), 325--345; G. E. Sacks, *Higher Recursion Theory* (1990), Chapter IV, Section 3.

Take `Name` to be the set of ranked formulas `ψ(x)` of the ramified language
`𝓛(ω₁^CK, 𝒢)` with one free number variable, let `dec σ ψ n true` mean `σ ⊩ ψ(n̄)` and
`dec σ ψ n false` mean `σ ⊩ ¬ψ(n̄)`, and let `𝒟` list the dense sets `{σ : σ decides φ}` for all
sentences `φ` of the language, ranked or not.  Then:

* `DecSys` axioms: forcing persists under extension, no condition forces a sentence and its
  negation, and every condition has an extension deciding a given sentence;
* *definability*: the forcing relation for the instances of a fixed ranked formula is `Δ¹₁`, and
  `Δ¹₁` is closed under number quantification, so `{n : ∃ α ⊇ σ, α ⊩ ψ(n̄)}` is hyperarithmetic
  (the uniqueness hypothesis is not even needed; it is included because it is what is available
  at the point of use);
* *naming and truth*: if `G` meets every `𝒟 k` then `G` is generic, `ω₁^G = ω₁^CK`, every set
  hyperarithmetic in `G` is `{n : 𝓜(G) ⊨ ψ(n̄)}` for a ranked `ψ`, and truth in `𝓜(G)` equals
  being forced by an initial segment of `G`;
* *hyperarithmetic dense sets are met*: for hyperarithmetic `C` and every `N`, the set of strings
  of the form `τ` followed by `|τ| + N + 1` bits disagreeing with `C` is dense and computable
  from `C`, hence hyperarithmetic, so a generic `G` has an initial segment in it. -/
theorem cohen_forcing_package :
    ∃ (Name : Type) (_ : Countable Name) (D : DecSys Name) (𝒟 : ℕ → Set (List Bool)),
      (∀ k σ, ∃ σ', σ <+: σ' ∧ σ' ∈ 𝒟 k) ∧
      (∀ ψ σ,
        (∀ n b c α α', σ <+: α → σ <+: α' → D.dec α ψ n b → D.dec α' ψ n c → b = c) →
          Hyp {n | ∃ α, σ <+: α ∧ D.dec α ψ n true}) ∧
      ∀ G : Set ℕ, (∀ k, ∃ σ, IsPrefixOf σ G ∧ σ ∈ 𝒟 k) →
        (∀ X, HypIn G X →
          ∃ ψ, ∀ n, (n ∈ X ↔ Truth D G ψ n true) ∧ (n ∉ X ↔ Truth D G ψ n false)) ∧
        (∀ C, Hyp C → ∀ N,
          ∃ τ, IsPrefixOf (ext (fun i => decide (i ∉ C)) τ (τ.length + N + 1)) G) := by
  admit

/-! ## Genericity and coarse descriptions -/

/-- If `X` has, for every `N`, an initial segment consisting of some `τ` followed by
`|τ| + N + 1` bits disagreeing with `C`, then `C` is not a coarse description of `X`.
(The counting is `le_count_symmDiff`.) -/
theorem not_setCoarseEq_of_ext {C X : Set ℕ}
    (h : ∀ N, ∃ τ, IsPrefixOf (ext (fun i => decide (i ∉ C)) τ (τ.length + N + 1)) X) :
    ¬ SetCoarseEq C X := by
  intro hCX
  have hb : ∀ i, (fun i => decide (i ∉ C)) i = true ↔ i ∉ C := by
    intro i
    simp
  have hev : ∀ᶠ n : ℕ in atTop, (count (symmDiff C X) n : ℝ) / n < 1 / 2 :=
    (tendsto_order.1 hCX).2 (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨τ, hτ⟩ := h N
  have hcount := le_count_symmDiff hb hτ
  set n := τ.length + (τ.length + N + 1) with hn
  have hlt := hN n (by omega)
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  rw [div_lt_iff₀ hnpos] at hlt
  have h2 : (n : ℝ) < 2 * (count (symmDiff C X) n : ℝ) := by
    have : n < 2 * count (symmDiff C X) n := by omega
    exact_mod_cast this
  linarith

/-! ## The main theorem -/

/-- **Report 10, Theorem 1.1** (for `Z = ∅`).  For every budget there are sets `A`, `B` such that
`A △ B` obeys the budget, every set hyperarithmetic in both `A` and `B` is hyperarithmetic, and
neither `A` nor `B` has a hyperarithmetic coarse description. -/
theorem exists_hyp_minimal_pair (𝔅 : Budget) :
    ∃ A B : Set ℕ, 𝔅.Obeys (symmDiff A B) ∧
      (∀ X, HypIn A X → HypIn B X → Hyp X) ∧
      (∀ C, Hyp C → ¬ SetCoarseEq C A) ∧ (∀ C, Hyp C → ¬ SetCoarseEq C B) := by
  obtain ⟨Name, hcount, D, 𝒟, hdense, hdef, hgen⟩ := cohen_forcing_package
  obtain ⟨A, B, hA, hB, hobey, -, -, hpair⟩ := exists_generic_pair D 𝔅 𝒟 hdense
  obtain ⟨hnameA, hextA⟩ := hgen A hA
  obtain ⟨hnameB, hextB⟩ := hgen B hB
  refine ⟨A, B, hobey, ?_, fun C hC => not_setCoarseEq_of_ext (hextA C hC),
    fun C hC => not_setCoarseEq_of_ext (hextB C hC)⟩
  intro X hXA hXB
  obtain ⟨ψ₀, h₀⟩ := hnameA X hXA
  obtain ⟨ψ₁, h₁⟩ := hnameB X hXB
  have hagree : ∀ n b c, Truth D A ψ₀ n b → Truth D B ψ₁ n c → b = c := by
    intro n b c hb hc
    cases b <;> cases c
    · rfl
    · exact absurd ((h₁ n).1.mpr hc) ((h₀ n).2.mpr hb)
    · exact absurd ((h₀ n).1.mpr hb) ((h₁ n).2.mpr hc)
    · rfl
  obtain ⟨σ, -, huniq, htruth⟩ := hpair ψ₀ ψ₁ hagree
  have hX : X = {n | ∃ α, σ <+: α ∧ D.dec α ψ₀ n true} := by
    ext n
    rw [(h₀ n).1, htruth n true]
    rfl
  rw [hX]
  exact hdef ψ₀ σ huniq

/-! ## No least hyperdegree -/

/-- `g` is a representative of least hyperdegree in the nonuniform coarse class of `f`. -/
def IsLeastHypNC (f g : ℕ → ℕ) : Prop := g ≡ₙ f ∧ ∀ h, h ≡ₙ f → HRed g h

/-- `g` is a representative of least hyperdegree in the uniform coarse class of `f`. -/
def IsLeastHypUC (f g : ℕ → ℕ) : Prop := g ≡ᵤ f ∧ ∀ h, h ≡ᵤ f → HRed g h

/-- A total function is computable from its graph. -/
theorem tRed_graph (g : ℕ → ℕ) : g ≤ₜ χ (graph g) := by
  have h1 : RecursiveIn {oracle (χ (graph g))} (fun k => (oracle (χ (graph g)) k).map (1 - ·)) :=
    recursiveIn_map (RecursiveIn.oracle _ (Set.mem_singleton _))
      ((Primrec.nat_sub.comp (Primrec.const 1) Primrec.id).to_comp)
  have h2 := Nat.RecursiveIn.rfind (RecursiveIn.iff_nat.mp h1)
  refine RecursiveIn.iff_nat.mpr (h2.of_eq fun a => ?_)
  apply Part.eq_some_iff.mpr
  rw [Nat.mem_rfind]
  refine ⟨?_, ?_⟩
  · simp [oracle, characteristicValue, graph]
  · intro m hm
    have hne : g a ≠ m := Nat.ne_of_gt hm
    simp [oracle, characteristicValue, graph, hne]

/-- Binary normalization at the level of sets: the set where a numerical coarse description of
`χ X` takes the value `1` is a coarse description of `X`, and it is computable from the
description. -/
theorem normalize_description {X : Set ℕ} {E : ℕ → ℕ} (hE : CoarseEq E (χ X)) :
    SetCoarseEq {n | E n = 1} X ∧ χ {n | E n = 1} ≤ₜ E := by
  constructor
  · refine DensityZero.mono hE ?_
    intro n hn
    simp only [disagree, Set.mem_setOf_eq]
    rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h1' : E n = 1 := h1
      simp [characteristicValue, h2, h1']
    · have h2' : ¬ E n = 1 := h2
      simpa [characteristicValue, h1] using h2'
  · have hc : Computable (fun v : ℕ => if v = 1 then 1 else 0) :=
      (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const 1)
        (Primrec.const 0)).to_comp
    have := recursiveIn_map (RecursiveIn.oracle (oracle E) (Set.mem_singleton _)) hc
    refine this.of_eq fun n => ?_
    simp [oracle, characteristicValue]

/-- A representative that is hyperarithmetically below two coarsely equal sets `A`, `B` with
`Δ¹₁(A) ∩ Δ¹₁(B) = Δ¹₁` yields a hyperarithmetic coarse description of `A`. -/
theorem hyp_description_of_least {A B : Set ℕ} {g : ℕ → ℕ}
    (hmin : ∀ X, HypIn A X → HypIn B X → Hyp X) (hg : g ≡ₙ χ A)
    (hgA : HRed g (χ A)) (hgB : HRed g (χ B)) :
    ∃ C, Hyp C ∧ SetCoarseEq C A := by
  -- the graph of `g` is hyperarithmetic
  have hA : HypIn A (graph g) := hgA.trans (HypIn.of_setTuringReducible (graph_tRed (χ A)))
  have hB : HypIn B (graph g) := hgB.trans (HypIn.of_setTuringReducible (graph_tRed (χ B)))
  have hG : Hyp (graph g) := hmin _ hA hB
  -- `g` computes a description, which normalizes to a set computable from the graph of `g`
  obtain ⟨E, hE, hEg⟩ := hg.exists_description
  obtain ⟨hC, hCE⟩ := normalize_description hE
  refine ⟨{n | E n = 1}, ?_, hC⟩
  have hred : ({n | E n = 1} : Set ℕ) ≤ᵀₛ graph g :=
    tRed_chi_iff.mp ((hCE.trans hEg).trans (tRed_graph g))
  exact (HypIn.of_setTuringReducible hred).trans hG

/-- **Report 10, Corollary 1.2.**  If the budget forces density zero, there is a set `A` whose
nonuniform and uniform coarse classes contain no representative of least hyperdegree, even when
representatives range over all total functions. -/
theorem exists_no_least_hyperdegree (𝔅 : Budget)
    (hzero : ∀ V : Set ℕ, 𝔅.Obeys V → DensityZero V) :
    ∃ A : Set ℕ, (¬ ∃ g, IsLeastHypNC (χ A) g) ∧ (¬ ∃ g, IsLeastHypUC (χ A) g) := by
  obtain ⟨A, B, hobey, hmin, hA, -⟩ := exists_hyp_minimal_pair 𝔅
  have hBA : CoarseEq (χ B) (χ A) := by
    rw [← setCoarseEq_iff]
    have : symmDiff B A = symmDiff A B := symmDiff_comm B A
    unfold SetCoarseEq
    rw [this]
    exact hzero _ hobey
  refine ⟨A, ?_, ?_⟩
  · rintro ⟨g, hg, hleast⟩
    obtain ⟨C, hC, hCA⟩ := hyp_description_of_least hmin hg
      (hleast _ (CoarseEq.refl _).ncEquiv) (hleast _ hBA.ncEquiv)
    exact hA C hC hCA
  · rintro ⟨g, hg, hleast⟩
    obtain ⟨C, hC, hCA⟩ := hyp_description_of_least hmin hg.ncEquiv
      (hleast _ (CoarseEq.refl _).ucEquiv) (hleast _ hBA.ucEquiv)
    exact hA C hC hCA

/-- The counting budget `|E ∩ [0,k)| ≤ √k`. -/
def sqrtBudget : Budget :=
  countingBudget Nat.sqrt (fun _ _ h => Nat.sqrt_le_sqrt h) (fun c => ⟨c * c, by simp [Nat.sqrt_eq]⟩)

/-- A set obeying the square-root budget has density zero. -/
theorem sqrtBudget_densityZero (V : Set ℕ) (hV : sqrtBudget.Obeys V) : DensityZero V := by
  have hcount : ∀ n, count V n ≤ Nat.sqrt n := by
    intro n
    have h := hV n n
    have hfil : ((Finset.range n).filter (· ∈ V)).filter (· < n) =
        (Finset.range n).filter (· ∈ V) := by
      apply Finset.filter_true_of_mem
      intro x hx
      exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    rw [hfil] at h
    exact h
  have hlim : Tendsto (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hlim
  have h1 : (count V n : ℝ) ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    have : count V n * count V n ≤ n :=
      le_trans (Nat.mul_le_mul (hcount n) (hcount n)) (Nat.sqrt_le n)
    have h2 : ((count V n * count V n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    rw [pow_two]
    exact_mod_cast h2
  calc (count V n : ℝ) / n ≤ Real.sqrt n / n :=
        div_le_div_of_nonneg_right h1 (Nat.cast_nonneg n)
    _ = 1 / Real.sqrt n := Real.sqrt_div_self'

/-- Report 10, Corollary 1.2, for a concrete budget: there is a set whose coarse classes contain
no representative of least hyperdegree. -/
theorem exists_no_least_hyperdegree' :
    ∃ A : Set ℕ, (¬ ∃ g, IsLeastHypNC (χ A) g) ∧ (¬ ∃ g, IsLeastHypUC (χ A) g) :=
  exists_no_least_hyperdegree sqrtBudget sqrtBudget_densityZero

/-! ## Minimal pairs inside a ball of the prefix-density metric

Budgets are closed under intersection, so the two constraints can be imposed at once: the
witnesses can be made coarsely equal *and* arbitrarily close in the prefix-density metric
`d(U,V) = supₙ ρₙ(U △ V)` in which the synthesis runs its Baire-category arguments.  Since
`d(A,B) ≤ r` says exactly that `A △ B` obeys `densityBudget r`, this places a hyperdegree
minimal pair inside every ball of that metric, however small the radius. -/

/-- **Hyperdegree minimal pairs inside an arbitrarily small ball.**  For every rational
`r > 0` there are `A`, `B` whose symmetric difference has density zero *and* satisfies
`|(A △ B) ∩ [0,n)| ≤ r·n` for every `n` — that is, `d(A,B) ≤ r` — such that every set
hyperarithmetic in both is hyperarithmetic, and neither has a hyperarithmetic coarse
description. -/
theorem exists_hyp_minimal_pair_close (r : ℚ) (hr : 0 < r) :
    ∃ A B : Set ℕ,
      DensityZero (symmDiff A B) ∧
      (∀ n, ((count (symmDiff A B) n : ℚ)) ≤ r * n) ∧
      (∀ X, HypIn A X → HypIn B X → Hyp X) ∧
      (∀ C, Hyp C → ¬ SetCoarseEq C A) ∧ (∀ C, Hyp C → ¬ SetCoarseEq C B) := by
  obtain ⟨A, B, hobey, hmin, hA, hB⟩ :=
    exists_hyp_minimal_pair (sqrtBudget.inter (densityBudget r hr))
  exact ⟨A, B, sqrtBudget_densityZero _ hobey.left, densityBudget_le hr hobey.right,
    hmin, hA, hB⟩

/-- The same, in the form used by Corollary 1.2: the class of `A` has no representative of
least hyperdegree, and the second witness lies within `r` of the first. -/
theorem exists_no_least_hyperdegree_close (r : ℚ) (hr : 0 < r) :
    ∃ A B : Set ℕ,
      (∀ n, ((count (symmDiff A B) n : ℚ)) ≤ r * n) ∧
      CoarseEq (χ B) (χ A) ∧
      (¬ ∃ g, IsLeastHypNC (χ A) g) ∧ (¬ ∃ g, IsLeastHypUC (χ A) g) := by
  obtain ⟨A, B, hzero, hclose, hmin, hA, -⟩ := exists_hyp_minimal_pair_close r hr
  have hBA : CoarseEq (χ B) (χ A) := by
    rw [← setCoarseEq_iff]
    unfold SetCoarseEq
    rw [symmDiff_comm B A]
    exact hzero
  refine ⟨A, B, hclose, hBA, ?_, ?_⟩
  · rintro ⟨g, hg, hleast⟩
    obtain ⟨C, hC, hCA⟩ := hyp_description_of_least hmin hg
      (hleast _ (CoarseEq.refl _).ncEquiv) (hleast _ hBA.ncEquiv)
    exact hA C hC hCA
  · rintro ⟨g, hg, hleast⟩
    obtain ⟨C, hC, hCA⟩ := hyp_description_of_least hmin hg.ncEquiv
      (hleast _ (CoarseEq.refl _).ucEquiv) (hleast _ hBA.ucEquiv)
    exact hA C hC hCA

end CoarseDegrees
