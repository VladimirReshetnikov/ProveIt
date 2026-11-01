import ZFCinPA.LStepExT

set_option autoImplicit false
noncomputable section

/-!
# Closure points of a class function on ordinals

The final templates of the reflection generator need, above any ordinal `α`, a
nonzero limit `β` closed under the reflection function `F`. `F` is a class
(it is a placeholder), so the iteration is carried out by hand, in the
resource style of `LStepEx.wb_exists`: every use of Separation or Replacement
for a formula mentioning `F` is an explicit hypothesis, discharged in template
models by `LTemplate.sep_iff`/`repl_iff`.

* `HStep F x y`: `y = succ (x ∪ ⋃ F[x])`, the inflationary step dominating `F`;
* `Chain F α n f`: `f` is a function on `n + 1` with ordinal values, `f 0 = α`
  and `f (k + 1) = HStep (f k)`;
* `chain_exists`, `chain_agree`: chains exist for every `n ∈ ω` and agree;
* `orbit_closure`: the union of the chain values is a nonzero limit above
  `α` closed under `F`.
-/

namespace LeanProofs.ZFCinPA.LIterate

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.LPieces LeanProofs.ZFCinPA.LStepAnd
open LeanProofs.ZFCinPA.LStepExT (least_ord ord_vunion mem_vsucc_of_sub)
open SetTheory.BusyBeaver.ZFC.InternalOrd
open LeanProofs.BoundedZFCConsistency (IsFunctionOn)

variable {V : Type*} [SetStructure V] (H : _root_.SetTheory.ZFAxioms (memRel V))
  (hR : Regular (memRel V))

local notation "ω" => _root_.SetTheory.omegaV H
local notation "∅" => _root_.SetTheory.vempty H
local notation "succ" => _root_.SetTheory.vsucc H
local notation "⟪" a ", " b "⟫ₖ" => _root_.SetTheory.kpair H a b

/-- **Induction on `ω`** for a predicate with a separation resource. -/
theorem omega_ind_res {Φ : V → Prop} (hsep : ∃ S : V, ∀ n, n ∈ S ↔ n ∈ ω ∧ Φ n)
    (h₀ : Φ ∅) (hs : ∀ n, n ∈ ω → Φ n → Φ (succ n)) : ∀ n, n ∈ ω → Φ n := by
  obtain ⟨S, hS⟩ := hsep
  intro n hn
  have hind : _root_.SetTheory.inductiveV H S :=
    ⟨(hS _).2 ⟨_root_.SetTheory.vempty_in_omega H, h₀⟩, fun x hx =>
      (hS _).2 ⟨_root_.SetTheory.omega_succ H x ((hS x).1 hx).1,
        hs x ((hS x).1 hx).1 ((hS x).1 hx).2⟩⟩
  exact ((hS n).1 (((_root_.SetTheory.omega_spec H n).1 hn).2 S hind)).2

/-- `y = succ (x ∪ ⋃ F[x])`. -/
def HStep (F : V → V → Prop) (x y : V) : Prop :=
  ∃ m, (∀ w, w ∈ m ↔ w ∈ x ∨ ∃ a, a ∈ x ∧ ∃ g, F a g ∧ w ∈ g) ∧ ∀ z, z ∈ y ↔ z ∈ m ∨ z = m

/-- A chain of length `n + 1` from `α`, with ordinal values. -/
def Chain (F : V → V → Prop) (α n f : V) : Prop :=
  IsFunctionOn H f (succ n) ∧ ⟪∅, α⟫ₖ ∈ f ∧ (∀ k x, ⟪k, x⟫ₖ ∈ f → Ord (memRel V) x) ∧
    ∀ k, k ∈ n → ∀ x y, ⟪k, x⟫ₖ ∈ f → ⟪succ k, y⟫ₖ ∈ f → HStep F x y

section Step

variable {F : V → V → Prop} (htot : Tot F)
  (himg : ∀ x : V, Ord (memRel V) x → ∃ Y : V, ∀ g, g ∈ Y ↔ ∃ a, a ∈ x ∧ F a g)
include H hR htot himg

/-- The step exists at every ordinal, is an ordinal above it, and contains
the values of `F` below it. -/
theorem hstep_exists {x : V} (hx : Ord (memRel V) x) :
    ∃ y, HStep F x y ∧ Ord (memRel V) y ∧ x ∈ y ∧ ∀ a, a ∈ x → ∀ g, F a g → g ∈ y := by
  obtain ⟨Y, hY⟩ := himg x hx
  have hYo : ∀ g, g ∈ Y → Ord (memRel V) g := by
    intro g hg
    obtain ⟨a, ha, hFa⟩ := (hY g).1 hg
    obtain ⟨g', ho, -, -, u⟩ := htot a (ord_of_mem hx ha)
    rw [u g hFa]
    exact ho
  have hUo := LStepExT.ord_vunion H hYo
  have hmo : Ord (memRel V) (_root_.SetTheory.vcup H x (_root_.SetTheory.vunion H Y)) := by
    rcases vcup_ord H hR hx hUo with h | h <;> rw [h] <;> assumption
  refine ⟨_, ⟨_root_.SetTheory.vcup H x (_root_.SetTheory.vunion H Y), fun w => ?_,
    fun z => _root_.SetTheory.vsucc_spec H _ z⟩, ord_succ H hmo, ?_, fun a ha g hFa => ?_⟩
  · refine (_root_.SetTheory.vcup_spec H x _ w).trans (or_congr Iff.rfl
      ((_root_.SetTheory.vunion_spec H Y w).trans ⟨fun ⟨g, hwg, hgY⟩ => ?_, fun ⟨a, ha, g, hFa, hwg⟩ => ?_⟩))
    · obtain ⟨a, ha, hFa⟩ := (hY g).1 hgY
      exact ⟨a, ha, g, hFa, hwg⟩
    · exact ⟨g, hwg, (hY g).2 ⟨a, ha, hFa⟩⟩
  · exact mem_vsucc_of_sub H hR hx hmo fun z hz => (_root_.SetTheory.vcup_spec H _ _ z).2 (Or.inl hz)
  · exact mem_vsucc_of_sub H hR (hYo g ((hY g).2 ⟨a, ha, hFa⟩)) hmo fun z hz =>
      (_root_.SetTheory.vcup_spec H _ _ z).2
        (Or.inr ((_root_.SetTheory.vunion_spec H Y z).2 ⟨g, hz, (hY g).2 ⟨a, ha, hFa⟩⟩))

omit hR htot himg in
/-- The step is functional. -/
theorem hstep_unique {x y y' : V} (h : HStep F x y) (h' : HStep F x y') : y = y' := by
  obtain ⟨m, hm, hy⟩ := h
  obtain ⟨m', hm', hy'⟩ := h'
  have e : m = m' := H.ext _ _ fun w => (hm w).trans (hm' w).symm
  subst e
  exact H.ext _ _ fun z => (hy z).trans (hy' z).symm

end Step

/-! ## Chains -/

section Chains

variable {F : V → V → Prop} (htot : Tot F)
  (himg : ∀ x : V, Ord (memRel V) x → ∃ Y : V, ∀ g, g ∈ Y ↔ ∃ a, a ∈ x ∧ F a g)
  {α : V} (hα : Ord (memRel V) α)

lemma nat_ord {n : V} (hn : n ∈ ω) : Ord (memRel V) n :=
  ord_of_mem (SetTheory.BusyBeaver.ZFC.ConstructibleZF.ord_omega H) hn

include H hR htot himg hα in
/-- **Chains exist** for every length in `ω`. -/
theorem chain_exists (hsepC : ∃ S : V, ∀ n, n ∈ S ↔ n ∈ ω ∧ ∃ f, Chain H F α n f) :
    ∀ n, n ∈ ω → ∃ f, Chain H F α n f := by
  refine omega_ind_res H hsepC ?_ ?_
  · -- the one-point chain
    refine ⟨_root_.SetTheory.vsingle H ⟪∅, α⟫ₖ, ⟨fun x y y' hy hy' => ?_, fun x hx => ?_, fun p hp => ?_⟩,
      (_root_.SetTheory.vsingle_spec H _ _).2 rfl, fun k x hkx => ?_, fun k hk => ?_⟩
    · have e := (_root_.SetTheory.vsingle_spec H _ _).1 hy
      have e' := (_root_.SetTheory.vsingle_spec H _ _).1 hy'
      exact ((_root_.SetTheory.kpair_inj H _ _ _ _ e).2).trans ((_root_.SetTheory.kpair_inj H _ _ _ _ e').2).symm
    · rcases (_root_.SetTheory.vsucc_spec H _ x).1 hx with hx | rfl
      · exact absurd hx (_root_.SetTheory.vempty_spec H x)
      · exact ⟨α, (_root_.SetTheory.vsingle_spec H _ _).2 rfl⟩
    · exact ⟨∅, α, _root_.SetTheory.vsucc_self H _, (_root_.SetTheory.vsingle_spec H _ _).1 hp⟩
    · rw [(_root_.SetTheory.kpair_inj H _ _ _ _ ((_root_.SetTheory.vsingle_spec H _ _).1 hkx)).2]
      exact hα
    · exact absurd hk (_root_.SetTheory.vempty_spec H k)
  · rintro n hn ⟨f, hfun, hzero, hord, hstep⟩
    have hno := nat_ord H hn
    obtain ⟨x, hx⟩ := hfun.2.1 n (_root_.SetTheory.vsucc_self H n)
    obtain ⟨y, hy, hyo, -, -⟩ := hstep_exists H hR htot himg (hord n x hx)
    -- no pair of `f` has key `succ n`
    have hkey : ∀ k z, ⟪k, z⟫ₖ ∈ f → k ∈ succ n := fun k z hkz => by
      obtain ⟨k', z', hk', e⟩ := hfun.2.2 _ hkz
      rw [(_root_.SetTheory.kpair_inj H _ _ _ _ e).1]
      exact hk'
    have hnew : ∀ z, ¬ ⟪succ n, z⟫ₖ ∈ f := fun z h => mem_irrefl H hR _ (hkey _ z h)
    have hmem : ∀ p, p ∈ _root_.SetTheory.vcup H f (_root_.SetTheory.vsingle H ⟪succ n, y⟫ₖ) ↔
        p ∈ f ∨ p = ⟪succ n, y⟫ₖ := fun p =>
      (_root_.SetTheory.vcup_spec H _ _ p).trans (or_congr Iff.rfl (_root_.SetTheory.vsingle_spec H _ _))
    refine ⟨_root_.SetTheory.vcup H f (_root_.SetTheory.vsingle H ⟪succ n, y⟫ₖ),
      ⟨fun k z z' hz hz' => ?_, fun k hk => ?_, fun p hp => ?_⟩,
      (hmem _).2 (Or.inl hzero), fun k z hkz => ?_, fun k hk z z' hz hz' => ?_⟩
    · rcases (hmem _).1 hz with hz | hz <;> rcases (hmem _).1 hz' with hz' | hz'
      · exact hfun.1 k z z' hz hz'
      · rw [(_root_.SetTheory.kpair_inj H _ _ _ _ hz').1] at hz; exact absurd hz (hnew z)
      · rw [(_root_.SetTheory.kpair_inj H _ _ _ _ hz).1] at hz'; exact absurd hz' (hnew z')
      · exact ((_root_.SetTheory.kpair_inj H _ _ _ _ hz).2).trans ((_root_.SetTheory.kpair_inj H _ _ _ _ hz').2).symm
    · rcases (_root_.SetTheory.vsucc_spec H _ k).1 hk with hk | rfl
      · obtain ⟨z, hz⟩ := hfun.2.1 k hk
        exact ⟨z, (hmem _).2 (Or.inl hz)⟩
      · exact ⟨y, (hmem _).2 (Or.inr rfl)⟩
    · rcases (hmem p).1 hp with hp | rfl
      · obtain ⟨k, z, hk, rfl⟩ := hfun.2.2 p hp
        exact ⟨k, z, (_root_.SetTheory.vsucc_spec H _ k).2 (Or.inl hk), rfl⟩
      · exact ⟨_, y, _root_.SetTheory.vsucc_self H _, rfl⟩
    · rcases (hmem _).1 hkz with hkz | e
      · exact hord k z hkz
      · rw [(_root_.SetTheory.kpair_inj H _ _ _ _ e).2]; exact hyo
    · rcases (_root_.SetTheory.vsucc_spec H _ k).1 hk with hk | rfl
      · -- an old index: both pairs are old
        have hz₁ : ⟪k, z⟫ₖ ∈ f := by
          rcases (hmem _).1 hz with hz | e
          · exact hz
          · rw [(_root_.SetTheory.kpair_inj H _ _ _ _ e).1] at hk
            exact absurd (hno.1 _ hk n (_root_.SetTheory.vsucc_self H n)) (mem_irrefl H hR n)
        have hz₂ : ⟪succ k, z'⟫ₖ ∈ f := by
          rcases (hmem _).1 hz' with hz' | e
          · exact hz'
          · have e' := (_root_.SetTheory.kpair_inj H _ _ _ _ e).1
            have hnk : n ∈ succ k := e' ▸ _root_.SetTheory.vsucc_self H n
            rcases (_root_.SetTheory.vsucc_spec H _ n).1 hnk with hnk | rfl
            · exact absurd (hno.1 k hk n hnk) (mem_irrefl H hR n)
            · exact absurd hk (mem_irrefl H hR _)
        exact hstep k hk z z' hz₁ hz₂
      · -- the last index
        have hz₁ : ⟪k, z⟫ₖ ∈ f := by
          rcases (hmem _).1 hz with hz | e
          · exact hz
          · have e' := (_root_.SetTheory.kpair_inj H _ _ _ _ e).1
            have h1 : k ∈ succ k := _root_.SetTheory.vsucc_self H k
            rw [← e'] at h1
            exact absurd h1 (mem_irrefl H hR k)
        rw [hfun.1 k z x hz₁ hx]
        rcases (hmem _).1 hz' with hz' | e
        · exact absurd hz' (hnew z')
        · rw [(_root_.SetTheory.kpair_inj H _ _ _ _ e).2]; exact hy

include H in
/-- **Chains agree** wherever both are defined. -/
theorem chain_agree {n n' f f' : V} (hf : Chain H F α n f) (hf' : Chain H F α n' f')
    (hn : n ∈ ω) (hn' : n' ∈ ω)
    (hsepA : ∃ S : V, ∀ k, k ∈ S ↔ k ∈ ω ∧ ∀ x x', ⟪k, x⟫ₖ ∈ f → ⟪k, x'⟫ₖ ∈ f' → x = x') :
    ∀ k, k ∈ ω → ∀ x x', ⟪k, x⟫ₖ ∈ f → ⟪k, x'⟫ₖ ∈ f' → x = x' := by
  obtain ⟨hfun, hzero, -, hstep⟩ := hf
  obtain ⟨hfun', hzero', -, hstep'⟩ := hf'
  have hno := nat_ord H hn
  have hno' := nat_ord H hn'
  refine omega_ind_res H hsepA ?_ ?_
  · intro x x' hx hx'
    exact (hfun.1 _ x α hx hzero).trans (hfun'.1 _ x' α hx' hzero').symm
  · intro k _ ih x x' hx hx'
    -- the predecessor `k` is in both domains
    have hk : ∀ {m g}, IsFunctionOn H g (succ m) → Ord (memRel V) m → ∀ z, ⟪succ k, z⟫ₖ ∈ g → k ∈ m := by
      intro m g hg hmo z hz
      obtain ⟨k', z', hk', e⟩ := hg.2.2 _ hz
      rw [← (_root_.SetTheory.kpair_inj H _ _ _ _ e).1] at hk'
      rcases (_root_.SetTheory.vsucc_spec H _ _).1 hk' with h | h
      · exact hmo.1 _ h k (_root_.SetTheory.vsucc_self H k)
      · rw [← h]; exact _root_.SetTheory.vsucc_self H k
    have hkn := hk hfun hno x hx
    have hkn' := hk hfun' hno' x' hx'
    obtain ⟨z, hz⟩ := hfun.2.1 k ((_root_.SetTheory.vsucc_spec H _ k).2 (Or.inl hkn))
    obtain ⟨z', hz'⟩ := hfun'.2.1 k ((_root_.SetTheory.vsucc_spec H _ k).2 (Or.inl hkn'))
    have e := ih z z' hz hz'
    subst e
    exact hstep_unique H (hstep k hkn z x hz hx) (hstep' k hkn' z x' hz' hx')

include H hR htot himg hα in
/-- **The orbit closes**: the union of all chain values is a nonzero limit
above `α`, closed under `F`. -/
theorem orbit_closure
    (hsepC : ∃ S : V, ∀ n, n ∈ S ↔ n ∈ ω ∧ ∃ f, Chain H F α n f)
    (hsepA : ∀ f f' : V, ∃ S : V, ∀ k, k ∈ S ↔ k ∈ ω ∧ ∀ x x', ⟪k, x⟫ₖ ∈ f → ⟪k, x'⟫ₖ ∈ f' → x = x')
    {O : V} (hO : ∀ γ, γ ∈ O ↔ ∃ n, n ∈ ω ∧ ∃ f, Chain H F α n f ∧ ⟪n, γ⟫ₖ ∈ f) :
    ∃ β, IsLim (memRel V) β ∧ α ∈ β ∧ ∀ a, a ∈ β → ∀ g, F a g → g ∈ β := by
  -- every orbit point is an ordinal
  have hOo : ∀ γ, γ ∈ O → Ord (memRel V) γ := fun γ hγ => by
    obtain ⟨n, -, f, hf, hγ⟩ := (hO γ).1 hγ
    exact hf.2.2.1 n γ hγ
  -- the successor of an orbit point is an orbit point, and contains it and its `F`-values
  have hnext : ∀ γ, γ ∈ O → ∃ γ', γ' ∈ O ∧ γ ∈ γ' ∧ ∀ a, a ∈ γ → ∀ g, F a g → g ∈ γ' := by
    intro γ hγ
    obtain ⟨n, hn, f, hf, hnγ⟩ := (hO γ).1 hγ
    have hsn := _root_.SetTheory.omega_succ H n hn
    obtain ⟨f', hf'⟩ := chain_exists H hR htot himg hα hsepC _ hsn
    obtain ⟨γ', hγ'⟩ := hf'.1.2.1 _ (_root_.SetTheory.vsucc_self H _)
    obtain ⟨x, hx⟩ := hf'.1.2.1 n ((_root_.SetTheory.vsucc_spec H _ n).2
      (Or.inl (_root_.SetTheory.vsucc_self H n)))
    have hxγ : x = γ := chain_agree H hf' hf hsn hn (hsepA f' f) n hn x γ hx hnγ
    subst hxγ
    have hst := hf'.2.2.2 n (_root_.SetTheory.vsucc_self H n) x γ' hx hγ'
    obtain ⟨y, hy, -, hxy, hcl⟩ := hstep_exists H hR htot himg (hOo x hγ)
    have e := hstep_unique H hy hst
    subst e
    exact ⟨y, (hO y).2 ⟨_, hsn, f', hf', hγ'⟩, hxy, hcl⟩
  have hαO : α ∈ O := by
    obtain ⟨f, hf⟩ := chain_exists H hR htot himg hα hsepC _ (_root_.SetTheory.vempty_in_omega H)
    exact (hO α).2 ⟨_, _root_.SetTheory.vempty_in_omega H, f, hf, hf.2.1⟩
  have hβ : ∀ z, z ∈ _root_.SetTheory.vunion H O ↔ ∃ γ, z ∈ γ ∧ γ ∈ O :=
    _root_.SetTheory.vunion_spec H O
  obtain ⟨γ₁, hγ₁, hαγ₁, -⟩ := hnext α hαO
  refine ⟨_root_.SetTheory.vunion H O,
    ⟨LStepExT.ord_vunion H hOo, ⟨α, (hβ α).2 ⟨γ₁, hαγ₁, hγ₁⟩⟩, fun a ha => ?_⟩,
    (hβ α).2 ⟨γ₁, hαγ₁, hγ₁⟩, fun a ha g hFa => ?_⟩
  · obtain ⟨γ, haγ, hγ⟩ := (hβ a).1 ha
    obtain ⟨γ', hγ', hγγ', -⟩ := hnext γ hγ
    exact ⟨γ, (hβ γ).2 ⟨γ', hγγ', hγ'⟩, haγ⟩
  · obtain ⟨γ, haγ, hγ⟩ := (hβ a).1 ha
    obtain ⟨γ', hγ', -, hcl⟩ := hnext γ hγ
    exact (hβ g).2 ⟨γ', hcl a haγ g hFa, hγ'⟩

end Chains

end LeanProofs.ZFCinPA.LIterate
