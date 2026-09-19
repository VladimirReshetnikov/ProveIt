/-
  KUNEN-FREE FACTS ABOUT A WITNESS (research note "Exacting embeddings of countable
  structures", §3).

  The theorems of this file -- and `jOrd_nat`, `omega_le_crit`, `jv_subset_fixed`,
  `no_surj_pow_crit`, `slSem_critSeq` of `WitnessFacts.lean` -- use only the elementarity
  of the two maps of a witness.  They never use `Published.critSeq_cofinal`, and they
  never use that the embedding is a member of the universe.  Their proofs therefore
  apply verbatim to *virtual* witnesses (embeddings that exist in a forcing extension)
  and to witnesses between countable structures, for which the Kunen inconsistency
  fails.  `Audit.lean` confirms that none of them depends on `sorryAx`.

  * `crit_regular`: no function in `V_α` maps an ordinal `μ < κ` onto a cofinal subset of
    the critical point `κ`.  With `no_surj_pow_crit` this makes `κ` inaccessible;
  * `interleave`: for a strictly increasing `e`, the orbits of two roots `r ≤ r' < e r`
    interleave: `e^n r ≤ e^n r' < e^(n+1) r`.  (All orbit classes of Lemma 12.1 are
    "parallel" fundamental sequences of `λ`.)

  Nothing is admitted in this file.
-/
import Cardinals.WitnessFacts

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal
open SetTheory (Form Sat scons)
open SetTheory.Form

/-- `∀ a ∈ v_k ∃ s ∈ v_S (a ∈ s ∨ a = s)`: `v_S` is cofinal in the ordinal `v_k`. -/
def cofF (S k : ℕ) : Form :=
  fAll (fImp (fMem 0 (k + 1)) (fEx (fAnd (fMem 0 (S + 2)) (fOr (fMem 1 0) (fEq 1 0)))))

/-- The meaning of `cofF`. -/
def CofSem (S k : ZFSet.{u}) : Prop := ∀ a ∈ k, ∃ s ∈ S, a ∈ s ∨ a = s

theorem cofF_spec {A : ZFSet.{u}} (hA : IsTransitive A) (e : ℕ → Carrier A) (S k : ℕ) :
    Sat (memOn A) e (cofF S k) ↔ CofSem (e S).1 (e k).1 := by
  unfold cofF CofSem
  simp only [Sat]
  constructor
  · intro h a ha
    obtain ⟨s, hs, hor⟩ := h ⟨a, hA.subset_of_mem (e k).2 ha⟩ ha
    exact ⟨s.1, hs, hor.imp id (fun h1 => congrArg Subtype.val h1)⟩
  · intro h d hd
    obtain ⟨s, hs, hor⟩ := h d.1 hd
    exact ⟨⟨s, hA.subset_of_mem (e S).2 hs⟩, hs, hor.imp id (fun h1 => Subtype.ext h1)⟩

namespace RelWitness

variable {α : Ordinal.{u}} {Y : ZFSet.{u}} {c : Cardinal.{u}} (w : RelWitness c.ord α Y)

theorem cof_iff (S k : Str w.X Y) : CofSem S.1 k.1 ↔ CofSem (w.jv S) (w.jv k) := by
  have hA := isTransitive_vonNeumann α
  have h := w.elem (cofF 0 1) (scons S (fun _ => k))
  rw [cofF_spec hA, cofF_spec hA] at h
  exact h

/-- **The critical point is regular**: no function in `V_α` maps some `μ < κ` onto a
cofinal subset of `κ`.  (Kunen-free.) -/
theorem crit_regular (hα : ∀ a < α, a + 1 < α) {μ : Ordinal.{u}} (hμ : μ < w.crit)
    (S : ZFSet.{u}) (hS : S ⊆ ordZ w.crit) (hcof : CofSem S (ordZ w.crit)) :
    ¬ ∃ f ∈ V_ α, SurjSem (V_ α) f (ordZ μ) S := by
  intro hex
  have hlamα := w.lam_lt_height
  have hμlam : μ < c.ord := hμ.trans w.crit_lt
  have hSV : S ∈ V_ c.ord :=
    mem_V_of_subset (β := w.crit) (fun t ht => ordZ_subset_V _ (hS ht)) w.crit_lt
  let sX : Str w.X Y := ⟨S, w.base hSV⟩
  let kX : Str w.X Y := w.ordX w.crit w.crit_lt
  obtain ⟨fX, hsX⟩ := w.surj_in_X hα (w.ordX μ hμlam) sX hex
  have hsJ := (w.surj_iff hα fX (w.ordX μ hμlam) sX).mp hsX
  rw [jv_ordX, w.jOrd_of_lt_crit hμ] at hsJ
  have hsX' : SurjSem (V_ α) fX.1 (ordZ μ) S := hsX
  -- `j(S) ⊆ S`
  have hjS : w.jv sX ⊆ S := by
    intro v hv
    obtain ⟨u, hu, hp⟩ := hsJ.2.2 v hv
    obtain ⟨ζ, hζ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hu
    obtain ⟨v', hv', hp'⟩ := hsX'.1 _ hu
    obtain ⟨η, hη, rfl⟩ := Ordinal.mem_toZFSet_iff.mp (hS hv')
    have hζlam : ζ < c.ord := hζ.trans hμlam
    have hηlam : η < c.ord := hη.trans w.crit_lt
    have hp'' := (w.pair_mem_iff hα (w.ordX ζ hζlam) (w.ordX η hηlam) fX).mp hp'
    rw [jv_ordX, jv_ordX, w.jOrd_of_lt_crit (hζ.trans hμ), w.jOrd_of_lt_crit hη] at hp''
    have hvA : v ∈ V_ α := (isTransitive_vonNeumann α).subset_of_mem (w.j sX).2 hv
    have : v = ordZ η :=
      hsJ.2.1 (ordZ ζ) (ordZ_mem_V (hζlam.trans hlamα)) v hvA
        (ordZ η) (ordZ_mem_V (hηlam.trans hlamα)) hp hp''
    rw [this]
    exact hv'
  -- but `j(S)` is cofinal in `j(κ) > κ`
  have hcofJ := (w.cof_iff sX kX).mp hcof
  have hkJ : w.jv kX = ordZ (w.jOrd w.crit) := w.jv_ordX w.crit_lt
  rw [hkJ] at hcofJ
  obtain ⟨s, hs, hor⟩ := hcofJ (ordZ w.crit) (Ordinal.toZFSet_mem_toZFSet_iff.mpr w.crit_lt_jOrd)
  obtain ⟨η, hη, rfl⟩ := Ordinal.mem_toZFSet_iff.mp (hS (hjS hs))
  rcases hor with h1 | h1
  · exact lt_asymm hη (Ordinal.toZFSet_mem_toZFSet_iff.mp h1)
  · exact absurd (ordZ_inj h1) (ne_of_gt hη)

end RelWitness

/-! ### Orbits of a strictly increasing map interleave -/

/-- If `e` is strictly increasing below `lam` and maps `lam` into itself, the orbits of
two points `r ≤ r' < e r` interleave. -/
theorem interleave (e : Ordinal.{u} → Ordinal.{u}) (lam : Ordinal.{u})
    (hlt : ∀ ξ < lam, e ξ < lam) (hmono : ∀ a b, a < b → b < lam → e a < e b)
    {r r' : Ordinal.{u}} (hr' : r' < lam) (h1 : r ≤ r') (h2 : r' < e r) (n : ℕ) :
    e^[n] r ≤ e^[n] r' ∧ e^[n] r' < e^[n + 1] r ∧ e^[n] r' < lam := by
  induction n with
  | zero => exact ⟨h1, h2, hr'⟩
  | succ n ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hlam1 : e^[n + 1] r < lam := by
      rw [Function.iterate_succ_apply']
      exact hlt _ (lt_of_le_of_lt ih1 ih3)
    refine ⟨?_, ?_, ?_⟩
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rcases ih1.lt_or_eq with h | h
      · exact (hmono _ _ h ih3).le
      · rw [h]
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply' (n := n + 1)]
      exact hmono _ _ ih2 hlam1
    · rw [Function.iterate_succ_apply']
      exact hlt _ ih3

end Cardinals
