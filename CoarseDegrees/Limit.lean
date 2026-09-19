import CoarseDegrees.Columns
import CoarseDegrees.Hyper

/-!
# Limit computability

`LimitComputableIn B A` says that `A` is the pointwise limit of a `B`-computable approximation.
By Shoenfield's limit lemma this is `A ≤ᵀ B'`, but the jump is not available in Mathlib or in
`C:\ProveIt`, so the dyadic-code criterion of report 10 is stated in limit form instead; no
jump operator is then needed anywhere.

The fact needed downstream is `LimitComputableIn.hypIn`: a limit of a `B`-computable
approximation is hyperarithmetic in `B`.  A `Σ¹₁` form of `A` and one of its complement are
produced by hand, the first from the constant witness `s` and the second from a Skolem
function.  In each case the matrix of the Kleene normal form is arranged to make just *one*
oracle query, which is what `setTuringReducible_of_one_query` needs.

Everything in this file is proved.
-/

noncomputable section

open scoped Computability
open TuringDegrees
open scoped SetTuring

namespace CoarseDegrees

/-! ## A reduction with a single oracle query -/

/-- If membership in `S` is a computable function of the input together with the answer to one
computably located query to `L`, then `S ≤ᵀₛ L`. -/
theorem setTuringReducible_of_one_query {S L : Set ℕ} (q : ℕ → ℕ) (hq : Computable q)
    (g : ℕ → ℕ → ℕ) (hg : Computable₂ g)
    (h : ∀ m, characteristicValue S m = g m (characteristicValue L (q m))) : S ≤ᵀₛ L := by
  have h1 : RecursiveIn {characteristic L} (fun m : ℕ => characteristic L (q m)) :=
    recursiveIn_precomp (RecursiveIn.oracle _ (Set.mem_singleton _)) hq
  have h0 : RecursiveIn {characteristic L} (fun m : ℕ => (Part.some m : Part ℕ)) :=
    Partrec.recursiveIn (f := fun m : ℕ => (Part.some m : Part ℕ)) Computable.id
  have hc : Computable (fun p : ℕ => g p.unpair.1 p.unpair.2) :=
    hg.comp (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair)
  have h4 := recursiveIn_map (recursiveIn_pair h0 h1) hc
  refine h4.of_eq fun m => ?_
  have hpair : (Nat.pair <$> (Part.some m : Part ℕ) <*> characteristic L (q m))
      = Part.some (Nat.pair m (characteristicValue L (q m))) := by
    simp [characteristic, Seq.seq, characteristicValue]
  rw [hpair]
  simp only [Part.map_some, Nat.unpair_pair]
  exact congrArg Part.some (h m).symm

/-! ## Limit computability -/

/-- `A` is the limit of a `B`-computable approximation: the set `L` of pairs `⟨k,t⟩` codes the
approximation, and for each `k` it is eventually correct about `k ∈ A`. -/
def LimitComputableIn (B A : Set ℕ) : Prop :=
  ∃ L : Set ℕ, L ≤ᵀₛ B ∧ ∀ k, ∃ s, ∀ t, s ≤ t → (Nat.pair k t ∈ L ↔ k ∈ A)

/-! ## Reading entries of a coded finite sequence -/

/-- The `i`-th entry of `σ`, or `0`. -/
def nth (σ : List ℕ) (i : ℕ) : ℕ := (σ[i]?).getD 0

theorem primrec_nth : Primrec₂ nth :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd) (Primrec.const 0)

/-- The finite sequence coded by the second component of `m`. -/
def seqOf (m : ℕ) : List ℕ := Denumerable.ofNat (List ℕ) m.unpair.2

theorem primrec_seqOf : Primrec seqOf :=
  (Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp Primrec.unpair)

theorem seqOf_pair (n : ℕ) (σ : List ℕ) : seqOf (Nat.pair n (Encodable.encode σ)) = σ := by
  simp [seqOf, Denumerable.ofNat_encode]

theorem nth_ofFn {f : ℕ → ℕ} {m i : ℕ} (hi : i < m) :
    nth (List.ofFn fun i : Fin m => f i) i = f i := by
  unfold nth
  rw [List.getElem?_eq_getElem (by simpa using hi)]
  simp

theorem length_ofFn {f : ℕ → ℕ} (m : ℕ) :
    (List.ofFn fun i : Fin m => f i).length = m := by simp

/-! ## `A` is `Σ¹₁` in the approximation -/

/-- The matrix for `A`: the bound `s` is read off as `f 0`. -/
def limT (L : Set ℕ) (k : ℕ) (σ : List ℕ) : Prop :=
  σ.length = 0 ∨ (Nat.pair k (σ.length - 1) ∈ L ∨ σ.length - 1 < nth σ 0)

theorem codeSet_limT_red {L : Set ℕ} : codeSet (limT L) ≤ᵀₛ L := by
  classical
  refine setTuringReducible_of_one_query
    (fun m => Nat.pair m.unpair.1 ((seqOf m).length - 1))
    ((Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.nat_sub.comp (Primrec.list_length.comp primrec_seqOf)
        (Primrec.const 1))).to_comp)
    (fun m v => if (seqOf m).length = 0 then 1
      else if v = 1 then 1
      else if (seqOf m).length - 1 < nth (seqOf m) 0 then 1 else 0)
    (by
      have hlen : Primrec (fun p : ℕ × ℕ => (seqOf p.1).length) :=
        Primrec.list_length.comp (primrec_seqOf.comp Primrec.fst)
      have hsub : Primrec (fun p : ℕ × ℕ => (seqOf p.1).length - 1) :=
        Primrec.nat_sub.comp hlen (Primrec.const 1)
      have hnth : Primrec (fun p : ℕ × ℕ => nth (seqOf p.1) 0) :=
        primrec_nth.comp (primrec_seqOf.comp Primrec.fst) (Primrec.const 0)
      exact (Primrec.ite (Primrec.eq.comp hlen (Primrec.const 0)) (Primrec.const 1)
        (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1)) (Primrec.const 1)
          (Primrec.ite (Primrec.nat_lt.comp hsub hnth) (Primrec.const 1)
            (Primrec.const 0)))).to_comp)
    ?_
  intro m
  have hq : characteristicValue L (Nat.pair m.unpair.1 ((seqOf m).length - 1)) = 1 ↔
      Nat.pair m.unpair.1 ((seqOf m).length - 1) ∈ L := by
    by_cases hL : Nat.pair m.unpair.1 ((seqOf m).length - 1) ∈ L <;>
      simp [characteristicValue, hL]
  have hmem : m ∈ codeSet (limT L) ↔ limT L m.unpair.1 (seqOf m) := by
    constructor
    · rintro ⟨n, σ, rfl, hT⟩
      rwa [seqOf_pair, Nat.unpair_pair]
    · intro hT
      exact ⟨m.unpair.1, seqOf m, by simp [seqOf, Denumerable.encode_ofNat, Nat.pair_unpair], hT⟩
  by_cases h0 : (seqOf m).length = 0
  · have hin : m ∈ codeSet (limT L) := hmem.mpr (Or.inl h0)
    simp [characteristicValue, hin, h0]
  · by_cases hL : Nat.pair m.unpair.1 ((seqOf m).length - 1) ∈ L
    · have hin : m ∈ codeSet (limT L) := hmem.mpr (Or.inr (Or.inl hL))
      simp [characteristicValue, hin, h0, hL]
    · by_cases hlt : (seqOf m).length - 1 < nth (seqOf m) 0
      · have hin : m ∈ codeSet (limT L) := hmem.mpr (Or.inr (Or.inr hlt))
        simp [characteristicValue, hin, h0, hL, hlt]
      · have hout : m ∉ codeSet (limT L) := by
          rw [hmem]
          unfold limT
          tauto
        simp [characteristicValue, hout, h0, hL, hlt]

theorem sigma11_of_limit {B A L : Set ℕ} (hL : L ≤ᵀₛ B)
    (hlim : ∀ k, ∃ s, ∀ t, s ≤ t → (Nat.pair k t ∈ L ↔ k ∈ A)) : Sigma11In B A := by
  refine ⟨limT L, codeSet_limT_red.trans hL, fun k => ?_⟩
  constructor
  · intro hk
    obtain ⟨s, hs⟩ := hlim k
    refine ⟨fun _ => s, fun m => ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl (by simp)
    · refine Or.inr ?_
      simp only [List.length_ofFn]
      by_cases hlt : m - 1 < s
      · refine Or.inr ?_
        have hnth : nth (List.ofFn fun _ : Fin m => s) 0 = s := by
          unfold nth
          rw [List.getElem?_eq_getElem (by simpa using hm)]
          simp
        rw [hnth]
        exact hlt
      · exact Or.inl ((hs (m - 1) (by omega)).mpr hk)
  · rintro ⟨f, hf⟩
    obtain ⟨s, hs⟩ := hlim k
    by_contra hk
    set t := max s (f 0) with ht
    have h1 := hf (t + 1)
    unfold limT at h1
    simp only [List.length_ofFn] at h1
    simp only [Nat.add_sub_cancel] at h1
    rcases h1 with h | h | h
    · omega
    · exact hk ((hs t (by omega)).mp h)
    · rw [nth_ofFn (by omega : (0:ℕ) < t + 1)] at h
      omega

end CoarseDegrees
