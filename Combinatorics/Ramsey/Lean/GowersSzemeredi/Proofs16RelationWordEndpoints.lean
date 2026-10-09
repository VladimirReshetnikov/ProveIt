import GowersSzemeredi.Proofs16RelationWordImages
import GowersSzemeredi.Proofs16CoherentRelationWordDomain

/-! The word image estimate uses only anchor and output frequencies.
Freiman-linear varying frequencies recover all intermediate domains with
the fixed radius cost `9^length`; no auxiliary frequencies are retained. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The union of the spectra of the anchors and output entries. -/
abbrev relationWordEndpointSpectrum {N : Nat}
    (T : ZMod N → Finset (ZMod N)) (as : List (ZMod N)) (w : ColumnWord N as.length) :
    Finset (ZMod N) := columnListSpectrum T (as ++ columnWordEntries w)

theorem mem_bohr_relation_word_endpoints {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (as : List (ZMod N)) (w : ColumnWord N as.length)
    (r : Real) (y : ZMod N) :
    y ∈ bohr (relationWordEndpointSpectrum T as w) r ↔
      ∀ x ∈ as ++ columnWordEntries w, y ∈ bohr (T x) r :=
  mem_columnListSpectrum_bohr T (as ++ columnWordEntries w) r y

/-- A word of `ell` triples needs at most `4*ell*d` endpoint frequencies. -/
theorem relationWordEndpointSpectrum_card_le {N d : Nat} [NeZero N]
    (A : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (as : List (ZMod N)) (w : ColumnWord N as.length)
    (ha : ∀ x ∈ as, x ∈ A) (hw : columnWordIn A w)
    (hT : ∀ x ∈ A, (T x).card ≤ d) :
    (relationWordEndpointSpectrum T as w).card ≤ 4*as.length*d := by
  let S := (as ++ columnWordEntries w).toFinset
  have hSA : ∀ x ∈ S, x ∈ A := by
    intro x hx
    have hx' : x ∈ as ++ columnWordEntries w := by simpa [S] using hx
    rcases List.mem_append.mp hx' with hx | hx
    · exact ha x hx
    · exact columnWordEntries_mem A w hw x hx
  have hcard := columnListSpectrum_card_le T (as ++ columnWordEntries w)
    (fun x hx => hT x (hSA x (by simpa [S] using hx)))
  simpa only [List.length_append, columnWordEntries_length, show as.length+3*as.length = 4*as.length by omega] using hcard

/-- Bounded-image word defects on the anchor-and-output Bohr domain. -/
theorem coherent_relation_word_image_card_le {N ell : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (F : ZMod N → ZMod N → ZMod N) (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    {r : Real} (hr : 0 ≤ r) (M : Nat)
    (htheta : ∀ i, IsFreimanLinearOn A (theta i))
    (hR : ∀ a b c d, R a b c d → ColumnQuadImageRelation
      (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F r M a b c d)
    (a : ZMod N) (as : List (ZMod N)) (w : ColumnWord N (a::as).length)
    (ha : ∀ x ∈ a::as, x ∈ A) (hw : w ∈ relationWordRepresentations A R (a::as)) :
    ((bohr (relationWordEndpointSpectrum
      (fun u => B ∪ Finset.univ.image (fun j => theta j u)) (a::as) w)
      (r/(9 : Real)^(a::as).length)).image (relationWordDefect F (a::as) w)).card ≤
        M^(2*as.length+1) := by
  let T := fun u => B ∪ Finset.univ.image (fun j => theta j u)
  have hbound := relation_word_defect_image_card_le_of_relation A T F r M R hR a as w hw
  apply (image_card_le_of_eq_on_subset _ (relationWordCommonDomain T r (a::as) w)
    (relationWordDefect F (a::as) w) (relationWordDefect F (a::as) w) ?_
    (fun _ _ => rfl)).trans hbound
  intro y hy
  have he := (mem_bohr_relation_word_endpoints T (a::as) w _ y).mp hy
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  apply coherent_relation_word_domain A B theta R hr htheta (a::as) w hw ha y
  · intro x hx
    simpa only [T, freimanFrequencyBohr] using he x (List.mem_append_left _ hx)
  · intro x hx
    simpa only [T, freimanFrequencyBohr] using he x (List.mem_append_right _ hx)

end LeanProofs.GowersSzemeredi
