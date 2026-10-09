import GowersSzemeredi.Proofs16ColumnWordDomains
import GowersSzemeredi.Proofs16AbstractBSGWords
import GowersSzemeredi.Proofs16FrequencyBohrCompletion

/-! Freiman-linear varying frequencies recover the auxiliary domains of
arbitrary-relation words. Exact relations between local map values are not
needed for domain recovery. The radius cost is `9^length`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem coherent_relation_word_domain {N ell : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop) {r : Real} (hr : 0 ≤ r)
    (htheta : ∀ i, IsFreimanLinearOn A (theta i)) :
    ∀ (as : List (ZMod N)) (w : ColumnWord N as.length),
      w ∈ relationWordRepresentations A R as →
      (∀ x ∈ as, x ∈ A) → ∀ y : ZMod N,
        (∀ x ∈ as, y ∈ freimanFrequencyBohr B theta (r/(9 : Real)^as.length) x) →
        (∀ x ∈ columnWordEntries w, y ∈ freimanFrequencyBohr B theta (r/(9 : Real)^as.length) x) →
        columnWordDomain (fun u => B ∪ Finset.univ.image (fun j => theta j u)) r as w y := by
  intro as
  induction as with
  | nil => intro w hw hanchors y ha he; trivial
  | cons a as ih =>
    cases as with
    | nil =>
      intro w hw hanchors y ha he
      have hle : r/(9 : Real)^([a].length) ≤ r := by simp only [List.length_singleton,pow_one]; linarith
      exact ⟨bohr_mono_radius _ hle (ha a (by simp)),
        bohr_mono_radius _ hle (he _ (by simp [columnWordEntries])),
        bohr_mono_radius _ hle (he _ (by simp [columnWordEntries])),
        bohr_mono_radius _ hle (he _ (by simp [columnWordEntries]))⟩
    | cons b as =>
      intro w hw hanchors y ha he
      let p := columnWordUnsplice a (columnAnchorEval id (b::as)) w
      have hparts : p.2.1 ∈ relationTripleRepresentations A R a ∧
          p.2.2 ∈ relationWordRepresentations A R (b::as) ∧
          p.1 ∈ mixedRelationQuadruples A A R := (Finset.mem_filter.mp hw).2
      let s := r/(9 : Real)^(a::b::as).length
      let t := r/(9 : Real)^(b::as).length
      have hs : 0 ≤ s := by dsimp [s]; positivity
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have hst : t = 9*s := by
        dsimp only [s,t]
        simp only [List.length_cons,pow_succ]
        field_simp
      have htr : t ≤ r := div_le_self hr (one_le_pow₀ (by norm_num))
      have hsr : s ≤ r := by linarith
      have h3r : 3*s ≤ r := by linarith
      have hstle : s ≤ t := by linarith
      have hsa : y ∈ freimanFrequencyBohr B theta s a := ha a (by simp)
      have hs1 : y ∈ freimanFrequencyBohr B theta s w.1.1 := he _ (by simp [columnWordEntries])
      have hs2 : y ∈ freimanFrequencyBohr B theta s w.1.2.1 := he _ (by simp [columnWordEntries])
      have hs3 : y ∈ freimanFrequencyBohr B theta s w.1.2.2 := he _ (by simp [columnWordEntries])
      have hs4 : y ∈ freimanFrequencyBohr B theta s w.2.1.1 := he _ (by simp [columnWordEntries])
      obtain ⟨hymem, hyvalue, _⟩ := Finset.mem_filter.mp hparts.1
      simp only [Finset.mem_product] at hymem
      obtain ⟨hy1, hy2, hy3⟩ := hymem
      have hyadd : a + w.1.2.1 = w.1.1 + p.2.1.2.2 := by
        change a = w.1.1-w.1.2.1+p.2.1.2.2 at hyvalue
        linear_combination hyvalue
      have hyfreq : ∀ i, theta i a+theta i w.1.2.1 = theta i w.1.1+theta i p.2.1.2.2 := by
        intro i
        exact htheta i _ _ _ _ (hanchors a (by simp)) hy2 hy1 hy3 hyadd
      have hybohr : y ∈ freimanFrequencyBohr B theta (3*s) p.2.1.2.2 :=
        freiman_frequency_bohr_complete B theta hyfreq
          (by simpa only [show 3*s/3=s by ring] using hsa)
          (by simpa only [show 3*s/3=s by ring] using hs2)
          (by simpa only [show 3*s/3=s by ring] using hs1)
      obtain ⟨_, hq0, hq2, hq1, hq3, hqadd, _⟩ := Finset.mem_filter.mp hparts.2.2
      have hzfreq : ∀ i, theta i p.2.1.2.2+theta i w.2.1.1 = theta i w.1.2.2+theta i p.2.2.1.1 := by
        intro i
        exact (htheta i _ _ _ _ hq0 hq1 hq2 hq3 hqadd).symm
      have hzbohr : y ∈ freimanFrequencyBohr B theta t p.2.2.1.1 := by
        rw [hst]
        apply freiman_frequency_bohr_complete B theta hzfreq
        · simpa only [show 9*s/3=3*s by ring] using hybohr
        · exact bohr_mono_radius _ (by linarith : s ≤ 9*s/3) hs4
        · exact bohr_mono_radius _ (by linarith : s ≤ 9*s/3) hs3
      have hzentries : ∀ x ∈ columnWordEntries p.2.2, y ∈ freimanFrequencyBohr B theta t x := by
        intro x hx
        change x ∈ p.2.2.1.1 :: w.2.1.2.1 :: w.2.1.2.2 :: columnWordEntries w.2.2 at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hzbohr
        · exact bohr_mono_radius _ hstle (he x (by simp only [columnWordEntries,List.mem_cons] at hx ⊢; tauto))
      have htail := ih p.2.2 hparts.2.1
        (fun x hx => hanchors x (List.mem_cons_of_mem a hx)) y
        (fun x hx => bohr_mono_radius _ hstle (ha x (List.mem_cons_of_mem a hx))) hzentries
      refine ⟨⟨bohr_mono_radius _ hsr hsa,bohr_mono_radius _ hsr hs1,
        bohr_mono_radius _ hsr hs2,bohr_mono_radius _ h3r hybohr⟩,htail,?_⟩
      intro i; fin_cases i
      · exact bohr_mono_radius _ hsr hs3
      · exact bohr_mono_radius _ htr hzbohr
      · exact bohr_mono_radius _ h3r hybohr
      · exact bohr_mono_radius _ hsr hs4

end LeanProofs.GowersSzemeredi
