import GowersSzemeredi.Proofs16SmallIndexPatterns

/-! Fix four small index patterns and the two row offsets by averaging.
The loss depends exponentially on the small rank, not on all m maps. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- One label fiber has at least the average size, in division-free form. -/
theorem exists_large_label_fiber {α β : Type*} [Fintype β] [Nonempty β]
    (T : Finset α) (f : α → β) :
    ∃ b : β, T.card ≤ Fintype.card β * (T.filter fun x => f x = b).card := by
  classical
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun b => (T.filter fun x => f x = b).card) Finset.univ_nonempty
  refine ⟨b, ?_⟩
  have hsum : (∑ c : β, (T.filter fun x => f x = c).card) = T.card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter T Finset.univ f
  rw [← hsum]
  calc (∑ c : β, (T.filter fun x => f x = c).card)
      ≤ ∑ _c : β, (T.filter fun x => f x = b).card :=
        Finset.sum_le_sum fun c hc => hmax c hc
    _ = _ := by simp

/-- Four index patterns of size at most ell and fixed offsets leave a
fiber V with |T| <= (m+1)^(4ell) N^2 |V|. No inactive indices are added. -/
theorem exists_fixed_index_patterns {N m ell : Nat} [NeZero N]
    (T : Finset (ZMod N × ZMod N × ZMod N))
    (I : ZMod N → Finset (Fin m)) (hI : ∀ y, (I y).card ≤ ell) :
    ∃ (J : Fin 4 → Finset (Fin m)) (z w : ZMod N) (V : Finset (ZMod N)),
      (∀ i, (J i).card ≤ ell) ∧
      T.card ≤ (m + 1)^(4 * ell) * N^2 * V.card ∧
      ∀ y ∈ V, (y, z, w) ∈ T ∧ I (y + z) = J 0 ∧ I z = J 1 ∧
        I (y + w) = J 2 ∧ I w = J 3 := by
  let P := smallIndexSets m ell
  letI : Nonempty P := ⟨⟨∅, by simp [P]⟩⟩
  let ip (y : ZMod N) : P := ⟨I y, mem_smallIndexSets.mpr (hI y)⟩
  let f (t : ZMod N × ZMod N × ZMod N) : (Fin 4 → P) × (ZMod N × ZMod N) :=
    (![ip (t.1 + t.2.1), ip t.2.1, ip (t.1 + t.2.2), ip t.2.2], t.2)
  obtain ⟨c, hc⟩ := exists_large_label_fiber T f
  let F := T.filter fun t => f t = c
  let V := F.image Prod.fst
  have hlabel (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ F) : f t = c :=
    (Finset.mem_filter.mp ht).2
  have hinj : Set.InjOn Prod.fst (F : Set (ZMod N × ZMod N × ZMod N)) := by
    intro t ht u hu htu
    apply Prod.ext htu
    exact (congrArg Prod.snd (hlabel t ht)).trans (congrArg Prod.snd (hlabel u hu)).symm
  have hV : V.card = F.card := Finset.card_image_of_injOn hinj
  have hcount : Fintype.card ((Fin 4 → P) × (ZMod N × ZMod N)) ≤ (m + 1)^(4 * ell) * N^2 := by
    calc Fintype.card ((Fin 4 → P) × (ZMod N × ZMod N)) = P.card^4 * N^2 := by
          simp [Fintype.card_prod, ZMod.card, pow_two]
      _ ≤ ((m + 1)^ell)^4 * N^2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (smallIndexSets_card_le m ell) 4)
      _ = (m + 1)^(4 * ell) * N^2 := by rw [← pow_mul, Nat.mul_comm ell 4]
  refine ⟨fun i => (c.1 i).val, c.2.1, c.2.2, V, fun i => mem_smallIndexSets.mp (c.1 i).property, ?_, ?_⟩
  · rw [hV]
    have hcF : T.card ≤ Fintype.card ((Fin 4 → P) × (ZMod N × ZMod N)) * F.card := by
      convert hc using 1
      congr 2
      ext t
      simp [F]
    exact hcF.trans (Nat.mul_le_mul_right F.card hcount)
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    have hfc := hlabel t ht
    have hzw : t.2 = c.2 := congrArg Prod.snd hfc
    have hpat := congrArg Prod.fst hfc
    have heq : (t.1, c.2.1, c.2.2) = t := by rw [← hzw]
    refine ⟨by simpa only [heq] using (Finset.mem_filter.mp ht).1, ?_, ?_, ?_, ?_⟩
    · have h := congrArg (fun q : Fin 4 → P => (q 0).val) hpat
      simpa [f, ip, hzw] using h
    · have h := congrArg (fun q : Fin 4 → P => (q 1).val) hpat
      simpa [f, ip, hzw] using h
    · have h := congrArg (fun q : Fin 4 → P => (q 2).val) hpat
      simpa [f, ip, hzw] using h
    · have h := congrArg (fun q : Fin 4 → P => (q 3).val) hpat
      simpa [f, ip, hzw] using h

end LeanProofs.GowersSzemeredi
