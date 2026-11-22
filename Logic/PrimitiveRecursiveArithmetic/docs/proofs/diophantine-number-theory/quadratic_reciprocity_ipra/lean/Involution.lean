import QRPermutation

namespace QR

/-- Product of a duplicate-free list partitioned into disjoint two-cycles,
each with the same product modulo `p`. The modulus may be arbitrary. -/
theorem pair_product {p a : Nat} {T : Nat → Nat} (xs : List Nat)
    (nd : xs.Nodup) (closed : ∀ x, x ∈ xs → T x ∈ xs)
    (inv : ∀ x, x ∈ xs → T (T x) = x) (free : ∀ x, x ∈ xs → T x ≠ x)
    (pair : ∀ x, x ∈ xs → (x * T x) % p = a % p) :
    natProd xs % p = a ^ (xs.length / 2) % p := by
  suffices aux : ∀ (n : Nat) (ys : List Nat), ys.length ≤ n →
      ys.Nodup → (∀ x, x ∈ ys → T x ∈ ys) → (∀ x, x ∈ ys → T (T x) = x) →
      (∀ x, x ∈ ys → T x ≠ x) → (∀ x, x ∈ ys → (x * T x) % p = a % p) →
      natProd ys % p = a ^ (ys.length / 2) % p by
    exact aux xs.length xs (Nat.le_refl _) nd closed inv free pair
  intro n
  induction n with
  | zero =>
    intro ys hlen _ _ _ _ _
    have he : ys = [] := List.length_eq_zero_iff.mp (by omega)
    rw [he]
    simp [natProd]
  | succ n ih =>
    intro ys hlen hnd hc hi hf ha
    cases ys with
    | nil => simp [natProd]
    | cons x rest =>
      obtain ⟨hxout, rnd⟩ := List.nodup_cons.mp hnd
      have hx : x ∈ x :: rest := List.mem_cons_self
      have htx : T x ∈ rest := (List.mem_cons.mp (hc x hx)).resolve_left (hf x hx)
      let zs := rest.erase (T x)
      have zmem (z : Nat) : z ∈ zs ↔ z ≠ T x ∧ z ∈ rest := (QR.nodup_mem_erase_iff rnd)
      have sub (z : Nat) (hz : z ∈ zs) : z ∈ x :: rest :=
        List.mem_cons_of_mem x ((zmem z).mp hz).2
      have stable (z : Nat) (hz : z ∈ zs) : T z ∈ zs := by
        have hfull := sub z hz
        obtain ⟨hne, hr⟩ := (zmem z).mp hz
        have hzx : z ≠ x := by rintro rfl; exact hxout hr
        have ht₁ : T z ≠ T x := by
          intro he
          have h := congrArg T he
          rw [hi z hfull, hi x hx] at h
          exact hzx h
        have ht₂ : T z ≠ x := by
          intro he
          have h := congrArg T he
          rw [hi z hfull] at h
          exact hne h
        exact (zmem (T z)).mpr ⟨ht₁, (List.mem_cons.mp (hc z hfull)).resolve_left ht₂⟩
      have hperm := QR.perm_cons_erase htx
      have hlength : rest.length = zs.length + 1 := hperm.length_eq
      have small : zs.length ≤ n := by simp only [List.length_cons] at hlen; omega
      have hpz := ih zs small (rnd.erase _) stable (fun z hz => hi z (sub z hz))
        (fun z hz => hf z (sub z hz)) (fun z hz => ha z (sub z hz))
      have hexp : (x :: rest).length / 2 = zs.length / 2 + 1 := by
        simp only [List.length_cons]; omega
      calc
        _ = ((x * T x) * natProd zs) % p := by
          simp only [natProd, perm_prod hperm]; rw [Nat.mul_assoc]
        _ = (a * a ^ (zs.length / 2)) % p := by
          rw [Nat.mul_mod, ha x hx, hpz, ← Nat.mul_mod]
        _ = _ := by rw [hexp, Nat.pow_succ, Nat.mul_comm]

/-- If exactly two elements are fixed, remove them and apply the two-cycle formula. -/
theorem two_fixed_product {p a r s : Nat} {T : Nat → Nat} (xs : List Nat)
    (nd : xs.Nodup) (closed : ∀ x, x ∈ xs → T x ∈ xs)
    (inv : ∀ x, x ∈ xs → T (T x) = x)
    (fixed : ∀ x, x ∈ xs → (T x = x ↔ x = r ∨ x = s))
    (hr : r ∈ xs) (hs : s ∈ xs) (hrs : r ≠ s)
    (pair : ∀ x, x ∈ xs → (x * T x) % p = a % p) :
    natProd xs % p = (r*s*a^((xs.length-2)/2)) % p := by
  let ys := xs.erase r
  let zs := ys.erase s
  have ynd : ys.Nodup := nd.erase r
  have hsy : s ∈ ys := (QR.nodup_mem_erase_iff nd).mpr ⟨hrs.symm, hs⟩
  have mem_zs (x : Nat) : x ∈ zs ↔ x ≠ s ∧ x ≠ r ∧ x ∈ xs := by
    rw [show x ∈ zs ↔ x ≠ s ∧ x ∈ ys from (QR.nodup_mem_erase_iff ynd),
        show x ∈ ys ↔ x ≠ r ∧ x ∈ xs from (QR.nodup_mem_erase_iff nd)]
  have sub (x : Nat) (hx : x ∈ zs) : x ∈ xs := ((mem_zs x).mp hx).2.2
  have reflect (x c : Nat) (hx : x ∈ xs) (hc : T c = c) (he : T x = c) : x = c := by
    have h := congrArg T he
    rwa [inv x hx, hc] at h
  have stable (x : Nat) (hx : x ∈ zs) : T x ∈ zs := by
    obtain ⟨hxs, hxr, hxx⟩ := (mem_zs x).mp hx
    exact (mem_zs (T x)).mpr
      ⟨fun he => hxs (reflect x s hxx ((fixed s hs).mpr (.inr rfl)) he),
       fun he => hxr (reflect x r hxx ((fixed r hr).mpr (.inl rfl)) he), closed x hxx⟩
  have free (x : Nat) (hx : x ∈ zs) : T x ≠ x := by
    obtain ⟨hxs, hxr, hxx⟩ := (mem_zs x).mp hx
    intro he
    exact ((fixed x hxx).mp he).elim hxr hxs
  have hpz := pair_product zs (ynd.erase _) stable (fun x hx => inv x (sub x hx))
    free (fun x hx => pair x (sub x hx))
  have hpr : xs.Perm (r :: ys) := QR.perm_cons_erase hr
  have hps : ys.Perm (s :: zs) := QR.perm_cons_erase hsy
  have hlen : (xs.length-2)/2 = zs.length/2 := by
    have h₁ := hpr.length_eq
    have h₂ := hps.length_eq
    simp only [List.length_cons] at h₁ h₂
    omega
  rw [perm_prod hpr]
  simp only [natProd, perm_prod hps, ← Nat.mul_assoc, hlen]
  exact (Nat.mul_mod (r*s) (natProd zs) p).trans
    (by rw [hpz, ← Nat.mul_mod])

end QR
