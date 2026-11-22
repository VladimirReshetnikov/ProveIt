import QuadraticReciprocity
import Involution
import QRConstructiveList

namespace QR

private abbrev units (p : Nat) := List.range' 1 (p-1)

private theorem mem_units {p k : Nat} (hp : 0 < p) :
    k ∈ units p ↔ 0 < k ∧ k < p := by
  unfold units
  rw [List.mem_range'_1]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> exact ⟨by omega,by omega⟩

/-- Last successful index, or zero if there is no successful index. -/
private def solve (p x a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => if x*n%p = a%p then n else solve p x a n

private theorem solve_spec {p x a : Nat} (n k : Nat)
    (hk : k < n) (he : x*k%p = a%p) :
    solve p x a n < n ∧ x*(solve p x a n)%p = a%p := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    simp only [solve]
    split
    · rename_i h; exact ⟨by omega, h⟩
    · rename_i h
      have hkn : k < n := by
        by_cases e : k=n
        · exact False.elim (h (e ▸ he))
        · omega
      obtain ⟨hbound,hspec⟩ := ih k hkn he
      exact ⟨by omega,hspec⟩

private theorem unit_perm {p x : Nat} (hp : primeB p = true) (hx : x%p ≠ 0) :
    ((units p).map (fun k => x*k%p)).Perm (units p) := by
  have hp1 := (primeB_spec.mp hp).1
  apply map_range_perm
  · intro i hi hib
    have hr := Nat.mod_lt (x*i) (by omega : 0 < p)
    exact ⟨mul_res_pos hp hx hi (by omega), by omega⟩
  · intro i j _ hi _ hj he
    exact mul_injective_mod hp hx (by omega) (by omega) he

private def partner (p a x : Nat) := solve p x a p

private theorem partner_spec {p a x : Nat} (hp : primeB p = true) (ha : a%p ≠ 0)
    (hx : x ∈ units p) :
    partner p a x ∈ units p ∧ x*(partner p a x)%p = a%p := by
  have hp1 := (primeB_spec.mp hp).1
  have hx' := (mem_units (by omega : 0<p)).mp hx
  have hr := Nat.mod_lt a (by omega : 0<p)
  have hxunit : x%p ≠ 0 := by rw [Nat.mod_eq_of_lt hx'.2]; omega
  have ha' : a%p ∈ units p := (mem_units (by omega : 0<p)).mpr ⟨by omega,hr⟩
  obtain ⟨k,hk,he⟩ := List.mem_map.mp ((unit_perm hp hxunit).mem_iff.mpr ha')
  have hks := (mem_units (by omega : 0<p)).mp hk
  have ⟨hb,hs⟩ := solve_spec p k hks.2 he
  change solve p x a p ∈ units p ∧ x*(solve p x a p)%p = a%p
  refine ⟨(mem_units (by omega : 0<p)).mpr ⟨?_,hb⟩,hs⟩
  by_cases hz : solve p x a p=0
  · simp [hz] at hs
    omega
  · omega

private theorem partner_invol {p a x : Nat} (hp : primeB p = true) (ha : a%p ≠ 0)
    (hx : x ∈ units p) : partner p a (partner p a x) = x := by
  have hp1 := (primeB_spec.mp hp).1
  have ⟨hy,he⟩ := partner_spec hp ha hx
  have ⟨hz,hf⟩ := partner_spec hp ha hy
  have hx' := (mem_units (by omega : 0<p)).mp hx
  have hy' := (mem_units (by omega : 0<p)).mp hy
  have hz' := (mem_units (by omega : 0<p)).mp hz
  have hyunit : partner p a x % p ≠ 0 := by rw [Nat.mod_eq_of_lt hy'.2]; omega
  rw [Nat.mul_comm x] at he
  exact mul_injective_mod hp hyunit hz'.2 hx'.2 (hf.trans he.symm)

private theorem partner_fixed {p a x : Nat} (hp : primeB p = true) (ha : a%p ≠ 0)
    (hx : x ∈ units p) : partner p a x = x ↔ x*x%p = a%p := by
  have hp1 := (primeB_spec.mp hp).1
  have ⟨hy,he⟩ := partner_spec hp ha hx
  have hx' := (mem_units (by omega : 0<p)).mp hx
  have hy' := (mem_units (by omega : 0<p)).mp hy
  constructor
  · intro hf; simpa [hf] using he
  · intro hf
    have hxunit : x%p ≠ 0 := by rw [Nat.mod_eq_of_lt hx'.2]; omega
    exact mul_injective_mod hp hxunit hy'.2 hx'.2 (he.trans hf.symm)

private theorem square_one {p x : Nat} (hp : primeB p = true) (hx : x ∈ units p) :
    x*x%p = 1 ↔ x=1 ∨ x=p-1 := by
  have hp1 := (primeB_spec.mp hp).1
  have hx' := (mem_units (by omega : 0<p)).mp hx
  constructor
  · intro h
    by_cases e : x=1
    · exact .inl e
    · right
      have hfact : (x-1)*(x+1) + 1 = x*x := by
        cases x with
        | zero => omega
        | succ k => simp [Nat.add_mul, Nat.mul_add]; omega
      have hdiv := Nat.mod_add_div (x*x) p
      rw [h] at hdiv
      have hd : p ∣ (x-1)*(x+1) := ⟨(x*x)/p, by omega⟩
      have hl : x-1 < p := by omega
      have hn : (x-1)%p ≠ 0 := by rw [Nat.mod_eq_of_lt hl]; omega
      have hz := Nat.le_of_dvd (by omega : 0 < x+1) (dvd_cancel_unit hp hn hd)
      omega
  · rintro (rfl | rfl)
    · simp [Nat.mod_eq_of_lt hp1]
    · have ident : (p-1)*(p-1) = 1+(p-2)*p := by
        generalize ht : p-2 = t
        have he : p=t+2 := by omega
        rw [he]
        simp [Nat.add_mul, Nat.mul_add]; omega
      rw [ident, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp1]


/-- Wilson's theorem, pairing each unit with its inverse. -/
theorem wilson_product {p : Nat} (hp : primeB p = true) (hodd : p%2 = 1) :
    natProd (List.range' 1 (p-1)) % p = p-1 := by
  have hp1 := (primeB_spec.mp hp).1
  have hp0 : 0<p := by omega
  have hone : 1%p=1 := Nat.mod_eq_of_lt hp1
  have hone' : 1%p ≠ 0 := by omega
  have h := two_fixed_product (p:=p) (a:=1) (r:=1) (s:=p-1) (T:=partner p 1)
    (units p) (nodup_range_one 1 (p-1))
    (fun _ hx => (partner_spec hp hone' hx).1)
    (fun _ hx => partner_invol hp hone' hx)
    (fun x hx => (partner_fixed hp hone' hx).trans (by rw [hone]; exact square_one hp hx))
    ((mem_units hp0).mpr ⟨by omega,by omega⟩)
    ((mem_units hp0).mpr ⟨by omega,by omega⟩)
    (by omega)
    (fun _ hx => (partner_spec hp hone' hx).2)
  simpa [units,Nat.mod_eq_of_lt (by omega : p-1<p)] using h

private theorem mod_mul_congr {a b c d p : Nat} (h₁ : a%p = c%p) (h₂ : b%p=d%p) :
    a*b%p = c*d%p := by rw [Nat.mul_mod a b, Nat.mul_mod c d, h₁, h₂]

private theorem mod_pow_congr {a b p : Nat} (h : a%p = b%p) (n : Nat) :
    a^n%p=b^n%p := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [Nat.pow_succ] using mod_mul_congr ih h

private theorem scale_prod (p c : Nat) (xs : List Nat) :
    natProd (xs.map (fun k => c*k%p)) % p = (c^xs.length * natProd xs) % p := by
  induction xs with
  | nil => simp [natProd]
  | cons x xs ih =>
    simp only [List.map_cons,List.length_cons,natProd,Nat.pow_succ]
    calc
      _ = ((c*x) * (c^xs.length * natProd xs)) % p :=
        mod_mul_congr (Nat.mod_mod _ _) ih
      _ = _ := by congr 1; ac_rfl

/-- Fermat's unit form, using the permutation induced by multiplication. -/
theorem fermat_unit {p x : Nat} (hp : primeB p = true) (hodd : p%2=1)
    (hx : x%p ≠ 0) : x^(p-1)%p = 1 := by
  have hp1 := (primeB_spec.mp hp).1
  have hp0 : 0<p := by omega
  let F := natProd (units p)
  have hF : F%p=p-1 := wilson_product hp hodd
  have hprod := scale_prod p x (units p)
  rw [perm_prod (unit_perm hp hx)] at hprod
  have ht : F%p = (x^(p-1)*F)%p := by simpa [F, units] using hprod
  apply mul_injective_mod (a:=F) hp (by omega) (Nat.mod_lt _ hp0) hp1
  rw [Nat.mul_mod_mod, Nat.mul_one, Nat.mul_comm F]; exact ht.symm

/-- Euler's criterion with the square-root test as a bounded Boolean search. -/
theorem euler_criterion {p a : Nat} (hp : primeB p = true) (hodd : p%2=1)
    (ha : a%p ≠ 0) :
    a^(half p)%p = (if squareB p a then 1 else p-1) := by
  have hp1 := (primeB_spec.mp hp).1
  have hp0 : 0<p := by omega
  cases hs : squareB p a with
  | true =>
    obtain ⟨x,hx,he⟩ := squareB_spec.mp hs
    have hx0 : x ≠ 0 := by rintro rfl; simp at he; omega
    have hxunit : x%p ≠ 0 := by rw [Nat.mod_eq_of_lt hx]; exact hx0
    have heven : 2*(half p) = p-1 := by unfold half; omega
    calc
      _ = (x*x)^(half p)%p := mod_pow_congr he.symm _
      _ = x^(p-1)%p := by rw [← Nat.pow_two, ← Nat.pow_mul, heven]
      _ = _ := fermat_unit hp hodd hxunit
  | false =>
    have hfree (x : Nat) (hx : x ∈ units p) : partner p a x ≠ x := by
      intro he
      have he' := (partner_fixed hp ha hx).mp he
      have hx' := (mem_units hp0).mp hx
      have hit := squareB_spec.mpr ⟨x,hx'.2,he'⟩
      rw [hs] at hit
      contradiction
    have h := pair_product (p:=p) (a:=a) (T:=partner p a) (units p) (nodup_range_one 1 (p-1))
      (fun _ hx => (partner_spec hp ha hx).1) (fun _ hx => partner_invol hp ha hx)
      hfree (fun _ hx => (partner_spec hp ha hx).2)
    have hWilson := wilson_product hp hodd
    simp only [units,List.length_range',hWilson] at h
    exact h.symm

end QR
