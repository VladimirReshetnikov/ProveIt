import QuadraticReciprocity
import QRPermutation

namespace QR

def phase (p k : Nat) : Nat := if k%2=0 then 1 else p-1

theorem mul_mod_congr {u v x y p : Nat} (h₁ : u%p=v%p) (h₂ : x%p=y%p) :
    u*x%p=v*y%p := by
  calc _ = u%p*(x%p)%p := Nat.mul_mod _ _ _
       _ = v%p*(y%p)%p := by rw [h₁,h₂]
       _ = _ := (Nat.mul_mod _ _ _).symm

theorem neg_mul_mod {p t : Nat} (ht : 0<t) (htp : t<p) : (p-1)*t%p = p-t := by
  have h : ((p-1)*t+t)%p = 0 := by
    rw [← Nat.succ_mul, show (p-1).succ=p by omega]
    simp
  rw [Nat.add_mod_eq_sub, Nat.mod_eq_of_lt htp] at h
  have hb := Nat.mod_lt ((p-1)*t) (by omega : 0<p)
  split at h <;> omega

theorem phase_mul {p : Nat} (hp : 1<p) (u v : Nat) :
    phase p (u+v)%p = phase p u * phase p v % p := by
  have hneg := neg_mul_mod (p:=p) (t:=p-1) (by omega) (by omega)
  have hone : 1%p=1 := Nat.mod_eq_of_lt hp
  have hminus : (p-1)%p=p-1 := Nat.mod_eq_of_lt (by omega)
  unfold phase
  split <;> split <;> split <;> simp_all <;> omega

/-- Each multiplier contributes its high-half sign times its folded representative. -/
theorem signed_rep {p a i : Nat} (hp : primeB p = true) (ha : a%p≠0)
    (hi : 0<i) (hbi : i≤half p) :
    a*i%p = phase p (if half p<a*i%p then 1 else 0) * foldRep p (a*i%p) %p := by
  have hp1 := (primeB_spec.mp hp).1
  have hi0 := mul_res_pos hp ha hi (by unfold half at hbi; omega)
  have hir := Nat.mod_lt (a*i) (by omega : p>0)
  by_cases h : half p<a*i%p
  · simp only [h, if_true, foldRep, phase]
    have hx := neg_mul_mod (p:=p) (t:=p-a*i%p) (by omega) (by omega)
    simpa using (show a*i%p = (p-1)*(p-a*i%p)%p by omega)
  · simp [h, foldRep, phase]

def prod1 (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n+1 => prod1 f n * f (n+1)

theorem prod1_mul (f g : Nat → Nat) (n : Nat) :
    prod1 (fun i => f i * g i) n = prod1 f n * prod1 g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [prod1, ih]; ac_rfl

theorem prod1_const (a n : Nat) : prod1 (fun _ => a) n = a^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prod1, ih, Nat.pow_succ]

theorem prod1_congr_mod {p : Nat} {f g : Nat → Nat} (n : Nat)
    (h : ∀ i, 0<i → i≤n → f i%p=g i%p) : prod1 f n %p = prod1 g n %p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact mul_mod_congr (ih (by intro i hi hib; exact h i hi (by omega))) (h _ (by omega) (by omega))

theorem prod1_phase {p : Nat} (hp : 1<p) (f : Nat → Nat) (n : Nat) :
    prod1 (fun i => phase p (f i)) n %p = phase p (sum1 f n) %p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prod1,sum1,phase_mul hp]
    exact mul_mod_congr ih rfl

/-- All factors in a prefix of the half factorial are units. -/
theorem half_factorial_unit {p : Nat} (hp : primeB p = true) (n : Nat) (hn : n≤half p) :
    prod1 id n %p ≠ 0 := by
  have hp1 := (primeB_spec.mp hp).1
  induction n with
  | zero => simp [prod1, Nat.mod_eq_of_lt hp1]
  | succ n ih =>
    intro he
    have hd := dvd_cancel_unit hp (ih (by omega)) (Nat.dvd_of_mod_eq_zero he)
    have hle := Nat.le_of_dvd (by omega : 0<n+1) hd
    unfold half at hn
    omega

theorem cancel_mod {p a u v : Nat} (hp : primeB p = true) (ha : a%p≠0)
    (he : a*u%p=a*v%p) : u%p = v%p := by
  have hp1 := (primeB_spec.mp hp).1
  apply mul_injective_mod hp ha (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
  simpa using he

/-- Pairwise parity identity behind Eisenstein's form of Gauss's lemma. -/
theorem eisenstein_term {p a : Nat} (hp : p%2=1) (ha : a%2=1) (i : Nat) :
    (i + (if half p < a*i%p then 1 else 0))%2 =
    (a*i/p + foldRep p (a*i%p))%2 := by
  have h := congrArg (fun z : Nat => z%2) (Nat.mod_add_div (a*i) p)
  dsimp at h
  rw [Nat.add_mod, Nat.mul_mod p, hp, Nat.one_mul, Nat.mod_mod,
    show a*i%2=i%2 by rw [Nat.mul_mod, ha, Nat.one_mul, Nat.mod_mod]] at h
  have hr := Nat.mod_lt (a*i) (by omega : p>0)
  unfold foldRep
  split <;> omega

theorem sum1_mod_congr {p : Nat} {f g : Nat → Nat} (n : Nat)
    (h : ∀ i, 0<i → i≤n → f i%p=g i%p) : sum1 f n %p = sum1 g n %p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum1]
    rw [Nat.add_mod, ih (by intro i hi hib; exact h i hi (by omega)), h _ (by omega) (by omega)]
    exact (Nat.add_mod _ _ _).symm

theorem sum1_range (f : Nat → Nat) (n : Nat) :
    sum1 f n = natSum ((List.range' 1 n).map f) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum1,natSum_range_succ,ih]

theorem prod1_range (f : Nat → Nat) (n : Nat) :
    prod1 f n = natProd ((List.range' 1 n).map f) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prod1,natProd_range_succ,ih]

theorem fold_perm {p a : Nat} (hp : primeB p = true) (hodd : p%2=1) (ha : a%p≠0) :
    ((List.range' 1 (half p)).map (fun i => foldRep p (a*i%p))).Perm (List.range' 1 (half p)) :=
  map_range_perm _ (fun _ hi hib => fold_maps hp hodd ha hi hib)
    (fun _ _ hi hib hj hjb => fold_injective hp ha hi hib hj hjb)

theorem eisenstein {p a : Nat} (hp : primeB p = true) (hodd : p%2=1)
    (ha : a%p≠0) (haodd : a%2=1) : highCount p a %2 = floorSum p a %2 := by
  have hf : sum1 (fun i => foldRep p (a*i%p)) (half p) = sum1 id (half p) := by
    rw [sum1_range,sum1_range,List.map_id]
    exact perm_sum (fold_perm hp hodd ha)
  have hsum := sum1_mod_congr (p:=2)
    (f:=fun i => id i + (if half p<a*i%p then 1 else 0))
    (g:=fun i => a*i/p + foldRep p (a*i%p)) (half p)
    (fun i _ _ => eisenstein_term hodd haodd i)
  rw [sum1_add,sum1_add,hf] at hsum
  unfold highCount floorSum
  omega

/-- The signed half-factorial identity with the common factorial cancelled. -/
theorem gauss_power {p a : Nat} (hp : primeB p = true) (hodd : p%2=1)
    (ha : a%p≠0) : a^(half p)%p = phase p (highCount p a) := by
  let I := fun i => if half p<a*i%p then 1 else 0
  let F := fun i => foldRep p (a*i%p)
  have hp1 := (primeB_spec.mp hp).1
  have hf : prod1 F (half p) = prod1 id (half p) := by
    rw [prod1_range,prod1_range,List.map_id]
    exact perm_prod (fold_perm hp hodd ha)
  have hprod := prod1_congr_mod (p:=p)
    (f:=fun i => a * id i) (g:=fun i => phase p (I i) * F i)
    (half p) (fun _ hi hib => signed_rep hp ha hi hib)
  rw [prod1_mul,prod1_mul,prod1_const,hf] at hprod
  have hsign := prod1_phase hp1 I (half p)
  have hfinal := hprod.trans (mul_mod_congr hsign (rfl : prod1 id (half p)%p = _))
  rw [Nat.mul_comm _ (prod1 id _), Nat.mul_comm _ (prod1 id _)] at hfinal
  have hc := cancel_mod hp (half_factorial_unit hp (half p) (Nat.le_refl _)) hfinal
  change a^half p%p = phase p (highCount p a)%p at hc
  have hb : phase p (highCount p a) < p := by unfold phase; split <;> omega
  rwa [Nat.mod_eq_of_lt hb] at hc

/-- Euler criterion stated as an equality of the natural representatives of the two signs. -/
def EulerLaw (p a : Nat) : Prop :=
  a^(half p)%p = if squareB p a then 1 else p-1

theorem gauss_of_euler {p a : Nat} (hp : primeB p = true) (hodd : p%2=1)
    (ha : a%p≠0) (he : EulerLaw p a) : GaussLaw p a := by
  have hg := (gauss_power hp hodd ha).symm.trans he
  have hp1 := (primeB_spec.mp hp).1
  unfold GaussLaw nonresBit
  unfold phase at hg
  split at hg <;> split at hg <;> rename_i hs <;> simp [hs] <;> omega

theorem unit_at_distinct_primes {p q : Nat} (hp : primeB p=true) (hq : primeB q=true)
    (hne : p ≠ q) : q%p ≠ 0 := by
  have hp1 := (primeB_spec.mp hp).1
  intro hz
  rcases prime_divisor hq (Nat.dvd_of_mod_eq_zero hz) with h | h <;> omega

/-- The sole local premise for this assembly is Euler's criterion at the two inputs. -/
theorem reciprocity_of_euler {p q : Nat} (hp : primeB p=true) (hq : primeB q=true)
    (hop : p%2=1) (hoq : q%2=1) (hne : p≠q)
    (ep : EulerLaw p q) (eq : EulerLaw q p) :
    (nonresBit p q + nonresBit q p)%2 = half p * half q %2 := by
  have hup := unit_at_distinct_primes hp hq hne
  have huq := unit_at_distinct_primes hq hp (Ne.symm hne)
  have gp := gauss_of_euler hp hop hup ep
  have gq := gauss_of_euler hq hoq huq eq
  unfold GaussLaw at gp gq
  rw [gp,gq,eisenstein hp hop hup hoq,eisenstein hq hoq huq hop,
    ← Nat.add_mod, floor_sum_swap hp hq hne]

example : (nonresBit 7 11 + nonresBit 11 7)%2 = 1 := by decide
example : (nonresBit 5 29 + nonresBit 29 5)%2 = 0 := by decide

end QR
