import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-!
# Exact search for pairs of sixth-power norms

A divisor of `q^6-p^6` determines the smaller squared term in a potential
norm collision. The checker uses only the factorizations of four small
positive factors, a bounded divisor traversal, and small residue masks.
-/

namespace GRHArticle.ClassGroups

/-- The lower endpoint of the two discriminant gaps. -/
def censusDiscriminantCutoff : ℕ := 310000000000000000000

/-- The four bounded factors of the difference of sixth powers. -/
def sixthPowerDifferenceFactors (p q : ℕ) : List ℕ :=
  [q-p, q+p, q^2+p*q+p^2, q^2-p*q+p^2]

theorem sixthPowerDifferenceFactors_prod {p q : ℕ} (hpq : p < q) :
    (sixthPowerDifferenceFactors p q).prod = q^6-p^6 := by
  have hp6 : p^6 ≤ q^6 := Nat.pow_le_pow_left hpq.le _
  have hpq' : p*q ≤ q^2 := by simpa only [pow_two] using Nat.mul_le_mul_right q hpq.le
  simp only [sixthPowerDifferenceFactors, List.prod_cons, List.prod_nil, mul_one]
  zify [hpq.le, hp6, hpq']
  ring

/-- Compute the prime exponents from the factorizations of the small factors. -/
def groupedFactorPowers (factors : List ℕ) : List (ℕ × ℕ) :=
  let l := factors.flatMap Nat.primeFactorsList
  l.dedup.map (fun p ↦ (p,l.count p))

private theorem groupedFactorPowers_prime (factors : List ℕ) {p : ℕ × ℕ}
    (hp : p ∈ groupedFactorPowers factors) : p.1.Prime := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  obtain ⟨n,_,hn⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hq)
  exact Nat.prime_of_mem_primeFactorsList hn

private theorem prod_flatMap_primeFactorsList (factors : List ℕ) (hs : ∀ x ∈ factors, x ≠ 0) :
    (factors.flatMap Nat.primeFactorsList).prod = factors.prod := by
  induction factors with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, List.prod_append, List.prod_cons]
    rw [Nat.prod_primeFactorsList (hs a (by simp)), ih (fun n hn ↦ hs n (by simp [hn]))]

theorem groupedFactorPowers_prod (factors : List ℕ) (hs : ∀ x ∈ factors, x ≠ 0) :
    ((groupedFactorPowers factors).map (fun pe ↦ pe.1^pe.2)).prod = factors.prod := by
  let l := factors.flatMap Nat.primeFactorsList
  have hset : l.dedup.toFinset = l.toFinset := by
    ext p
    simp [List.mem_dedup]
  have hp := ((List.toFinset_toList (List.nodup_dedup l)).map (fun p ↦ p^l.count p)).prod_eq
  simp only [hset, Finset.prod_map_toList, ← Finset.prod_list_count] at hp
  simpa only [groupedFactorPowers, List.map_map, Function.comp_def, l] using
    hp.symm.trans (prod_flatMap_primeFactorsList factors hs)

/-- Test products of prime powers up to the given bound, pruning a whole
branch once its existing factor exceeds that bound. -/
def checkBoundedDivisors (cap : ℕ) (test : ℕ → Bool) : List (ℕ × ℕ) → ℕ → Bool
  | [], d => if d ≤ cap then test d else true
  | (p,e)::L, d => if d ≤ cap then
      (List.range (e+1)).all fun i ↦ checkBoundedDivisors cap test L (d*p^i)
    else true

theorem checkBoundedDivisors_of_dvd {cap : ℕ} {test : ℕ → Bool} {L : List (ℕ × ℕ)}
    (hp : ∀ pe ∈ L, pe.1.Prime) {d u : ℕ} (hu₀ : 0 < u)
    (hu : u ∣ (L.map (fun pe ↦ pe.1^pe.2)).prod) (hle : d*u ≤ cap)
    (hv : checkBoundedDivisors cap test L d = true) : test (d*u) = true := by
  induction L generalizing d u with
  | nil =>
    have h1 : u = 1 := Nat.dvd_one.mp hu
    subst u
    simpa only [mul_one, checkBoundedDivisors, if_pos (by simpa only [mul_one] using hle)] using hv
  | cons pe L ih =>
    obtain ⟨p,e⟩ := pe
    simp only [List.map_cons, List.prod_cons] at hu
    obtain ⟨a,b,ha,hb,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hu
    obtain ⟨i,hi,rfl⟩ := (Nat.dvd_prime_pow (hp (p,e) (by simp))).mp ha
    have hd : d ≤ cap := (Nat.le_mul_of_pos_right d hu₀).trans hle
    have hb₀ : 0 < b := Nat.pos_of_ne_zero (fun h ↦ by simp [h] at hu₀)
    have h := List.all_eq_true.mp (show (List.range (e+1)).all
        (fun j ↦ checkBoundedDivisors cap test L (d*p^j)) = true from by
          simpa only [checkBoundedDivisors, if_pos hd] using hv)
      i (List.mem_range.mpr (Nat.lt_succ_of_le hi))
    rw [← mul_assoc] at hle ⊢
    exact ih (fun q hq ↦ hp q (by simp [hq])) hb₀ hb hle h

private def residueMask (r : ℕ) (l : List ℕ) : ℕ :=
  l.foldr (fun i a ↦ (2^((i+1)^2 % r)) ||| a) 0

private theorem testBit_residueMask_iff (r z : ℕ) (l : List ℕ) :
    (residueMask r l).testBit z = true ↔ ∃ i ∈ l, (i+1)^2 % r = z := by
  induction l with
  | nil => simp [residueMask]
  | cons i l ih =>
    change ((2^((i+1)^2 % r)) ||| residueMask r l).testBit z = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq, ih]
    constructor
    · rintro (he | ⟨j,hj,he⟩)
      · exact ⟨i,List.mem_cons_self,he⟩
      · exact ⟨j,List.mem_cons_of_mem _ hj,he⟩
    · rintro ⟨j,hj,he⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · exact Or.inl he
      · exact Or.inr ⟨j,hj,he⟩

/-- Nonzero squares modulo a small witness prime. -/
def squareResidueMask (r : ℕ) : ℕ :=
  residueMask r (List.range (r-1))

/-- The primes allowed in the arithmetic obstruction. -/
def sixthWitnessPrimes : List ℕ :=
  [19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151]

private theorem sixthWitnessPrimes_spec :
    ∀ r ∈ sixthWitnessPrimes, r.Prime ∧ 19 ≤ r ∧ r ≤ 151 := by
  decide +kernel

/-- The same witness primes paired with their Boolean square tables. -/
def sixthWitnessMasks : List (ℕ × ℕ) :=
  [(19, 199410),
    (23, 340830),
    (29, 332473074),
    (31, 303908790),
    (37, 96068509338),
    (41, 1870503675702),
    (43, 3678700564050),
    (47, 4626135339998),
    (53, 5310023542746834),
    (59, 156326468341437114),
    (61, 1662926210933060154),
    (67, 61808106872519771730),
    (71, 20052041432995567486),
    (73, 9059857384996697084766),
    (79, 89932533647391829339958),
    (83, 2911111237809585785085594),
    (89, 526807005835216593886842678),
    (97, 152076272278209298711361952606),
    (101, 1550432784880709368503235994226),
    (103, 1760368345969468176824550810518),
    (107, 50079290986288516948354744811034),
    (109, 473022961816146413042658758988474),
    (113, 8586949319576899938239170417650582),
    (127, 30790515292689894969866990722818747158),
    (131, 736595995152387833549853625256200223418),
    (137, 144045494737659012533968429665233398647702),
    (139, 264983527547230301571683161851591864167154),
    (149, 441852139177177952668163358831104772057793266),
    (151, 425021430996567349671854096638566139059703606)]

private theorem sixthWitnessMasks_eq :
    sixthWitnessMasks = sixthWitnessPrimes.map (fun r ↦ (r,squareResidueMask r)) := by
  decide +kernel

/-- `-M` has a nonzero square representative at one of the witness primes. -/
def HasSixthSquareWitness (M : ℕ) : Prop :=
  ∃ r, r.Prime ∧ 19 ≤ r ∧ r ≤ 151 ∧ M % r ≠ 0 ∧
    ∃ b, 0 < b ∧ b < r ∧ b^2 % r = (r-M%r)%r

/-- Test a candidate for a nonzero square residue. -/
def checkSixthSquareWitness (M : ℕ) : Bool :=
  sixthWitnessMasks.any fun (r,mask) ↦ M%r != 0 && mask.testBit ((r-M%r)%r)

theorem hasSixthSquareWitness_of_check {M : ℕ} (h : checkSixthSquareWitness M = true) :
    HasSixthSquareWitness M := by
  obtain ⟨a,ha,hb⟩ := List.any_eq_true.mp h
  rw [sixthWitnessMasks_eq] at ha
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hp,h₁,h₂⟩ := sixthWitnessPrimes_spec r hr
  simp only [Bool.and_eq_true] at hb
  obtain ⟨i,hi,he⟩ := (testBit_residueMask_iff r _ _).mp hb.2
  have hir := List.mem_range.mp hi
  exact ⟨r,hp,h₁,h₂,by simpa using hb.1,i+1,by omega,by omega,he⟩

/-- The value of `xb²` in the lower norm equation once the smaller
divisor is fixed. -/
def sixthNormCandidate (p q u : ℕ) : ℕ :=
  4*p^6 - ((q^6-p^6)/u-u)^2

/-- Check one pair across all relevant divisors. -/
def checkSixthNormPair (p q : ℕ) : Bool :=
  let N := q^6-p^6
  let lo := q^3-p^3
  checkBoundedDivisors N.sqrt (fun u ↦
    if lo < u then
      let M := sixthNormCandidate p q u
      if censusDiscriminantCutoff < M then checkSixthSquareWitness M else true
    else true) (groupedFactorPowers (sixthPowerDifferenceFactors p q)) 1

theorem hasSixthSquareWitness_of_pairCheck {p q u : ℕ} (hpq : p < q)
    (hu : u ∣ q^6-p^6) (hlo : q^3-p^3 < u) (hhi : u ≤ (q^6-p^6).sqrt)
    (hM : censusDiscriminantCutoff < sixthNormCandidate p q u)
    (hc : checkSixthNormPair p q = true) : HasSixthSquareWitness (sixthNormCandidate p q u) := by
  have hfac (n : ℕ) (hn : n ∈ sixthPowerDifferenceFactors p q) : n ≠ 0 := by
    simp only [sixthPowerDifferenceFactors, List.mem_cons, List.not_mem_nil, or_false] at hn
    have hq : 0 < q := by omega
    have hq₂ : 0 < q^2 := pow_pos hq _
    have hpq' : p*q < q^2 := by
      simpa only [pow_two] using Nat.mul_lt_mul_of_pos_right hpq hq
    rcases hn with rfl | rfl | rfl | rfl <;> omega
  have hprod := (groupedFactorPowers_prod _ hfac).trans (sixthPowerDifferenceFactors_prod hpq)
  have h := checkBoundedDivisors_of_dvd (fun _ hpe ↦ groupedFactorPowers_prime _ hpe)
    (u := u) (by omega) (hprod.symm ▸ hu) (by simpa only [one_mul] using hhi) hc
  apply hasSixthSquareWitness_of_check
  simpa only [one_mul, if_pos hlo, if_pos hM] using h

/-- Eligible primes for the full sixth-power search. -/
def sixthEligiblePrimes : List ℕ :=
  (List.range 5501).filter (fun p ↦ decide p.Prime && decide (censusDiscriminantCutoff < 4*p^6))

/-- Check every pair whose smaller-prime index lies in one contiguous block. -/
def checkSixthNormPairsBlock (start length : ℕ) : Bool :=
  let all := sixthEligiblePrimes
  ((all.drop start).take length).all fun p ↦
    all.all fun q ↦ if p < q then checkSixthNormPair p q else true

end GRHArticle.ClassGroups
