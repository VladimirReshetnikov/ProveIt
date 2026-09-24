import Diophantine.Common.DiophantinePairing
import Diophantine.Common.RecursivelyEnumerableDioph
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin

/-!
# The Diophantine graph of the nth prime

Primality is primitive recursive by bounded trial division. Counting primes
below an output is primitive recursive by filtering a finite range. An output
is the prime with zero-based index `r` exactly when it is prime and has `r`
smaller primes. The recursively enumerable to Diophantine bridge therefore
gives an exact graph with the article's one-based index `n` represented by
`n - 1`.

The graph includes every natural input: at both `n = 0` and `n = 1` the output
is the first prime, two. This construction establishes Diophantineness without
claiming the article's numerical bound on the number of witnesses.
-/

namespace JSWW1976

private theorem prime_primrecPred : PrimrecPred Nat.Prime := by
  have hmod : PrimrecPred (fun p : ℕ × ℕ => p.2 % p.1 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst) (Primrec.const 0)
  have hone : PrimrecPred (fun p : ℕ × ℕ => p.1 = 1) :=
    Primrec.eq.comp Primrec.fst (Primrec.const 1)
  have hdivisor : PrimrecPred (fun p : ℕ × ℕ => p.1 ∣ p.2 → p.1 = 1) := by
    refine (hmod.not.or hone).of_eq ?_
    intro p
    constructor
    · rintro (hnot | hunit) hdiv
      · exact False.elim (hnot (Nat.dvd_iff_mod_eq_zero.mp hdiv))
      · exact hunit
    · intro h
      by_cases hzero : p.2 % p.1 = 0
      · exact Or.inr (h (Nat.dvd_iff_mod_eq_zero.mpr hzero))
      · exact Or.inl hzero
  have hbounded : PrimrecPred (fun n : ℕ => ∀ d < n, d ∣ n → d = 1) :=
    hdivisor.primrecRel.forall_lt.comp Primrec.id Primrec.id
  exact ((Primrec.nat_le.comp (Primrec.const 2) Primrec.id).and hbounded).of_eq
    (fun _ => Nat.prime_def_lt.symm)

private theorem primeCount_primrec : Primrec (Nat.count Nat.Prime) := by
  have hfilter : Primrec (fun n : ℕ => (List.range n).filter (Nat.Prime ·)) :=
    (Primrec.listFilter prime_primrecPred).comp Primrec.list_range
  refine (Primrec.list_length.comp hfilter).of_eq ?_
  intro n
  simp only [Nat.count, List.countP_eq_length_filter]

/-- An exact finite-count characterization of the zero-based nth prime. -/
private theorem nth_prime_eq_iff (index output : ℕ) :
    Nat.nth Nat.Prime index = output ↔
      Nat.Prime output ∧ Nat.count Nat.Prime output = index := by
  constructor
  · intro h
    subst output
    exact ⟨Nat.nth_mem_of_infinite Nat.infinite_setOf_prime index,
      Nat.count_nth_of_infinite Nat.infinite_setOf_prime index⟩
  · rintro ⟨hprime, hcount⟩
    rw [← hcount]
    exact Nat.nth_count hprime

private theorem packedNthPrime_primrecPred : PrimrecPred (fun packed : ℕ =>
    Nat.nth Nat.Prime (packed.unpair.1 - 1) = packed.unpair.2) := by
  have hindex : Primrec (fun packed : ℕ => packed.unpair.1 - 1) :=
    Primrec.nat_sub.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1)
  have houtput : Primrec (fun packed : ℕ => packed.unpair.2) :=
    Primrec.snd.comp Primrec.unpair
  have hprime := prime_primrecPred.comp houtput
  have hcount := Primrec.eq.comp (primeCount_primrec.comp houtput) hindex
  exact (hprime.and hcount).of_eq
    (fun packed => (nth_prime_eq_iff (packed.unpair.1 - 1) packed.unpair.2).symm)

/-- The exact nth-prime graph is Diophantine, with natural subtraction making
the input zero denote the first prime as well. -/
theorem nthPrime_graph_dioph :
    Dioph {v : Fin 2 → ℕ | Nat.nth Nat.Prime (v 0 - 1) = v 1} := by
  have hpacked : Dioph {v : Unit → ℕ |
      Nat.nth Nat.Prime ((v ()).unpair.1 - 1) = (v ()).unpair.2} :=
    Diophantine.rePred_dioph packedNthPrime_primrecPred.computablePred.to_re
  have hlift : Dioph {v : Option (Fin 2) → ℕ |
      Nat.nth Nat.Prime ((v none).unpair.1 - 1) = (v none).unpair.2} :=
    Dioph.reindex_dioph (Option (Fin 2)) (fun _ : Unit => none) hpacked
  have hpair : Dioph.DiophFn (fun v : Fin 2 → ℕ => Nat.pair (v 0) (v 1)) :=
    Diophantine.pair_dioph (Dioph.proj_dioph 0) (Dioph.proj_dioph 1)
  have hgraph := Dioph.diophFn_comp1 hlift hpair
  change Dioph {v : Fin 2 → ℕ |
    Nat.nth Nat.Prime ((Nat.pair (v 0) (v 1)).unpair.1 - 1) =
      (Nat.pair (v 0) (v 1)).unpair.2} at hgraph
  simpa only [Nat.unpair_pair] using hgraph

end JSWW1976
