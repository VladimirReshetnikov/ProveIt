import IPRADerivations.Combinatorics.HallCondition
import IPRADerivations.Core.CertificateTactics

/-!
# Sphere packing, sphere covering and the Singleton bound

Packet: `combinatorics/Combinatorics-iPRA`, `structure.tex`, results 48 ("Hamming, Singleton, and Gilbert
bounds") and 49 ("Perfect binary codes"). A code has `m` words, the ambient space `N` words, and the balls
about the codewords are an incidence table `B c w` of integer terms (a bit when `w` is in the ball of `c`); the
ball volume is a term `V`. As iPRA derivations:

* `sumFin_const`: `∑_{i : Fin m} V = m V`;
* `sphere_packing`: "Radius-`t` balls about codewords are disjoint ... Counting all their points gives the
  first bound": balls with at least `V` points, each word in at most one ball, give `m V ≤ N`;
* `singleton_bound`: "deletion is injective on `C`, proving Singleton's bound": an injection of the `m`
  codewords into `K` words, as a table with row sums at least one and column sums at most one, gives `m ≤ K`;
* `sphere_covering`: "balls of radius `d − 1` around the final code cover all `q^n` words. Counting them with
  multiplicity gives the opposite inequality": balls with at most `V` points covering every word give
  `N ≤ m V`;
* `perfect_code`: balls of exactly `V` points that partition the words give `m V = N` (the two inequalities),
  as for the binary Hamming code with `V = n + 1`.

Not derived: the ball volume `V_q(n, t)` as a count of words, the triangle inequality of the Hamming distance,
the greedy construction of the Gilbert code and the Hamming code itself.
-/

namespace LeanProofs.IPRA.Combinatorics.CodingBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.HallCondition (double_weighted)
open Syn
open scoped Fm

variable {n m N K : ℕ} {Γ : List (Fm PTm n)}

/-- `∑_{i : Fin m} V = m V`. -/
theorem sumFin_const (V : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun _ : Fin m => V) (ZT.natLit m * V) := by
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- The sphere-packing bound: `m V ≤ N`. -/
theorem sphere_packing (B : Fin m → Fin N → ZT n) (V : ZT n)
    (hball : ∀ c, Γ ⊢[PRAAx] zle V (ZT.sumFin fun w => B c w))
    (hdisj : ∀ w, Γ ⊢[PRAAx] zle (ZT.sumFin fun c => B c w) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] zle (ZT.natLit m * V) (ZT.natLit N) := by
  have h := double_weighted B (fun _ => V) (fun _ => ZT.natLit 1) hball hdisj
  ipra_zle (zsl h) with ZT.toZ_eq (sumFin_const (Γ := Γ) (m := m) V) -
    ZT.toZ_eq (sumFin_const (Γ := Γ) (m := N) (ZT.natLit 1))

/-- The Singleton bound in its counting form: an injection of `m` words into `K` words gives `m ≤ K`. -/
theorem singleton_bound (T : Fin m → Fin K → ZT n)
    (hrow : ∀ c, Γ ⊢[PRAAx] zle (ZT.natLit 1) (ZT.sumFin fun w => T c w))
    (hinj : ∀ w, Γ ⊢[PRAAx] zle (ZT.sumFin fun c => T c w) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] zle (ZT.natLit m) (ZT.natLit K) := by
  have h := sphere_packing T (ZT.natLit 1) hrow hinj
  ipra_zle (zsl h)

/-- The sphere-covering bound: `N ≤ m V`. -/
theorem sphere_covering (B : Fin m → Fin N → ZT n) (V : ZT n)
    (hball : ∀ c, Γ ⊢[PRAAx] zle (ZT.sumFin fun w => B c w) V)
    (hcov : ∀ w, Γ ⊢[PRAAx] zle (ZT.natLit 1) (ZT.sumFin fun c => B c w)) :
    Γ ⊢[PRAAx] zle (ZT.natLit N) (ZT.natLit m * V) := by
  have h := double_weighted (fun w c => B c w) (fun _ => ZT.natLit 1) (fun _ => V) hcov hball
  ipra_zle (zsl h) with ZT.toZ_eq (sumFin_const (Γ := Γ) (m := N) (ZT.natLit 1)) -
    ZT.toZ_eq (sumFin_const (Γ := Γ) (m := m) V)

/-- A perfect code: balls of `V` points partitioning the words give `m V ≤ N` and `N ≤ m V`. -/
theorem perfect_code (B : Fin m → Fin N → ZT n) (V : ZT n)
    (hball : ∀ c, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun w => B c w) V)
    (hpart : ∀ w, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun c => B c w) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit m * V) (ZT.natLit N) := by
  have hb : ∀ c, ∑ w, ZT.toZ Γ (B c w) = ZT.toZ Γ V := fun c => by
    have e := ZT.toZ_eq (hball c)
    simpa only [ZT.toZ_sumFin] using e
  have hp : ∀ w, ∑ c, ZT.toZ Γ (B c w) = 1 := fun w => by
    have e := ZT.toZ_eq (hpart w)
    simpa only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_one] using e
  have sw : ∑ c, ∑ w, ZT.toZ Γ (B c w) = ∑ w, ∑ c, ZT.toZ Γ (B c w) := Finset.sum_comm
  rw [Finset.sum_congr rfl fun c _ => hb c, Finset.sum_congr rfl fun w _ => hp w] at sw
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, _root_.mul_one] at sw
  apply ZT.derive
  simp only [ZT.toZ_mul, ZT.toZ_natLit]
  exact sw

end LeanProofs.IPRA.Combinatorics.CodingBounds
