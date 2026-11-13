import Mathlib.NumberTheory.Dioph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Indexes
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Logic.Godel.GodelBetaFunction
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Computability.RE
import Mathlib.Tactic.Cases

/-!
# Every recursively enumerable set is Diophantine

This file proves the hard direction of the Matiyasevich–Robinson–Davis–Putnam
theorem. The public statement is `MRDP.mrdp`: a recursively enumerable subset
of `ℕ` is represented by one integer polynomial with finitely many witnesses.

The proof proceeds in four stages:

1. Recover binomial coefficients as digits of a power, then express factorials
   and finite products of CRT moduli using Diophantine operations.
2. Use the Chinese remainder theorem to replace a bounded universal quantifier
   by finitely many existential witnesses and arithmetic conditions.
3. Encode finite recursion traces to show that primitive recursive functions
   have Diophantine graphs.
4. Apply this to a bounded evaluator for a partial recursive semidecider, then
   combine two natural-coefficient polynomials into one integer polynomial.

`Dioph S` means that the set of assignments `S` is Diophantine; `DiophFn f`
means that the graph of `f` is Diophantine. The notation `D.1`, `D+`, `D*`,
`D/`, and `D%` constructs proofs of closure under constants and arithmetic.
The natural witnesses throughout this file may be zero.
-/

-- The closure search for the CRT certificate needs this elaboration budget.
set_option maxHeartbeats 250000

namespace MRDP

open Dioph Finset List MvPolynomial Nat Partrec.Code

/-! ## Binomial coefficients and finite polynomial representations -/

/-- Binomial coefficients of Diophantine functions are Diophantine.

For `q = 2^n + 1`, every coefficient in `(q + 1)^n` is smaller than `q`.
Consequently its base-`q` digit at position `k` is exactly `n.choose k`.
-/
lemma binomial_diophFn (dn : DiophFn.{0} n) (dk : DiophFn k) :
    DiophFn <| Function.uncurry choose ∘ Function.prod n k := by
  have hBase_dioph := pow_dioph (D.2) dn D+ D.1
  -- Division shifts the selected digit to the units place; remainder extracts it.
  convert pow_dioph (hBase_dioph D+ D.1) dn D/ pow_dioph hBase_dioph dk D% hBase_dioph
  dsimp
  generalize n _ = n
  let q := 2 ^ n + 1
  have hCoefficient_bound := n.choose_le_two_pow
  -- The binomial theorem supplies the finite list of base-q digits.
  erw [show q.succ ^ _ = ofDigits q (ofFn <| n.choose ∘ Fin.val) by
        simpa [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, sum_ofFn,
          sum_range, mul_comm] using add_pow q 1 _,
    ofDigits_div_pow_eq_ofDigits_drop _ (by lia) _ <| by grind,
    ofDigits_mod_eq_head!]
  simp_all [head!_eq_head?_getD, -ofFn_succ, apply_ite_left, q,
    choose_eq_zero_iff, Nat.mod_eq_of_lt]

/-- Represent a Diophantine set by equality of two natural-coefficient polynomials.

The input coordinates are unchanged. All auxiliary coordinates are replaced by
`Fin m`, so later arguments can take finite maxima and apply the finite CRT.
-/
lemma exists_fin_polynomial (hS : Dioph S) :
    ∃ m, ∃ e f : MvPolynomial (_ ⊕ Fin m) _,
      ∀ v, v ∈ S ↔ ∃ t,
        let assignment := Sum.elim v t
        e.eval assignment = f.eval assignment := by
  have ⟨_, P, hRepresentation⟩ := hS
  -- Split an integer polynomial expression into a difference of natural ones.
  have ⟨p, q, hDifference⟩ : ∃ p q, ∀ v, P v = ↑(eval v p) - eval v q := by
    refine' P.isPoly.rec
      (⟨X ·, 0, _⟩)
      (fun a => ⟨C a.toNat, C a.neg.toNat, _⟩)
      (fun _ _ ⟨a, b, _⟩ ⟨c, d, _⟩ => ⟨a + d, b + c, _⟩)
      fun _ _ ⟨a, b, _⟩ ⟨c, d, _⟩ => ⟨a * c + b * d, a * d + b * c, _⟩
    all_goals
      simp_all <;> grind
  -- Both polynomials use only finitely many coordinates. Enumerate their joint support.
  obtain ⟨s, p, q, rfl, rfl⟩ := exists_finset_rename₂ p q
  let coordinateMap x := Sum.map id (fun _ => s.equivFin x) x.val
  existsi _, p.rename coordinateMap, q.rename coordinateMap
  intro v
  simp_all [eval_rename, sub_eq_zero]
  constructor <;> rintro ⟨w, hw⟩
  -- Restrict an existing assignment to the finite support.
  existsi Sum.elim v w ∘ Subtype.val ∘ s.equivFin.symm
  swap
  -- Extend a finite witness by zero outside that support.
  existsi Subtype.val.extend (w ∘ s.equivFin) 0 ∘ Sum.inr
  all_goals
    convert hw <;>
    simp_all [funext_iff, coordinateMap, Function.extend_val_apply]

/-! ## Factorials and products of CRT moduli -/

/-- The modulus assigned to row `index` at a common factorial scale. -/
abbrev crtModulus (scale index : ℕ) := (index + 1) * scale + 1

/-- Factorials of Diophantine functions are Diophantine.

Set `r = (n + 2)^(n + 2)` and `C = (r + n).choose n`. The ascending factorial
estimate below shows that `n! = ((r + 1)^n + (C - 1)) / C`, a ceiling quotient.
-/
lemma factorial_diophFn (df : DiophFn.{0} g) : DiophFn <| Nat.factorial ∘ g := by
  have hShift_dioph := df D+ D.2
  have hRadius_dioph := pow_dioph hShift_dioph hShift_dioph
  have hChoose_dioph := binomial_diophFn (hRadius_dioph D+ df) df
  convert ←
    (pow_dioph (hRadius_dioph D+ D.1) df D+ (hChoose_dioph D- D.1)) D/ hChoose_dioph
  dsimp
  generalize g _ = n
  have hFactorial_bound := n.succ.succ.factorial_le_pow
  simp [factorial_succ] at hFactorial_bound
  set r := n.succ.succ ^ n.succ.succ
  -- Bound the error between a power and its corresponding ascending factorial.
  have hAscending_bound n : r.succ * r.succ.ascFactorial n ≤
      r.succ ^ n * r.succ + n ^ 2 * r.succ.ascFactorial n := by
    induction' n with n <;> simp_all [ascFactorial_succ, pow_succ]
    nlinarith [zero_le <| n * r.succ.ascFactorial n]
  have hChoose_pred := Nat.sub_add_cancel <| Nat.choose_pos <| n.le_add_left r
  -- These are the two inequalities characterizing the natural-number quotient.
  apply Nat.div_eq_of_lt_le
  all_goals
    nlinarith [hAscending_bound n, r.ascFactorial_eq_factorial_mul_choose n,
      r.succ.pow_succ_le_ascFactorial n]

/-- An arithmetic expression for the product of the first `len` CRT moduli.

Its syntax uses only powers, factorials, binomial coefficients, and remainders,
so its Diophantine character follows from the closure lemmas above.
-/
abbrev encodedModuliProduct (len T : ℕ) : ℕ :=
  let q := crtModulus T len ^ len + 2
  T ^ len * (len.factorial * choose (q + len) len) % (T * q - 1)

/-- The arithmetic encoding agrees with the actual finite product at positive scale. -/
lemma encodedModuliProduct_eq_prod (hT : 0 < T) :
    encodedModuliProduct len T = ∏ k ∈ range len, crtModulus T k := by
  -- The product lies below the remainder modulus used in its encoding.
  have hProduct_bound :=
    card_range len ▸ Finset.prod_le_pow_card _ (crtModulus T) (crtModulus ..) <| by
      intros
      unfold crtModulus
      gcongr
      exact?
  have hScaled_bound := hProduct_bound.trans <| Nat.le_mul_of_pos_left _ hT
  apply mod_eq_of_modEq _ <| by lia
  rw [← ascFactorial_eq_factorial_mul_choose, ascFactorial_eq_prod_range,
    pow_eq_prod_const T, ← prod_mul_distrib]
  gcongr
  -- Each factor difference is the negative of the encoding modulus.
  exact modEq_of_dvd ⟨-1, by lia⟩

/-! ## Polynomial evaluation and Diophantine closure -/

-- A row has parameters x, a distinguished index k, and a tuple of witnesses w.
-- `none` selects the index; `some i` selects parameter i; `Sum.inr` selects a witness.
local notation:max "evalRow" x:max k:max w:max => eval (Sum.elim (Option.elim' k x) w)

/-- Transport inequalities or congruences coordinatewise through a natural polynomial. -/
macro "polynomial_congr" : tactic =>
  `(tactic| focus
    simp [eval_eq]
    -- Resolve coordinate types before splitting their sum and option constructors.
    gcongr <;> exact by
      cases_type* _root_.Sum Option <;> exact?)

/-- Apply the existential, finite-conjunction, and arithmetic Diophantine closure rules. -/
macro "dioph" xs:Lean.Parser.Tactic.SolveByElim.arg,* : tactic =>
  `(tactic| focus
    -- Normalize finite conjunctions into the predicate shape used by the search.
    have finite ι m predicate :=
      @DiophList.forall.{0} ι <| @ofFn _ m predicate
    simp [forall_iff_forall_mem] at finite
    -- A tuple of existential witnesses is represented by a coordinate-indexed function.
    try apply_rules [dsimp% [Equiv.sumArrowEquivProdArrow]
      (@ex_dioph _ _ <|
        setOf <| Function.uncurry · ∘ Equiv.sumArrowEquivProdArrow ..), inter]
    all_goals solve_by_elim (maxDepth := 64) only
      [proj_dioph, const_dioph, add_dioph, mul_dioph, mod_dioph,
        sub_dioph, pow_dioph, modEq_dioph, dvd_dioph,
        factorial_diophFn, binomial_diophFn, $xs,*])

open scoped Vector3

/-- Polynomial evaluation is Diophantine when its arguments are input coordinates. -/
lemma evalRow_diophFn :
    DiophFn.{0} fun v => evalRow (v ∘ y) (v k) (v ∘ w) e := by
  induction e using induction_on <;> exact by
    simp
    repeat' cases_type _root_.Sum Option
    all_goals dioph *

/-! ## Eliminating bounded universal quantifiers -/

/-- Diophantine predicates are closed under an input-coordinate bounded universal quantifier.

The main certificate packs the witnesses for all rows into CRT residues. The scale
is a factorial large enough both to separate the moduli and to recover polynomial
equalities from congruences. A one-coordinate vector holds the encoded row index.
-/
lemma boundedForall_dioph
    (h : Dioph.{0} <| Function.uncurry P ∘ Equiv.piOptionEquivProd) :
    Dioph {v | ∀ i < v boundIndex, P i v} := by
  have ⟨_, e, f, hPolynomial⟩ := exists_fin_polynomial h
  -- e and f are natural-coefficient polynomials representing the predicate.
  -- u bounds each witness coordinate; a stores its CRT encoding; v stores the index.
  have hCertificate {N x} :
      let bound k u := evalRow x k u (e + f) + N
      (∃ u, let T := (bound N u)!
        ∃ a, ∃ v : Vector3 _ 1,
        (∀ i, encodedModuliProduct N T ∣ ∏ t ∈ range (u i + 1), (a i - t)) ∧
        crtModulus T v.head ≡ 0 [MOD encodedModuliProduct N T] ∧
        evalRow x v.head a e ≡ evalRow x v.head a f [MOD encodedModuliProduct N T]) ↔
      ∀ k < N, ∃ w, evalRow x k w e = evalRow x k w f := by
    intro bound
    constructor
    · -- Decode one row of a certificate.
      rintro ⟨u, a, v, hWitness_product, hIndex, hEvaluation⟩ k hk
      let T := (bound N u)!
      have hScale_pos := factorial_pos <| bound N u
      have ⟨p, hp, hpk⟩ := @exists_prime_and_dvd (crtModulus T k) <| by lia
      have hPrime_product := hpk.trans <|
        encodedModuliProduct_eq_prod hScale_pos ▸ dvd_prod_of_mem _ <| Finset.mem_range.mpr hk
      -- A prime divisor of the product divides one falling-factorial factor.
      -- Truncated subtraction requires min(a i, j), not necessarily j itself.
      choose j _ _ using fun i =>
        show ∃ j ≤ u i, _ from
          have ⟨j, _, hpj⟩ :=
            hp.prime.exists_mem_finset_dvd <| hPrime_product.trans <| hWitness_product i
          ⟨min (a i) j, by grind,
            (modEq_sub (min_le_left ..)).of_dvd (Nat.sub_eq_sub_min .. ▸ hpj)⟩
      have hCoprime : p.Coprime T := Nat.Coprime.of_dvd_left hpk (by simp)
      -- A prime coprime to (bound N u)! exceeds both decoded polynomial values.
      have hRow_bound : bound k j < p :=
        lt_of_le_of_lt (by
          unfold bound
          polynomial_congr) <|
          not_le.mp <| hp.dvd_factorial.not.mp <|
            hp.coprime_iff_not_dvd.mp hCoprime
      -- Cancel the common factorial scale to recover the row-index congruence.
      have hIndex_congruence :=
        ModEq.cancel_right_of_coprime hCoprime <|
          ModEq.add_right_cancel' _ <| (hIndex.of_dvd hPrime_product).trans hpk.zero_modEq_nat
      have hPolynomial_congruence g : evalRow x v.head a g ≡ evalRow x k j g [MOD p] := by
        polynomial_congr
      existsi j
      -- Both evaluations are below p, so congruence is actual equality.
      grind [eval_add, ModEq, = Nat.mod_eq_of_lt, hEvaluation.of_dvd hPrime_product]
    · -- Encode a family of row witnesses using the Chinese remainder theorem.
      choose! w hRows
      -- Take the coordinatewise maximum of the witnesses over the finite range.
      let u := sup (range N) w
      existsi u
      intro T
      have hPairwise_coprime : (List.range N).Pairwise (Coprime.onFun <| crtModulus T) :=
        List.pairwise_lt_range.imp_of_mem <| by
          intros
          apply coprime_mul_succ
          apply dvd_factorial <;> grind
      -- Encode the row indices once, then encode each witness coordinate separately.
      have ⟨c, hIndex_residue⟩ := chineseRemainderOfList id _ _ hPairwise_coprime
      have ⟨a, hWitness_residue⟩ :=
        Equiv.subtypePiEquivPi.symm <|
          (chineseRemainderOfList · _ _ hPairwise_coprime) ∘' Function.swap w
      existsi a, [c], fun i => modEq_zero_iff_dvd.mp ?_, ?_ <;>
        erw [encodedModuliProduct_eq_prod (factorial_pos _)] <;>
        apply modEq_list_map_prod_iff hPairwise_coprime |>.2 <;>
        intro k hk
      · exact
          Dvd.dvd.modEq_zero_nat <|
            (dvd_of_mod_eq_zero <| sub_mod_eq_zero_of_mod_eq <| hWitness_residue i _ hk).trans <|
              dvd_prod_of_mem _ <| mem_range_succ_iff.mpr <| Pi.le_def.mp (le_sup hk) i
      · apply ModEq.trans _ dvd_rfl.modEq_zero_nat
        unfold crtModulus
        gcongr
        exact?
      · have hPolynomial_congruence g :
            evalRow x c a g ≡ evalRow x k (w k) g [MOD crtModulus T k] := by
          polynomial_congr
        dsimp [Vector3.head]
        grind [ModEq]
  -- Transfer the certificate to the original predicate and discharge its arithmetic syntax.
  apply ext _ <| by
    intro
    simpa only [← hPolynomial] using! hCertificate
  simp only [← descFactorial_eq_prod_range, descFactorial_eq_factorial_mul_choose]
  dioph evalRow_diophFn

/-! ## Primitive recursion and recursively enumerable sets -/

/-- A primitive recursion can be certified by the entries of one finite encoded trace.

The two coordinates of v are the beta-function parameters: entry i is
`v.head % ((i + 1) * v.tail.head + 1)`.
-/
lemma recursionTrace_iff :
    Nat.rec base step k = out ↔
      ∃ v : Vector3 _ 2,
        let entry := HMod.hMod v.head ∘ crtModulus v.tail.head
        entry 0 = base ∧ entry k = out ∧
        ∀ i < k, entry (i + 1) = step i (entry i) := by
  constructor
  -- Encode the actual trace, including both the initial and final entries.
  have hTrace := beta_unbeta_coe <| ofFn <| Nat.rec base step ∘ @Fin.val k.succ
  simp [Fin.forall_iff, beta, -ofFn_succ] at hTrace
  intro
  existsi [_, _], hTrace _ k.zero_le
  unfold Vector3.head Vector3.tail
  swap
  -- Conversely, the transition equations determine every entry by induction.
  rintro ⟨v, hInitial, rfl, hStep⟩
  induction k
  all_goals
    dsimp
    grind

/-- Every primitive recursive function on a fixed-length vector has a Diophantine graph.

Mathlib's Diophantine composition lemmas use `Fin2` coordinates, whereas
`Nat.Primrec'` uses `List.Vector`; the statement performs that coordinate conversion.
-/
lemma primrec_diophFn (hf : Nat.Primrec' function) :
    DiophFn (function <| List.Vector.ofFn <| · ∘ Fin2.ofFin) := by
  induction hf <;> simp_all [Function.comp_def] <;>
    try dioph *
  · -- Compose the outer graph with all component graphs.
    rename_i ihOuter ihComponents
    simpa using diophFn_comp ihOuter _ <|
      Iff.mpr (vectorAllP_iff_forall ..) <| ihComponents ∘' Fin2.toFin
  · -- Primitive recursion is an existential trace with bounded transition checks.
    rename_i ihBase ihStep
    apply ext _ fun _ => recursionTrace_iff.symm
    -- The base case reads only the original parameters.
    -- A transition reads: its index, the preceding trace entry, and those parameters.
    dioph eq_dioph,
      reindex_diophFn (fun i => Sum.inl (some (Fin2.fs i))) ihBase,
      diophFn_comp ihStep
        ((fun assignment => assignment none) ::
          (fun assignment =>
            assignment (some (Sum.inr Fin2.fz)) %
              crtModulus
                (assignment (some (Sum.inr (Fin2.fs Fin2.fz))))
                (assignment none)) ::
          fun i assignment => assignment (some (Sum.inl (some (Fin2.fs i))))),
      Iff.mpr (vectorAllP_cons ..),
      Iff.mpr (vectorAllP_iff_forall ..), boundedForall_dioph

/-- **MRDP, hard direction:** every recursively enumerable set is Diophantine.

The polynomial and its finite number of witnesses depend only on S, not on n.
Both the input and witness coordinates range over the natural numbers.
-/
theorem mrdp {S : Set ℕ} (hS : REPred S) :
    ∃ k, ∃ P : MvPolynomial (Unit ⊕ Fin k) ℤ,
      ∀ n, n ∈ S ↔ ∃ w,
        P.eval (Int.ofNatHom ∘ Sum.elim (fun _ => n) w) = 0 := by
  -- Choose a program semideciding S. Its bounded evaluator is primitive recursive.
  have ⟨c, hCode⟩ := exists_code.mp hS
  have ⟨_, e, f, hPolynomial⟩ :=
    exists_fin_polynomial <|
      ext
        (ex1_dioph <| reindex_diophFn [none, some _]
          (primrec_diophFn
            (Nat.Primrec'.prim_iff₂.mpr <| _root_.Primrec.encode.comp₂ <|
              primrec_evaln.to₂.comp₂
                (Primrec₂.pair.comp₂ Primrec₂.left <| Primrec₂.const c) Primrec₂.right))
            D= D.1)
        fun v => show _ ↔ S (v Unit.unit) from by
          -- A successful evaluation returns some 0, whose natural encoding is 1.
          symm
          simpa [hCode, ← Encodable.encode_inj, Encodable.encode] using @evaln_complete c _ 0
  -- Move to integer coefficients: equality e = f becomes the single equation e - f = 0.
  existsi _, e.map Int.ofNatHom - f.map Int.ofNatHom
  intro n
  simpa [← eval₂_comp, sub_eq_zero] using! hPolynomial fun _ => n

end MRDP
