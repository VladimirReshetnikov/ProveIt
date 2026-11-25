import IPRADerivations.Foundations.FiniteSetExponential
import IPRADerivations.Foundations.FilteredEnumeration
import IPRADerivations.Core.CommonLemmas

/-!
# The mixed-radix enumeration of a coordinate grid (`ipra_presentations_to_witnesses`, `thm:module-enumeration`)

Packet: `foundations/ipra_presentations_to_witnesses`, theorem `thm:module-enumeration`, proof:
"Now enumerate all integer tuples `(z_1, …, z_r)` with `-R_k ≤ z_k ≤ R_k` ... and retain exactly
those tuples for which each `F_ℓ` evaluates to zero. Every retained tuple is a common zero by
the retention test. Every common zero is visited by the grid bound and retained, proving
completeness. Distinct integer tuples give distinct rational tuples ... To implement the
Cartesian product with uniform arity, put `B_k = 2 R_k + 1` and `B = ∏_k B_k`. For each
`0 ≤ n < B`, recover its mixed-radix digits `d_k < B_k` by successive remainder and quotient
operations, and set `z_k = d_k - R_k`." The theorem "examines at most `∏_{k=1}^r (2 R_k + 1)`
candidate tuples".

The arity `r` is a parameter of the Lean statements (each instance is one iPRA derivation); the
radices `B_k` and the digits are arbitrary terms.

* `prodT B`, `code B d`, `dig B n`: the product `∏_k B_k`, the code of a digit tuple, and the
  digits of a code, by successive remainder and quotient;
* `code_lt`: digits `d_k < B_k` give a code below `∏_k B_k`: at most `∏_k B_k` candidates;
* `dig_congr`, `dig_code`, `dig_lt`, `code_dig`: `dig` and `code` are mutually inverse between
  the digit tuples with `d_k < B_k` and the codes below `∏_k B_k` (radices positive);
* `code_inj`: distinct digit tuples have distinct codes;
* `digit_pos`, `digit_neg`, `pos_recover`, `neg_recover`: a signed coordinate with `|z| ≤ R`
  is the digit `R + |z|` or `R ∸ |z|` below `2 R + 1`, and `|z|` is recovered from it;
* `grid_complete`: for any retention test `K(n, y)`, a retained tuple with `d_k < B_k` occurs
  in the list `j ↦ sel K j (∏ B) y` of `Foundations/FilteredEnumeration`, at the index
  `rank K (code B d) y`; soundness and the absence of repetitions are `sel_spec` there.

With `Foundations/EigenvalueGrid` (each coordinate of a common zero satisfies `|z_k| ≤ R_k`)
this is the enumeration of the theorem. Not derived: the evaluation of the polynomials `F_ℓ` at
a decoded rational tuple as a program on coefficient codes (the test `K` is a parameter), and
the certificate checker.
-/

namespace LeanProofs.IPRA.Foundations.MixedRadixGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.FiniteSetExponential
  (pair_lt pair_fst pair_snd pair_eta snd_lt fst_lt)
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel sel_rank rank_lt_size)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- `∏_k B_k`. -/
def prodT : {r : ℕ} → (Fin r → PTm k) → PTm k
  | 0, _ => one
  | _ + 1, B => prodT (fun i => B i.succ) * B 0

/-- The mixed-radix code of a digit tuple: `code(d) = code(d_1, …) B_0 + d_0`. -/
def code : {r : ℕ} → (Fin r → PTm k) → (Fin r → PTm k) → PTm k
  | 0, _, _ => zero
  | _ + 1, B, d => code (fun i => B i.succ) (fun i => d i.succ) * B 0 + d 0

/-- The mixed-radix digits of a code, by successive remainder and quotient. -/
def dig : {r : ℕ} → (Fin r → PTm k) → PTm k → Fin r → PTm k
  | 0, _, _ => fun i => i.elim0
  | _ + 1, B, n => Fin.cases (rem n (B 0)) (dig (fun i => B i.succ) (quo n (B 0)))

/-- Digits below the radices give a code below the product: the number of candidates. -/
theorem code_lt : {r : ℕ} → {B d : Fin r → PTm k} → (∀ i, Γ ⊢[PRAAx] lt (d i) (B i)) →
    (Γ ⊢[PRAAx] lt (code B d) (prodT B))
  | 0, _, _, _ => le_refl _
  | _ + 1, _, _, h => pair_lt (code_lt fun i => h i.succ) (h 0)

/-- The digits depend only on the value of the code. -/
theorem dig_congr : {r : ℕ} → (B : Fin r → PTm k) → {n n' : PTm k} → (Γ ⊢[PRAAx] n ≐ n') →
    ∀ i, Γ ⊢[PRAAx] dig B n i ≐ dig B n' i
  | 0, _, _, _, _, i => i.elim0
  | _ + 1, B, _, _, h, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrAp2 remF h (.eqRefl _)
    · exact dig_congr (fun i => B i.succ) (congrAp2 quoF h (.eqRefl _)) j

/-- Decoding a code returns the digits. -/
theorem dig_code : {r : ℕ} → {B d : Fin r → PTm k} →
    (∀ i, Γ ⊢[PRAAx] B i ≐ succ (pred (B i))) → (∀ i, Γ ⊢[PRAAx] lt (d i) (B i)) →
    ∀ i, Γ ⊢[PRAAx] dig B (code B d) i ≐ d i
  | 0, _, _, _, _, i => i.elim0
  | _ + 1, B, d, hB, h, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact pair_snd (hB 0) (h 0)
    · exact (dig_congr (fun i => B i.succ) (pair_fst (hB 0) (h 0)) j).eqTrans
        (dig_code (fun i => hB i.succ) (fun i => h i.succ) j)

/-- Every digit of a code is below its radix. -/
theorem dig_lt : {r : ℕ} → {B : Fin r → PTm k} → (∀ i, Γ ⊢[PRAAx] B i ≐ succ (pred (B i))) →
    (n : PTm k) → ∀ i, Γ ⊢[PRAAx] lt (dig B n i) (B i)
  | 0, _, _, _, i => i.elim0
  | _ + 1, B, hB, n, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact snd_lt (hB 0) n
    · exact dig_lt (fun i => hB i.succ) (quo n (B 0)) j

/-- Encoding the digits of a code below the product returns the code. -/
theorem code_dig : {r : ℕ} → {B : Fin r → PTm k} → (∀ i, Γ ⊢[PRAAx] B i ≐ succ (pred (B i))) →
    {n : PTm k} → (Γ ⊢[PRAAx] lt n (prodT B)) → (Γ ⊢[PRAAx] code B (dig B n) ≐ n)
  | 0, _, _, n, h =>
    ((monus_zero n).eqSymm.eqTrans ((succ_monus_succ n zero).eqSymm.eqTrans h)).eqSymm
  | _ + 1, _, hB, n, h =>
    (congrAdd (congrMul (code_dig (fun i => hB i.succ) (fst_lt (hB 0) h)) (.eqRefl _))
      (.eqRefl _)).eqTrans (pair_eta (hB 0) n).eqSymm

/-- "Distinct integer tuples give distinct" codes. -/
theorem code_inj {r : ℕ} {B d d' : Fin r → PTm k}
    (hB : ∀ i, Γ ⊢[PRAAx] B i ≐ succ (pred (B i))) (h : ∀ i, Γ ⊢[PRAAx] lt (d i) (B i))
    (h' : ∀ i, Γ ⊢[PRAAx] lt (d' i) (B i)) (e : Γ ⊢[PRAAx] code B d ≐ code B d') (i : Fin r) :
    Γ ⊢[PRAAx] d i ≐ d' i :=
  (dig_code hB h i).eqSymm.eqTrans ((dig_congr B e i).eqTrans (dig_code hB h' i))

/-! ## Signed coordinates as digits below `2R + 1` -/

/-- A nonnegative coordinate `z = Z ≤ R` is the digit `R + Z < 2R + 1`. -/
theorem digit_pos {Z R : PTm k} (h : Γ ⊢[PRAAx] le Z R) :
    Γ ⊢[PRAAx] lt (R + Z) (succ (R + R)) :=
  (succ_monus_succ _ _).eqTrans (add_le_add₂ (le_refl R) h)

/-- A negative coordinate `z = -Z`, `Z ≤ R`, is the digit `R ∸ Z < 2R + 1`. -/
theorem digit_neg {Z R : PTm k} (h : Γ ⊢[PRAAx] le Z R) :
    Γ ⊢[PRAAx] lt (monus R Z) (succ (R + R)) :=
  (succ_monus_succ _ _).eqTrans
    (le_trans (le_of_eq_add (d := Z) ((eq_add_of_le h).eqTrans (add_comm _ _)))
      (le_add_right R R))

/-- The absolute value is recovered from the digit of a nonnegative coordinate. -/
theorem pos_recover (Z R : PTm k) : Γ ⊢[PRAAx] monus (R + Z) R ≐ Z := add_monus' Z R

/-- The absolute value is recovered from the digit of a negative coordinate. -/
alias neg_recover := Common.monus_monus_of_le

/-! ## The list of retained tuples -/

/-- Completeness of the grid enumeration: a retained digit tuple is listed, at the index given
by the rank of its code. -/
theorem grid_complete (K : PTm 2) {r : ℕ} {B d : Fin r → PTm k} {y : PTm k}
    (h : ∀ i, Γ ⊢[PRAAx] lt (d i) (B i))
    (hk : Γ ⊢[PRAAx] neg (inst2 K (code B d) y ≐ zero)) :
    Γ ⊢[PRAAx] lt (rank K (code B d) y) (rank K (prodT B) y) ⋏
      (sel K (rank K (code B d) y) (prodT B) y ≐ code B d) :=
  .andI (rank_lt_size K (code_lt h) hk) (sel_rank K (code_lt h) hk)

end LeanProofs.IPRA.Foundations.MixedRadixGrid
