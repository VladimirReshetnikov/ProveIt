# Explicit object-iPRA formalization obligations

Target repository: `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA`.
Kernel: `Prf PRAAx` and the checked `pra_iff_native` theorem documented in
`ConciseIPRA/README.md`. Native Lean `Nat` proofs do not imply object proofs.

1. Implement PR symbols for list coding, bounded boolean AND/OR, `max`,
   bounded evaluation and filtering. Supply defining equations in `PR` syntax.
2. Express the frontier certificate as ONE equation `Valid p = 1`. Its fields
   include the closure `T p s i ≤ S p` and rank decrease for all bounded nodes.
3. Define `I p r` as ONE quantifier-free equation: a bounded conjunction over
   all `s ≤ S p` of `(rank p s ≤ r → P p s)`, Booleanized.
4. Construct actual derivations `Prf PRAAx (Valid p = 1 -> I p 0)` and
   `Prf PRAAx (Valid p = 1 -> (I p r -> I p (r+1)))` using conditional
   equation rewrites. Apply the QF induction axiom (with p free), specialize
   to `R p`, and eliminate the bounded conjunction.
5. Define the enumeration `E p j`, `N p`, `B p`, `h p x`, `W p x`, the scan
   with PR recurrences, plus a **proved** coverage bound for the particular
   mathematical representation. Do NOT infer it from a cardinality bound.
6. Prove exact rational triangle and Lipschitz bounds on integer cross
   products; reify their bounded arithmetic operations and prove equation
   induction in `Prf PRAAx`.
7. Test proof terms with the repository Lake workspace, and audit relevant
   Lean theorem dependencies. No general lifting of host `Nat` theorems is
   admitted as an axiom.

Status: paper contains detailed human proofs of the conditional principles;
this Lean file is a native finite seed, not a completed `Prf PRAAx` library.
