# Lean formalization plan for finite-query normal form

## Target environment

- Repository: `VladimirReshetnikov/ProveIt`
- Audited branch/commit: `main` at `31784f0710fa04ccd8ee863ce9bad91fb1d8cf88`
- Lean toolchain: `leanprover/lean4:v4.32.0`
- Intended library: `IPRADerivations`
- Intended namespace: `LeanProofs.IPRA.FQNF`
- Suggested repository directory:
  `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/FQNF/`

The files in `lean/FQNF/` are source-oriented. `KernelCore.lean` contains only
structural proof constructors and no placeholder. The remaining files expose
`sorry` only at the exact arithmetic milestones listed below. Lean was not
available in the artifact runtime, so even `KernelCore.lean` is not claimed to
have elaborated here.

## Existing checked APIs to reuse

The implementation should import, not reprove, the following repository work.

1. `ConciseIPRA.Deduction`
   - `Prf.substWeaken`, `Prf.subst`, `Prf.weaken`
   - `Prf.trans` (simultaneous cut)
   - natural-deduction and equality constructors
2. `ConciseIPRA.PR`
   - syntax `PR`, `PTm`, `PRAAx`
   - defining equations and `PRA.qfInd`
3. `IPRADerivations.Core.Basic`
   - arithmetic terms, `inst`, `ind`, congruence
4. `IPRADerivations.Core.Definitions`
   - `PTm.toPR`, `recDef`, finite sums/products, `powF`
5. `IPRADerivations.Core.Pairing`
   - `eqb`, pairing and projections, simultaneous recursion
6. `IPRADerivations.Core.Division`
   - `quo`, `rem`, `div_mod`, `div_mod_unique`
7. `IPRADerivations.Core.Search`
   - `Search.mu`, `search_spec`, `search_found`, `search_minimal`
8. `IPRADerivations.Core.BoundedSums` and `Core.MultiSums`
   - bounded folds and reflection of bounded universal claims
9. `docs/proofs/foundations/ipra_local_global/lean/ObjectIteration.lean`
   - `primitiveRecursionInvariant`, `primitiveRecursionAt`
10. `docs/proofs/algebra/ipra_stable_observables/lean/ObjectObservation.lean`
    - checked certificate/stability combinators

The last two files should eventually be moved or rederived in the checked
`IPRADerivations` library so that FQNF does not depend on material under
`docs/proofs`.

## Phase 0: structural core (one file)

File: `FQNF/KernelCore.lean`.

1. Add the file to the `IPRADerivations` source tree.
2. Replace ASCII names only if the repository style requires it.
3. Run:

   ```bash
   lake env lean Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/FQNF/KernelCore.lean
   ```

4. Fix only elaboration details; the proofs are direct applications of
   `Prf.trans`, `PRA.qfInd`, and implication introduction/elimination.
5. Add `#print axioms` checks for:
   - `compileLocal`
   - `compileAndExtend`
   - `ReflectedChecker.soundAt`
   - `loopProduces`
   - `stableOfIndependent`

Expected result: no `sorryAx`; only the ordinary metatheoretic Lean axioms
already accepted by the repository audit.

## Phase 1: fixed checker reflection

Create `FQNF/BoolReflection.lean`.

### Definitions

```lean
def IsBool (t : PTm n) : Fm PTm n := (t ≐ zero) ⋎ (t ≐ one)

def BNot (a : PTm n) : PTm n := monus one a
def BAnd (a b : PTm n) : PTm n := a * b
def BOr  (a b : PTm n) : PTm n := monus one (BNot a * BNot b)
```

Use existing `eqb` for equality tests. Prove, in `Prf PRAAx`, truth tables and
Boolean closure. Then define `ReflectedChecker` constructors for:

- equality of terms;
- conjunction and disjunction;
- implication on Boolean predicates;
- bounded universal fold (product of checks);
- bounded existential fold (sum/sign or least search).

### Key theorem

For every fixed bounded formula compiler `compile : BFm k -> PTm k`, prove:

```lean
([] : List (Fm PTm k)) ⊢[PRAAx]
  ((compile A ≐ one) ⟶ denote A)
```

and the converse. This is a structural induction on bounded formula syntax.
Quantifiers are bounded folds, so the object proof uses the already checked
bounded-sum/product lemmas rather than an unbounded truth predicate.

## Phase 2: digit and mixed-radix coding

File: `FQNF/Digits.lean`.

### 2.1 Definitions

Keep the supplied definitions:

```lean
def place  (b i) := ap2 powF i b
def digitT (z i b) := rem (quo z (place b i)) b
```

Define the array encoder as a specialized bounded sum:

```text
encode(a,L,x,b) = sum_{i<L} a(i,x) * b^i.
```

For mixed radix, define recursively:

```text
M(0)=1,
M(i+1)=M(i)*r(i),
pack(L)=sum_{i<L} a(i)*M(i),
get(c,i)=rem (quo c M(i)) r(i).
```

All symbols are primitive recursive by `recDef`, `sumF`, and `prodF`.

### 2.2 Arithmetic lemma order

1. `pow_pos`: `1 <= b -> 0 < b^i`.
2. `lower_sum_lt_place`: if every `a(j)<b`, then
   `sum_{j<i} a(j)b^j < b^i`.
3. `encode_split`: for `i<L`,

   ```text
   encode(L) = lower(i) + b^i*a(i) + b^(i+1)*upper(i).
   ```

4. Use `div_mod_unique` twice:
   - quotient by `b^i` is `a(i)+b*upper(i)`;
   - remainder of that quotient modulo `b` is `a(i)`.
5. Prove `digit_encodeArray`.
6. Prove the mixed-radix analog by replacing powers with prefix products.
7. Prove the global bounds `encode < b^L` and `pack < product r(i)`.

Every induction formula is an equality/inequality assembled from repository QF
predicates, hence admissible for `PRA.qfInd`.

### 2.3 Why mixed radix matters

A master certificate can pack components with different query-dependent bounds
without padding all components to the maximum bound. Its object proof is the
same division-with-remainder argument, and the total bound is the product of
component bounds.

## Phase 3: least certificate selection

File: `FQNF/CertificateSearch.lean`.

### 3.1 Normalize the checker convention

The repository search finds a zero. FQNF verifiers return one. Define:

```lean
failure(c,q) = 1 monus check(c,q).
```

Prove under `IsBool(check(c,q))`:

```text
check(c,q)=1  <->  failure(c,q)=0.
```

### 3.2 Explicit witness theorem

Instantiate `Search.search_found` with `failureBody check`. From

```text
w < B(q), check(w,q)=1
```

derive

```text
sel(q) < B(q), check(sel(q),q)=1, sel(q) <= w.
```

No new induction is required: all search induction is already checked in
`Core/Search.lean`.

### 3.3 Existential producer theorem

Use `Prf.exE` on

```text
exists w. w < B(q) and check(w,q)=1.
```

Inside the witness context invoke the explicit-witness theorem. The selected
term contains only `q`, so the conclusion shifts correctly and the witness is
discharged. This is the exact intuitionistic replacement for hidden finite
choice.

## Phase 4: whole-path certificates

File: `FQNF/PathCode.lean`.

1. Define `state(c,t)=digit(c,t,base(q))`.
2. Define a Boolean path checker as the conjunction of:
   - state range at every time;
   - start check;
   - each adjacent edge check;
   - terminal check.
3. Compile the bounded conjunction to a QF checker equation.
4. Prove checker reflection from local reflection lemmas.
5. Apply Phase 3 to select the least complete path code.

Two adapters should be offered:

- **whole-code search**, requiring only existence of a complete finite path;
- **stepwise trace**, when local seriality gives a least next state, proved by
  `primitiveRecursionAt`.

The first may be exponentially expensive, but it is the robust normal form and
requires no viability table. The second is an optimization justified by the
same interface.

## Phase 5: high-level package compiler

File: `FQNF/Query.lean`.

After the exact formula substitutions are stabilized, prove `Package.compile`:

1. specialize `producer` at the query;
2. apply the precondition;
3. invoke `select_of_exists`;
4. specialize `extractor` at selected code and query;
5. eliminate implication.

Add a conditional compiler in which a boundary formula is an explicit premise.
This is the adapter for height bounds, analytic constants, covering
representatives, compactness moduli, and separation data that are not produced
by the reusable kernel.

## Phase 6: finite names and stable observables

File: `FQNF/Names.lean`.

1. Implement signed integers and rationals using existing difference and
   division infrastructure.
2. Define interval-code validity: ordered endpoints, width bound, and the
   theorem-specific enclosure predicate.
3. Prove cross-certificate midpoint stability.
4. Reuse `stableOfIndependent` (or import the checked
   `ObjectObservation.lean`) to erase representative choice.
5. Build addition, multiplication, inverse-under-apartness, composition, finite
   sums, and integration adapters with explicit demand transformers.
6. Prove exact-label recovery only under a supplied gap formula.

## Phase 7: domain adapters

Implement adapters in this order, because each exercises a distinct part of
the generic layer.

1. **Finite combinatorics:** paths, finite colorings, certificates.
2. **Polynomial algebra:** coefficient arrays, matrices, determinant identities.
3. **Root clusters:** interval/disc certificates and symmetric observations.
4. **Analysis:** rational interval names with explicit moduli.
5. **Topology:** finite complexes and carrier maps.
6. **Algebraic geometry:** ideal-membership and localization witnesses.
7. **Diophantine geometry:** height-bound-to-complete-list compiler.

For each adapter, the terminal declaration must literally have type

```lean
([] : List (Fm PTm 0)) ⊢[PRAAx] phi
```

before any transfer through `pra_iff_native` is claimed.

## Completion and audit checklist

- [ ] `lake build IPRADerivations`
- [ ] no `sorry`, `admit`, `axiom`, or `opaque` in finished modules
- [ ] `Checks/Axioms.lean` includes every public FQNF theorem
- [ ] all producer bounds are terms, not metatheoretic cardinalities
- [ ] every checker is specialized fixed `PR` syntax; no universal evaluator
- [ ] every induction invariant is syntactically QF
- [ ] exact branch claims carry an explicit gap premise
- [ ] quotient outputs are either witnessed or proved stable
- [ ] README distinguishes checked derivations, semantic tests, and plans
- [ ] proof packets cite the exact FQNF package fields they instantiate
