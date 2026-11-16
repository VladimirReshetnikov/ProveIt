# FIBER-iPRA Lean formalization plan

Baseline: `VladimirReshetnikov/ProveIt` commit
`58627ed89814ba122e1f0f012f1aba103cda267b`.

Target namespace: `LeanProofs.IPRA.FIBER`.

Formal acceptance criterion: every public mathematical endpoint has literal
Lean type `Prf PRAAx Γ φ` (notation `Γ ⊢[PRAAx] φ`), compiles in the repository,
contains no placeholder, and passes `#print axioms`.

## Phase 0 - structural kernel

1. Place `Kernel.lean` under
   `Derivations/Lean/IPRADerivations/FIBER/Kernel.lean`.
2. Adjust only import paths or elaboration details required by the current API.
3. Build it independently.
4. Add examples of `discharge`, `specialize`, and `seal` with a nonempty
   context and a nontrivial substitution.
5. Run `#print axioms`.

This phase should be nearly immediate: all proofs are aliases of checked
`Prf` operations and `IPRA.inst`.

## Phase 1 - Boolean atoms and folds

Create:

- `Bool.lean`: bit operations and object proofs that outputs are 0 or 1;
- `Fold.lean`: primitive-recursive `anyBit` and `allBit`;
- indexing and extension lemmas at arbitrary terms;
- soundness/completeness of the folds against finite bounded formulas.

Critical proof discipline: the induction predicate must be a QF state equation.
Do not induct on a formula containing a bounded quantifier.  For `allBit`, prove
an indexing lemma saying that `allBit N = 1` and `i < N` imply `p i = 1`.
For the converse, use a QF induction on `allBit k = 1` under the universal
hypothesis.

## Phase 2 - fixed bounded formula reflection

Implement the metalevel datatype `BFm` and:

```lean
def BFm.toFm : BFm n → Fm PTm n
def BFm.bit  : BFm n → PTm n
def BFm.reflect (A : BFm n) :
  ([] : List (Fm PTm n)) ⊢[PRAAx] (A.bit ≐ PTm.num 1 🡘 A.toFm)
```

The recursion is external Lean recursion.  There is no object-level universal
truth predicate.  The bounded-quantifier cases call the fold theorems from
Phase 1.

Add reflection tests containing nested bounded quantifiers and parameters under
binders.

## Phase 3 - least accepted certificate and sequence coding

Create a one-success adapter over `IPRADerivations.Core.Search` by searching for
zero of the complement bit.  Reuse exact declarations:

- `Search.mu`;
- `Search.search_spec`;
- `Search.search_found`;
- `Search.search_minimal`.

Prove acceptedness, bound, and minimality at arbitrary terms.

Choose one canonical sequence representation, preferably built from the checked
pairing/projection and simultaneous recursion library.  Prove append/lookup and
concatenation equations in `Prf PRAAx`.  Mixed-radix encoding may be added as an
optimization later.

## Phase 4 - master certificates

First prove a fixed three-query theorem.  Then prove the general bounded-family
version:

```text
(∀ i < N, ∃ c < B(i), V(i,c)=1)
  -> ∃ C, ∀ i < N,
       lookup(C,i) < B(i) ∧ V(i,lookup(C,i))=1.
```

Internally define the `i`th witness by least accepted search and construct the
sequence by primitive recursion.  The construction is finite bounded choice,
not an additional axiom.

## Phase 5 - demand closure

Start with two coordinates.  Define capped componentwise maximum, iteration,
and potential.  Prove:

1. iteration is increasing;
2. a nonfixed update strictly increases the potential;
3. potential is bounded by the sum of caps;
4. stabilization by the sum of caps;
5. minimality below every prefixed point.

Generalize to fixed `r`, then to an encoded finite vector only after the
fixed-arity proof is stable.

## Phase 6 - bounded strategies

Implement depth-one `∀∃` first, then a metalevel fixed quantifier-pattern
syntax.  A verifier checks all leaves.  The realization proof recursively uses
`allI`, `allE`, `exI`, reflected table lookup, and leaf reflection.

Do not claim extraction from arbitrary unbounded classical proofs.

## Phase 7 - interface and compiler records

Separate host metadata from object proof fields.  A well-formed node must carry
its local `Prf PRAAx` contract.  Define the compiler by recursion over an
acyclic schedule.  Cyclic source graphs must first be specialized through the
finite demand closure and unrolled.

The compiler result should include:

- demand term;
- master-certificate bound and verifier;
- output transformer and observation;
- exact residual formula list;
- final `Prf PRAAx` proof.

Scope checking must reject a local certificate that appears in the public
formula unless it is marked canonical and introduced by proved least search,
or is hidden behind an invariant observation relation.

## Phase 8 - cross-domain checked examples

### Dyadic coherence

Use the existing integer-difference and powers libraries.  Prove the exact
cleared-denominator estimate

```text
|2^(m-n) a(n) - a(m)| <= 2^(m-n) - 1
```

from adjacent bounds `|2a(k)-a(k+1)| <= 1`, by QF induction on `m-n`.

### Finite-net lifting

Encode a finite list of net points, a coverage verifier, a modulus, and finite
pointwise proofs.  Open the local covering witness by `Prf.exE` and ensure it
does not escape.

### Cluster observation

For a small fixed polynomial degree, verify two cluster certificates and prove
agreement of a symmetric observation.  Add gap-guarded labeling as a separate
corollary.

## Phase 9 - bridge and audit

For every public module:

```sh
lake build +IPRADerivations.FIBER.<Module>
```

Then:

- scan for `sorry`, `admit`, and new `axiom` declarations;
- run `#print axioms` on public endpoints;
- transfer one theorem through `pra_iff_native`;
- transport one open sequent through `IPRABridge` and back;
- record toolchain, commit, command, elapsed time, and peak memory.

## First reviewable pull request

The recommended first PR contains only:

1. compiled `Kernel.lean`;
2. one-success search adapter;
3. fixed two-query master certificate;
4. two-coordinate demand closure;
5. dyadic adjacent-motion theorem;
6. checks and axiom audit.

It should not yet include a generic JSON frontend or a large application.
