# Top-down matching of the fixed C254 templates

`term_patterns.py` replaces the constructor-witness interface with a trusted
pattern matcher. Certificates omit `constructor_ids`, and matching keeps no
constructor-results array. The exact twelve rules, both bundle gates, normalized
zero and fixed falsity endpoint remain. `pattern_codec.py` removes only those
witness fields from the earlier unary codec. This is an executable research
frontend with an ordinary soundness/completeness argument; no compiled TM,
state saving, Lean theorem or internal PA theorem is claimed.

The fixed templates still come from source50's attributed `spec254.json`
(arrival `85633fd2f57b5dca16f87667699134d1b500ebc0`, manuscript pin
`fab89c5d26b81cd2ccab2ee5d213ff23725c7726`). The trusted circuit compiler is
reused to reconstruct a finite pattern DAG. Candidate certificates cannot choose
these templates. The numeric/source50 modules are producer and test references,
not verifier dependencies.

## Matcher and normalization

The arena is unchanged: sole `Z` at ID0, four constructor tags, backward child
references, and no stored `B0(0,0)` alias. Duplicate positive records are allowed.
Their denotation is `value(Bk(l,r))=4*P(value(l),value(r))+k`, for the exact C254
Cantor pairing; only ID0 denotes zero. The verifier never computes denotations,
interns candidate terms, searches for a constructor, or tests global uniqueness.

A trusted pattern DAG has parameter leaves, literal `Z`, and constructor nodes
with backward wires. Matching starts at the claimed formula and walks an
explicit obligation stack. A parameter leaf requires its exact supplied ID;
literal `Z` requires ID0; a constructor requires the expected tag and schedules
its children. Crucially, expected tag0 with actual ID0 is treated as the virtual
`B0(0,0)`, with actual child IDs0,0. Positive expected tags reject zero.
This handles substitutions that collapse a nonliteral implication pattern to
truth: rho8 with all parameters zero is one necessary example. The virtual rule
does not relax parameter-ID equality or literal-zero matching.

Traversal follows the fixed pattern, so parameter leaves stop without examining
their potentially huge denotations. Repeated compound subpatterns can use
separate positive copies. The proof-row formula list remains; only the
constructor-results array and its certificate fields disappear. Truth, MP,
GEN, both distinguishing-path gates and recognition of any exact `B1(0,0)`
falsity copy retain their prior checks.

## Ordinary exact-calculus argument

Induction on the trusted pattern proves matching sound. Parameter-ID equality
gives equal denotation; zero is exact; each actual constructor has the indicated
constructor value of its children. The virtual case uses `B0(0,0)=0` and satisfies
the same induction. Thus matching proves the claimed schema instance, even
where repeated compounds use different IDs. Successful distinguishing paths
prove actual numeric inequalities despite duplicates. Induction on backward
proof-row references, with the unchanged MP/GEN checks, proves derivability of
every accepted conclusion in exact C254. Default acceptance gives `C254 F`.

For existential completeness, use the existing interned normalized producer on
a finite C254 derivation. Each constructor pattern matches by normalization
induction, with the virtual zero case where needed. Every repeated parameter
has the same interned ID, and each genuine inequality has a finite mismatch
path. Erasing the old circuit witnesses supplies an accepted certificate; the
new codec serializes it. Existence of a fixedF certificate is therefore unchanged.
This is an ordinary proof argument, not a formal Lean verification of Python.

Acceptance of every duplicate-containing old encoding is not asserted. An
equal-value parameter copy with a different ID may fail a leaf comparison;
the canonical producer supplies completeness. Conversely repeated compound
copies can match without sharing one old circuit-result ID. Both behaviors are
sound because constructor denotations, rather than record uniqueness, determine
the schema instance.

## Exact codec and observed cost

The binary protocol retains unary naturals, fixed2-bit node tags, fixed4-bit
rule tags, proof references, claimed formula IDs and termination-coded paths.
It removes the fixed-arity constructor-ID lists. On an erasure control, saving
is exactly `sum(id+1)` over those removed unary fields. Node/proof counts remain
bounded by actual remaining bits before record allocation. Truncation, forward
references, unknown tags and leftover bits reject. Resource exceptions propagate.
Fair length-lex enumeration still reaches every finite certificate; a finite
negative search is never interpreted as consistency.

Fresh `test_patterns.py` evidence in `pattern-results.json` includes:

- All12 rule controls and15 exact codec roundtrips; all15 reject at fixedF.
- All261 template assignments over0/1/2 against the original constructor:
  246 valid instances and15 retained bundle-gate failures. There are22 virtual
  zero cases and37 virtual constructor checks in aggregate.
- Duplicate output/compound acceptance; both distinct-ID equal-value gate
  attacks and malformed node/row/MP/GEN/pattern/path controls rejected.
- Fourteen explicit malformed words plus all262,143 words of length at most17:
  every call terminates, all245 successful parses re-encode exactly, and no
  fixedF certificate occurs in that finite domain.
- The genuine deep bundle retains4,159 node validations and2,048 gate edges.
  Its match uses197 visits:98 constructors,47 parameters,52 zero leaves; maximum
  pending stack18. The old shared circuit uses62 constructor checks.
- The small bundle shrinks4,582→2,506 bits (2,076 witness bits removed); the deep
  bundle9,042,403→8,790,471 (251,932 removed). Each omits62 constructor IDs.
- Numeric/producer/compiler/old-verifier APIs can be disabled without changing
  positive controls. Injected `MemoryError` and `RecursionError` inside the
  actual matcher and GEN checker propagate through the codec.

The [maintained replay](../results/term-pattern-verification.json) freshly runs
all four certificate suites and both clean-process codec controls in 15.588
seconds. The [independent review](../results/term-pattern-review.json) found no
unresolved defect. It corrected a stale axiom description in one test; that
control now explicitly duplicates the actual rho1 formula's compound All
subtree and passes the final replay. Verifier and codec behavior were unchanged
by that test correction.

The saved `example-pattern-bundle.json` and `.bits` are positive controls,
not refutations; they support a clean-process hosted-spec replay. Run the
maintained certificate runner to recover source50 outside the checkout and
execute the sequential suites; directly, the test command is:

```sh
uv run --no-project python -B test_patterns.py
```

## Next compiler checkpoint

The remaining generic primitive is indexed `ReadNode(ID)`, together with
prior-proof-formula lookup. Unroll the trusted pattern control and compare a
path-per-check implementation with a depth-first fixed-continuation version.
The Python obligation stack need not become a runtime stack. Compare against
an optimized static-circuit implementation: its wires can also be allocated
statically, so a62-entry runtime values array was never mandatory. Compare the
live wire slots together with parser, candidate, gate and scratch storage under
the actual chosen schedule.

First implement and test a register-level `ReadNode` on an explicitly delimited
finite binary word, preserving the candidate and checking truncation/backward
references. Then charge the whole parser, prior-proof access, both gates,
patterns, fixedF, fair scheduler, reset and blank initializer through an actual
backend. More constructor reads may offset the removed fields. No comparison
with252 states follows from witness-bit savings alone.
