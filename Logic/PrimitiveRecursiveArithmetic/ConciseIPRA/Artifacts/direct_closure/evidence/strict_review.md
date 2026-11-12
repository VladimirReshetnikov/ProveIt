# Independent review of the strict native checkers and translations

## Verdict

I found no soundness defect in the reviewed strict checkers or the two proof
translations. The implementations match the stated native rules, including
context retention, the literal-equation restriction on progression, and
the eigenvariable conditions represented by de Bruijn scope.

This is an invariant-level source review plus finite regression evidence,
not a machine-checked universal correctness theorem for Python. The Lean
migration remains separately labeled uncompiled.

The controlled same-style implementation saving is supported: the complete
new checker is smaller than the complete old checker in normalized source
bytes, significant tokens, and AST nodes. This is **not** a result below the
repository's 529-byte checker frontier. The normalized gzip size increases.

## Exact reviewed sources

The source hashes recorded by the audit tests are:

| File | SHA-256 |
| --- | --- |
| `strict_old.py` | `4a3811374119363cadfc54d5b87e9332df55272d837f4dade0260b3ba196ebf0` |
| `strict_q.py` | `793cc66da356e2586b66ef21d8f2ac1928503b96cf8bd49a280049f6c8962851` |
| `translate.py` | `e2066dbc76fa2406c8073f34966d00505aa65917fa1e827bedbf66ec9f1da2da` |

The files are under `output/ipra_direct_closure_2026-11-10/code/`. The review
also inspected `tests/verify.py` and its existing validation receipt. No
checker or translator source was modified during the review.

## 1. Strict syntax and the input boundary

`validate` checks the exact list shape, sort, arity, and scope of each term
or formula. The term variable index must be an actual Python `int`, not a
Boolean or floating-point value, and must lie between zero and the current
scope minus one. The declared signature gives one extra bound variable only
to an iterator update, one to Q, and two to D. Seeds and counters do not
acquire the update's local state variable.

The proof rule branches unpack their precise argument arity. Unsupported
rule tags fall through to an exception. Malformed shapes, absent document
fields, or bad argument counts fail before the command-line driver prints
`ACCEPT`. The use of `require` rather than assertions preserves those checks
under `python -O`.

The checker validates the supplied context and advertised goal before
checking the derivation. It consequently certifies a sequent with the stated
context and numerical parameters. An empty context is required when that
sequent is described as an assumption-free theorem. Unused additional JSON
fields have no semantic effect.

## 2. Capture-avoiding substitution invariant

Let a term or formula be scoped over a finite list of numerical variables.
If `images` maps every free variable to a well-scoped term in a target
scope, `substitute(expression, images)` is the usual simultaneous
capture-avoiding substitution.

The critical helper is `lift(images, bound)`. It preserves the newly bound
indices below `bound`. A free index is first reduced by `bound`, mapped by
`images`, and then its image is shifted by `bound`. This is the standard
lifting equation, and it works uniformly beneath nested iterator, Q, and D
binders. `shift` recursively shifts only free variables because substitution
lifts its map again at each nested binder.

The three specialized maps are correct:

- `instantiate` replaces index zero by the supplied term and decrements
  every higher free index, removing one variable from the scope.
- `successor_instance` replaces index zero by its successor and preserves
  every higher index, keeping the scope unchanged.
- `witness_instance` preserves the induction coordinate at index zero,
  replaces the existential coordinate at index one by the shifted witness,
  and decrements every higher index. Thus a D matrix scoped over `n+2`
  variables becomes a Q-style matrix over `n+1` variables. The witness's
  parameters remain outside the induction variable.

All substitutions use the binder counts in the signature. Neither an
iterator's seed nor its counter is mistakenly treated as containing its
state binder.

## 3. Rule-by-rule scope review

Hypothesis, computation, transport, and QE have their literal stated types.
The successor computation instantiates the update with the recursive call,
including when the update has another iterator inside it. The recursive
call is a term at the outer scope, so its state binder cannot capture an
update variable when inserted.

Transport validates its formula template at scope `n+1`, verifies an actual
equality premise, and checks the other premise against the template's left
instance. Its conclusion is exactly the right instance. QE similarly
checks the zero instance before producing the requested instance.

### D elimination

A D matrix has indices `y=0`, `x=1`. In the elimination branch, the formerly
bound witness becomes the fresh external variable at index zero. The local
Q binder then protects y, so the stored matrix can be reused unchanged as
the body of that Q. The retained context is shifted by one, and the branch
must prove `shift(conclusion)`. This last equality is essential: merely
checking the unshifted conclusion would allow the fresh witness to escape
into the position of an old parameter.

### D case introduction

The witness is checked at scope n, so it cannot depend on the subsequently
introduced case variable. After its instantiation, the local assumption is
the shifted zero instance. The successor target uses the fresh variable at
index zero. The fixed parameters are unchanged, and the old context is
shifted by one. This is precisely the case rule.

### Old and new progression

The old checker validates a literal equation matrix over `n+2` variables,
validates its witness at scope n, and obtains the progression equation with
`witness_instance`. The new checker validates that equation directly at
scope `n+1`. Both place the equation itself in the fresh-variable context
and require its successor instance. The respective returned conclusions are
D and Q, exactly as specified.

In particular, neither checker permits progression on Q or D formulas.
The new checker has not accidentally introduced full-formula induction.

These observations establish the usual derivation invariant by induction
on the checked proof tree: in a validated context at scope n, every
successful `derive` call returns a well-scoped formula derivable by the
corresponding mathematical calculus. The supplied advertised goal is then
checked for exact equality with that returned formula.

## 4. Proof-translation review

`translate.py` is correctly treated as an untrusted producer. Its output
must be checked by the destination standalone program. The fact that it
imports helper functions from `strict_q` does not add those producer
functions to either standalone checker's trust boundary.

`map_proof` implements two independent operations together: numerical
substitution and embedding an old hypothesis list into a new one. Under a
local proof branch it lifts the numerical map by one, preserves the newly
introduced hypothesis at index zero, and maps each older hypothesis through
the outer embedding before adding one. This is the required transformation
under all of DE, D-case, old D-progress, and new Q-progress.

In old-to-Q translation, the old instantiated equation is used as the new
Q matrix. The new Q proof is then moved under D-case's fresh numerical
variable and its new base assumption. The numerical map `i -> i+1` and the
hypothesis map `i -> i+1` are therefore both necessary; they play distinct
roles. QE at the fresh successor and the new base hypothesis finish the
case branch.

In Q-to-old translation, the matrix gains an unused existential variable at
index one. Existing indices greater than zero are incremented, while the
induction index zero is preserved. Old D progression with witness zero then
has exactly the original progression premise. DE returns its local Q
hypothesis. The required branch goal equals that local hypothesis because
shifting the original Q formula introduces precisely the same unused
variable.

The translations recurse on every premise. They neither duplicate nor
discard an original progression premise. The node-count implementation
agrees with the mathematical transformations: +3 nodes per old progression
and +2 per new progression, including nested progression occurrences.

## 5. Concrete coverage gap in the initial tests

The initial `progress_with_context` comment says it tests a retained
hypothesis whose index changes inside a translated proof. Its proof only
uses `['hyp', 0]`, which is the induction hypothesis. The retained outer
hypothesis is never used. Thus that example does not establish its stated
retained-hypothesis coverage, even though it is a valid positive test.

The existing transport-beneath-binders case is also useful, but it has no
progression node; the proof translator copies it rather than applying
`map_proof`. It therefore does not exercise the most delicate interaction
between translating progression and nested binders.

These were test-coverage findings, not defects in the checker or producer.

## 6. Targeted additional checks

The independent audit script is `analysis/logic/review_strict.py`. Its
receipt is `strict_review_checks.json`, and it writes its source,
translated, and round-trip certificates under `review_certificates/`.
The five added source proofs cover:

1. Old D progression that actually uses a retained equality hypothesis,
   with a nonvacuous parameterized iterator witness and two nested iterator
   binders in the matrix.
2. The corresponding direct-Q progression proof with the same retained
   equality and nested binders.
3. Old progression whose premise performs DE on a retained D hypothesis,
   using both the fresh Q hypothesis and the independently shifted
   induction hypothesis inside that branch.
4. The corresponding Q progression proof.
5. Old progression containing another progression beneath DE and transport.

Every source proof, translated proof, and round-trip proof passed its
appropriate standalone checker. There were 10 destination/round-trip
checks and 30 command-line runs across normal and optimized Python modes.
The advertised goals and contexts remained exactly unchanged, and all
translation node-count formulas held.

Two negative controls were also checked:

- Replacing the actually used retained-hypothesis reference with the
  induction-hypothesis reference invalidates the nested-iterator proof.
- A gated existential major supplies a fresh witness x=0. Its DE branch
  validly proves x=0, but the advertised conclusion says that an unrelated
  retained parameter a equals zero. Both standalone checkers reject this
  escape. The major and the branch were separately checked as valid, so
  rejection is specifically due to the required shifted conclusion.

The latter is a substantive eigenvariable control: dropping the shift
would incorrectly certify a=0 for an arbitrary parameter a.

## 7. Complexity interpretation

The reported normalized measurements are:

| Complete standalone implementation | Tokens | AST nodes | Bytes | gzip-9 bytes |
| --- | ---: | ---: | ---: | ---: |
| Matched old rules | 1,187 | 1,358 | 5,199 | 1,303 |
| Direct Q rules | 1,169 | 1,337 | 5,116 | 1,322 |
| Difference | -18 | -21 | -83 | +19 |

The two programs share the same explicit validator, substitution engine,
context machinery, JSON input, and verdict driver. Their rule-specific
source difference corresponds to removal of the progression witness and
its instantiation. The measurements therefore support a controlled
simplification of a straightforward implementation.

They do not show that 5,116 bytes is below the repository's compact
529-byte implementation, nor that this calculus has an optimal checker.
The larger gzip result must remain visible as the user's requested
informational coordinate.
