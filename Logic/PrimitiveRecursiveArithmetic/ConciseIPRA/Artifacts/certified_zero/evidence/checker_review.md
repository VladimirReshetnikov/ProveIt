# Semantic review of initializer-driven computation dispatch

## Reviewed versions and conclusion

The reviewed files are:

| File | SHA-256 |
|---|---|
| `design/final/checker.py` | `b02aa84a742d24032199246aad0d9968e1875dc4a95b482ca6461a76e3550a68` |
| `design/final/checker_bytes.py` | `5520fce8cf011fb3b91f6d9936d12f53aa73908f8aa139dec06a7d1a609fd8ea` |
| `design/final/checker_joint.py` | `6bde2f96fa87238f1527f9bf8d9845bac20ac3580bc1c6b3229d49c4427a92c4` |

I found no new soundness defect in these changes. The argument is
compositional: it uses the supplied arity calculus's semantic opening,
freshness, zero-completion, and known-zero-instance supply lemmas, and the
new admissibility proof in `seed_normalization.tex`. It is a written
assistant review, not proof-assistant verification or external human peer
review. Finite test success is not the basis for the universal conclusion.

The explicit-list profile is the preferred public checker. The joint profile has
the inherited malformed-string/runtime qualification explained below.
These files retain the inherited parity-based opener; they do not use the
separate, uncompleted boxed-substitution experiment.

## 1. Scope traversal and arithmetic source construction

The preferred opener uses an explicit `isinstance(a, list)` test. On ordinary
JSON values this traverses arrays only. Its depth increment `5-len(a)` is
unchanged from the arity-calculus draft: unary formulas are paired
binders, binary formulas are equations, and ternary formulas are internal
closures. Numerical roots have depth 3; unary numerical terms are
successors and ternary numerical terms are scalar iterators. Surplus
arrays have the constant interpretations specified in that draft.

The inherited argument is semantic opening at meaningful sorted roots.
It must not be replaced by a claim that the opener is raw-idempotent on
all surplus arrays. The existing counterexample to that stronger claim
continues to apply. Preserving the documented constant interpretations
of ignored arrays is also essential.

The predecessor packet constructs its source as
`[s and [s], u, t]`. A truthy `s` therefore supplies an actual unary
successor constructor, regardless of the predecessor's numerical value.
A successful falsy `s` denotes zero. The recursive source is `[s,u,t]`,
and a used state image is still validated at numerical root depth 3.
Neither state validation nor the source constructor was removed by the
new dispatch.

The byte profile replaces only the explicit list test by `a*0 == []`.
For ordinary JSON runtime values this recognizes exactly lists among
successful tests: numbers and booleans give numeric zero, strings give an
empty string, and dictionaries and null raise errors. All rejected
non-list container/string cases also reject under the explicit-list
program's scalar comparison. This preserves the accepted proof language
without using user-supplied Python methods or an additional evaluator.

## 2. Initializer-driven dispatch and completeness

After a falsy major, the initializer `u` now decides between computation
and paired introduction. Thus direct computations with a falsy literal
zero initializer disappear, while introduction puts zero in its unused
`u` field. This is a syntactic restriction. A truthy initializer can still
denote numerical zero, and the checker does not assert its positivity.

The closed term

\[
C=I(S(S0),S0;v.0)
\]

has the direct permitted computation `C=0`: both its predecessor and its
initializer have nonempty encodings. For an excluded computation, replace
the zero initializer and, when necessary, the zero predecessor by one
fresh motive variable. Its instance at `C` is directly permitted, and
transport along `C=0` gives the original instance. The base counter stays
zero. Bound variables and passive update parameters stay fixed. This
proves that every missing computation axiom is admissible and preserves
the exact native end sequent; it does not assume that two raw zero aliases
are automatically interchangeable.

The repair has three native nodes when its closed zero lemma is copied.
It gives the stated finite proof transformation, independently of whether
the delivered producer implements arbitrary native derivations or only
the supplied examples. Both positive and negative scalar aliases remain
subject to the inherited decoder and scope tests.

## 3. New false-major computation packets need zero-instance discharge

Computation is no longer selected specifically by `m is None`. It can
now occur with `m=0`. For an atomic retained goal, that marker can make
the common continuation open the generated hypothesis at the newly
allocated parameter rather than at zero. The generated `H(b)` need not
be a uniformly true arithmetic equation.

The correct argument is the inherited known-zero-instance rule. The
retained goal and context were validated before allocation, so they do
not mention any newly admitted relevant name. The zero-completion lemma
proves `H(0)`; substitute zero for the fresh names in the continuation
proof and cut this computation instance in. This validates the new
packet possibilities without adding any induction principle.

For arbitrary JSON numeric aliases this must be a **simultaneous** zero
substitution. It includes the designated integer parameter and every
negative fractional name in the newly admitted unit interval that occurs
in the finite certificate. Those fractional names are not all the same
parameter. `seed_normalization.tex` has been amended to state this
explicitly, consistently with the arity reference.

## 4. Unified hypothesis assignment and conditional expression

The expression

```python
h = m * 3 if m else computation if u else (a := i(*a, t, 2))
```

is right-associative and therefore means `m*3 if m else (computation if
u else introduction)`. It evaluates only its selected arm. The truthy
major has already been proved and its optional transport performed
before this assignment. The major array itself is not mutated by those
calls, so retesting `m` selects the same export as the former branch-local
assignment. This also preserves the order relative to any global-floor
changes made while proving the major.

In the computation arm the expression leaves the retained goal
unchanged. In the introduction arm it assigns the same opening result
to both `a` and `h`. Thus hoisting the assignment out of the three-way
dispatch preserves its successful behavior and exception behavior.
The exact-arity argument-binding check in `i(*a,t,2)` remains present.
A unary paired formula is opened correctly; a formula with at least two
array children supplies too many arguments and fails. The exceptional
empty goal already denotes truth, as in the inherited proof.

The parity test is applied to the opened introduction matrix, so only
literal equations among meaningful nonconstant formulas can receive
progress introduction. Nonempty initializer packets instead use the
fresh-supply argument in section 3; they are not additional induction
instances.

## 5. Boolean transport in the strict profile

The strict profile writes transport as

```python
a = major_matches and target_matches and i(t, s) or a
```

instead of an `if`. The only potential difference is a matched transport
whose minor opening is false-valued. On every successful opening a
nonempty array preserves its outer arity, so a canonical nonempty
formula cannot have such a minor. For an empty template, both openings
are the empty truth array. For scalar formula padding, both openings are
the same preserved scalar or the zero truth alias; the numerical image
does not affect formula padding. Thus a false-valued minor and a matched
target both denote truth, and retaining the old goal is harmless. Python
zero aliases such as `False` and `0.0` do not alter this conclusion.

Canonical object formulas are nonempty arrays, so their transport
compilation agrees directly with the ordinary conditional version. The
joint profile retains that ordinary conditional version in any event.

## 6. Boolean choice of the fresh opening image

After decreasing `k`, the expression

```python
(m or len(a) % 2 == m) and k
```

returns exactly `k` when the condition holds and returns `False`
otherwise. The former conditional expression returned integer zero in
the latter case. Boolean false is a numerical zero alias in the retained
decoder; it also compares equal to zero in Python's recursive list
comparisons. The condition has the same short-circuit behavior, including
avoiding `len(a)` in the truthy-major case. This change neither enlarges
the meaningful progress class nor changes a canonical numerical image.

## 7. Additional changes in the joint profile

The final joint profile uses the same explicit `k=0`, default missing
image `None`, and separate input-driver assignments as the preferred
profile. The earlier experimental `0j` marker and driver/default
assignment expressions are absent from this reviewed freeze. Importing
`load` directly from `json` retains the same standard parser dependency.

The generic opener tries iteration and falls back to scalar handling on
an exception. If a traversal of a non-scalar container fails, its scalar
ordering comparison also fails; there is no successful conversion of a
failed list traversal into an unchecked scalar. Empty strings and empty
objects can normalize to empty arrays. A dictionary with the sole empty
string key can normalize to a unary array with an empty child; dictionary
values are ignored. These are the additional aliases already discussed
in the arity reference, not arbitrary new operators.

A nonempty string can recurse into itself. On the concrete finite-stack
CPython runtime, recursion and subsequent type errors reject it. On an
ideal unbounded interpreter, opening it can diverge. Therefore the joint
profile is not claimed to be a total recognizer of arbitrary JSON on an
ideal unbounded machine. Its canonical integer-and-array proof language
is structurally well founded. The strict profile avoids this particular
limitation.

## 8. What remains assumed or unformalized

- The complete arity decoder, semantic-opening lemma, generated-supply
  zero-completion argument, and the inherited arithmetic/logical
  bi-interpretation remain written mathematical proofs. This review does
  not constitute a Lean or Rocq formalization of them.
- The proof of canonical completeness is a finite metatheoretic
  transformation. A producer for named regression examples is not a
  verified universal compiler from arbitrary iPRA derivations.
- Canonical completeness does not claim that every raw alias of a
  provable formula has a proof with the same submitted spelling.
- The measured programs depend on the specified Python interpreter and
  standard JSON implementation. Failure is an uncaught exception and
  nonzero exit status; success requires normal return and the final
  `ACCEPT` output. Resource exhaustion can reject large valid proofs.
- Smaller normalized source does not establish an absolute minimum, a
  new arithmetic foundation, or a major mathematical breakthrough.

Subject to those explicit limits, the initializer normalization and the
listed control-flow transformations compose with the inherited checker
proof. Because the native consequence relation is unchanged, the
inherited whole-domain, actual-equality bi-interpretation is preserved;
finite numerical agreement alone would not justify that conclusion.
