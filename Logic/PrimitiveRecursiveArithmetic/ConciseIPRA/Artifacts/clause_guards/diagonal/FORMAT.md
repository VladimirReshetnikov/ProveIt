# Exact primary certificate format

The checker reads one JSON object with exactly `goal` and `proof`. The decoded
goal must be a closed formula and the finite proof tree must derive exactly it.
Duplicate textual JSON keys follow Python's ordinary last-key decoding semantics.
Acceptance means exit status zero and exactly `ACCEPT` followed by one newline.
Invalid input produces `REJECT` and a nonzero exit status. Ordinary Python memory
and recursion limits can reject sufficiently large valid finite certificates.

## Numerical terms and formulas

At a local proof scope of size `k`:

- `0` is zero.
- Negative integers `-1,...,-k` are rigid free parameters.
- Positive integers `1,...,d` are locally bound indices at binder depth `d`.
- `[0,t]` is successor `S(t)`.
- `[n,a,h]` is the raw initialized iterator `I(n,a;u.h)`. Only its body `h`
  binds an additional variable, represented by index 1.
- `[s,t]` in a formula position is equality.
- `[B]` in a formula position is `D_(x,y) B`; the matrix binds two variables:
  `y` is index 1 and `x` is index 2.

The expected sort distinguishes successor terms from equality formulas.
Booleans, floats, strings, null, dictionaries and arbitrary list arities are
not numerical terms. Positive free indices, out-of-scope negative labels,
and malformed successors are rejected. Numerical and formula syntax is
validated where introduced; the inference invariant preserves those sorts
for derived formulas. There is no normalization: `I(0,a;h)` remains a term.

Opening removes one binder. It replaces its index by an in-scope term,
decrements indices referring beyond the removed binder, and protects all
indices bound inside iterators or D. Inserted terms have no free positive
indices, so insertion beneath nested binders cannot capture them. Rigid
negative parameters retain their identity.

## Clauses

A context contains reusable pairs `(A,B)`, representing `A -> forall v B(v)`.
`A` has no additional free bound index; `B` has one additional bound variable.
An ordinary hypothesis `H` is stored as `(0=0,H)`, with the binder unused.
The public verifier starts with no clauses. Clause formation happens only
in the introduction and elimination instructions below.

## Five instruction patterns

1. `['r', t]`: reflexivity, returning `t=t` after validating `t`.
2. `['v', p, q]`: evaluation, where `p` proves `s=t` and `q` proves `b=r`.
   If `b=I(0,a;h)`, require `s=a` and return `r=t`. If
   `b=I(S(c),a;h)`, require `s=I(c,a;h)` and return `r=h[t/u]`.
   No other counter or source shape is accepted.
3. `['u', j, t, p]`: use retained clause `(A,B)` at index `j`. Require a
   valid nonnegative index and a valid in-scope target term `t`; require
   `p` to derive exactly `A`; return `B(t)`.
4. `['e', G, p, q]`: paired elimination. Require `G` in the current scope
   and `p` deriving `D_(x,y) B`. Introduce fresh rigid parameter `b=-k-1`.
   Check `q` deriving `G` with the additional clause `(B(b,0),B(b,y))`.
   Return `G`. Validating `G` before allocating `b` enforces non-escape.
5. `['i', G, t, q]`: paired introduction. Require `G=D_(x,y) B` and an
   in-scope witness `t`. Let `z=-k-1`. Set `eta=z` exactly if the original
   uninstantiated matrix is the literal shape
   `I(y,y;u.h)=I(y,y;u.l)`; otherwise set `eta=0`. Check `q` deriving
   `B(t,S(z))` with the additional ordinary hypothesis `B(t,eta)`.
   Return `G`. The witness and the conclusion cannot contain the fresh `z`.

Every instruction checks its exact tag and number of fields. No separate
hypothesis, Q, computation-axiom, transport-template, weakening, cut, or
substitution instruction is trusted. Reuse of a retained clause is explicit
through its index. The evaluation instruction has two computational cases;
its five-pattern count must not be described as five case-free clauses.

## Native comparison format

The native control additionally permits `['q',B]` as a formula with one bound
variable. It has `['h',j]` for a retained formula and
`['q',t,p,q]` for Q elimination. Paired elimination retains Q itself; introduction
retains an ordinary formula. The arithmetic instructions and diagonal guard
are unchanged. The control corresponds to the repository's `SPrf` interface.

## Scope of executable translation

`proof_tools.translate` checks a closed primary certificate, translates its
proof, and checks the native output. End formulas are literally identical.
It records whether each retained clause came from an ordinary hypothesis or a
D elimination; those are exactly the origins possible at the public interface.
It is not an executable translation of arbitrary externally supplied generalized
clause contexts, and it is not a general native-to-clause compiler. The written
proof supplies the general formula translation and both round trips.
