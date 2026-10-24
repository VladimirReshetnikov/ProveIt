# Exact integer projection, with every sign condition retained

All rings in Sections 1–3 are the ordinary integers. No premise about
Pell equations, CRT witnesses, proof checking, or coordinate signs is used
in a projection step.

## 1. One signed monic step

Let the current integer coordinates be `(v,z)`. Suppose an actual current
residual is exactly `v-f(z)` or its negative, where `f` is an integer
polynomial independent of `v`. Keep every other row after the pointwise
substitution `v := f(z)`, and remove the defining row. A row whose
substitution is the zero polynomial may also be removed.

Projection of a full zero to `z` gives a zero of the substituted system:
the defining row forces `v=f(z)`, so every substituted residual equals
the corresponding old residual. Conversely a zero `z` of the new system
has the **unique** extension `v=f(z)`. The defining residual vanishes by
construction, every kept old row vanishes by substitution, and every
dropped zero row vanishes identically. These two maps are inverse on
zero sets. Negative coefficients in `f` pose no integrality problem.

Each materialized certificate supplies the actual row identifier,
coordinate and complete polynomial `f`. The independent replayer checks
the monic identity up to sign in the integer polynomial ring, checks
that `f` contains no self/deleted coordinate, and substitutes it into
**every** remaining row. It requires every resulting row to remain of
degree at most two. Neither a variable's `kind` nor the optimizer's
heuristic ordering is a premise of this argument.

## 2. A complete ordered certificate

Apply Section 1 successively in the recorded order. After the last step,
the surviving coordinates are renamed in increasing original-index
order. Reverse the list of restorations to recover each deleted
coordinate as an integer polynomial in coordinates already recovered.
Thus the composition is again a zero-set bijection.

An optimizer may in general omit a surviving coordinate not used in any
row; that would preserve zero *existence*, but would lose injectivity.
Here every one of the 18 measured runs has
`unconstrained_removed = []`. The checker explicitly rejects otherwise.
Every original coordinate is either retained or uniquely restored.
All complete child coordinate lists are live.

The certificate replayer starts with the entire parent residual array.
It has no separate fast path which omits sign guards. A guard is either
retained after its complete substitution, removed only as an exact zero
polynomial, or used as one of the monic defining rows whose truth is
ensured by reverse restoration. This accounts for every original guard.
It is unnecessary, and would generally be false, to assume every
unrestricted child coordinate is nonnegative before restoration.

The child equation omits the parent's original-index `seed_guards`
metadata; those indices would be stale after renaming. The unchanged
parent packet and certificate retain all needed guard identities.

## 3. From the single quartic to the full integer row system

For every parent and child, the specified single equation is

```
Q(x) = sum_j r_j(x)^2 = 0.
```

An integer square is nonnegative. Therefore `Q(x)=0` if and only if each
listed integer residual vanishes. Exact symbolic SOS expansion gives
the supplied collected `expanded_polynomial.json`, including every
coefficient. Each residual has degree at most two, so the total degree
is at most four. A nonzero collected degree-four monomial, recorded in
`CHECK.json`, proves exact degree four. There is no possible appeal to
numerical sampling in this degree conclusion.

Combining Sections 1–3 gives a polynomial bijection of integer zero
sets between each new single quartic and its frozen integer parent.

## 4. The restored natural-domain certificate

Each integer parent consists of an unchanged natural residual prefix
and 234 explicit seed guards. For a seed `x`, a guard is

```
x = a^2 + b^2 + c^2 + c.
```

For every integer `c`, `c(c+1)>=0`, so the guard forces `x>=0`.
Conversely every natural `x` has this representation: by the
three-square theorem `4x+1`, which is 1 or 5 modulo eight, is a sum of
three integer squares. Exactly one coordinate is odd modulo four;
write the squares after reordering as `(2a)^2,(2b)^2,(2c+1)^2` and
cancel/divide by four. This includes `x=0`.

Every next sign-certificate step uses an actual vanished prefix row,
possibly multiplied by minus one, of the form

```
c*x = P(z),       c>0,
```

where `x` is absent from `P`, every coefficient of `P` is nonnegative,
and each coordinate with an odd exponent in a monomial of `P` is
already known nonnegative. Even powers need no sign premise. Thus
`P(z)>=0`, then `x>=0`. Induction through the finite ordered certificate
proves every prefix coordinate nonnegative, on an arbitrary integer
zero of the restored full system. The independent checker reconstructs
all these conditions from the actual coefficient rows and earlier
conclusions. No natural correctness theorem or coordinate-kind
annotation is used to bootstrap the signs.

Now projecting away only the fresh guard auxiliaries gives a zero of
the literal natural parent. Conversely a natural zero extends to an
integer-parent zero by choosing the three guard witnesses separately.
This extension is an existence equivalence; it is not a unique-lift
claim. The projection of Sections 1–3 is bijective only between the new
integer zero sets and their full integer parents.

## 5. Scope and reproducibility

The generator uses the signed monic optimizer from the authenticated
batched arrival. Its independent replayer is a separate source module
which does not import that optimizer. The present checker additionally
authenticates each frozen integer parent, the original synchronized
natural archive member, its complete prefix and fresh seed guards,
then replays the entire sign derivation and complete SOS expansion.
All original sources and parent packets are copied and hash pinned.
The 18 fixed heuristic configurations are a reproducible finite search,
not a claim of smallest possible integer quartic or minimal guard count.

For each of seven materialized points, three signed off-source
assignments are restored and checked against **every** original
residual. The checker also rejects a changed restoration coefficient
and a missing output row even after updating that child's hash. These
are transcription/implementation controls in addition to the unbounded
polynomial proof in Sections 1–4.

The accepted ordinary synchronized parent proof can be composed with
this exact arithmetic equivalence without changing its source,
constants, power hypotheses or native interface. This does not establish
that the equation has no zero, does not establish Con(ZFC), and does
not supply the still-required encoded object-ZFC derivation. No Lean
source or process is involved in this candidate.
