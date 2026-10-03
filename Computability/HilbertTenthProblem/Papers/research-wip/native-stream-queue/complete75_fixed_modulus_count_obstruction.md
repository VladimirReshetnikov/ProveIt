# A fixed-modulus count cannot replace the complete75 input bridge

A literal transfer of the sparse compiler's three-gate input-count relation
to the fixed cell radix of complete75 cannot give a universal construction.
Under the explicit port guard below, every fixed-program positive-input
language is ultimately periodic. In particular it cannot represent the
powers of two. This rules out the stated replacement, not counting methods
in general or every possible replacement of the input bridge.

The [checker](complete75_fixed_modulus_count_obstruction.py) audits the exact
positive translation on guarded hypothetical remainders of both the
[complete75 certificate](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md) and the
[normalized87 polynomial](complete75_normalized_strong87.md). Neither frozen
source is changed. Its [receipt](complete75_fixed_modulus_count_obstruction.json)
contains selected complete hypothetical sources and the finite audits.
No new operation bound or full positive Pell zero is asserted.

## 1. The exact fixed-port hypothesis

Fix positive integers a,m,c. The varying ordinary input x and existential
coordinates alpha,t are strictly positive integers. Other strictly positive
existential coordinates are collected in z. Suppose every constraint and
output depends on x,alpha,t only through the two expressions

    U=alpha+a*x,                 V=m*(t-1)+c*x.             (1)

The rest of the finite arithmetic source may be arbitrary. It may compute
word extractions, enforce local or unbounded chronological constraints,
use the two ports repeatedly, and use any fixed program numerals. It must
not read x,alpha,t or an intermediate partial value of(1) separately.
In particular m is fixed on a program slice, not a varying witness or a
function of x. There must be no additional input-bound condition outside
these ports.

The ordinary count relation is L=V, where L is a supplied word or any
permitted computed history expression. This is only one instance of the
hypothesis: the argument does not assume that L has been correctly typed
as a selector. It therefore survives additional x-independent constraints
that do perform that typing, provided they obey the same port guard.

The current complete75 raw bound is C+alpha+2d*x=q, so a=2d. In its
normalized87 descendant the computed field is

    C=q-F-Z-alpha-2d*x=q-F-Z-U.

After removing the four original input comparisons, or the normalized
input-norm factor and its private computation, these remainders depend
on x and alpha only through U. Reassociating the two additions or
subtractions to expose U is an exact all-integer arithmetic identity.
Attaching a new count port V then meets(1) if no other input connection
is introduced. Keeping the original input norm would violate this guard;
the theorem makes no claim against the established75/87 constructions.

## 2. An exact positive downward translation

Put P=m/gcd(m,c), so cP/m is a positive integer. For an integer k>=1 and
x-kP>0, keep z unchanged and set

    x'=x-kP,
    alpha'=alpha+a*kP,
    t'=t+(cP/m)*k.                                      (2)

Every new existential coordinate remains strictly positive. Directly,

    alpha'+a*x'=alpha+a*x,
    m*(t'-1)+c*x'=m*(t-1)+c*x.                           (3)

Thus both ports agree exactly. Topological induction through the complete
remaining source proves that every body register, comparison residual and
output polynomial has the same value. The private partial products used
to construct(1) can change; their separate use is precisely what the guard
forbids. Equation(3) is an all-integer identity, while positivity in(2)
is an unconditional implication on the stated positive domain.

Consequently, if any guarded source accepts x, it also accepts every
positive x-kP. This conclusion holds regardless of the finalizer or the
validity of a proposed semantic interpretation of the remaining source.
It does not presume that a finite arithmetic fixture is a complete zero.

## 3. Ultimately periodic slices, and an explicit language obstruction

For each residue representative r in{1,...,P}, consider accepted inputs
r+Pj, j>=0. Downward closure says that their j-indices form an initial
segment of the nonnegative integers. Such a segment is empty, finite,
or all nonnegative integers. There are only P residue classes. Beyond
the largest endpoint among the finite segments, acceptance therefore
depends only on the residue modulo P. Every fixed-program language is
ultimately periodic.

This is an existence statement about the threshold for each slice. It
provides no uniform algorithm extracting that threshold from an arbitrary
existential arithmetic source; no such algorithm is used or claimed.

A direct obstruction does not even need the threshold argument. If the
source represented precisely the positive powers of two, choose a power
2^h>2P. It must accept2^h and hence2^h-P. But

    2^(h-1)<2^h-P<2^h,

so the latter is not a power of two. This decidable, hence recursively
enumerable, language already contradicts universality for every possible
fixed positive P. Increasing the fixed radix for each program does not
avoid the argument, since this single language defeats every fixed P.

## 4. Why the paid sparse prefix is different

The [sparse674 universal compiler](residue_affine_sparse_universal.md)
uses L=(B-1)(t-1)+x inside an already paid chronological history. Here B
is a varying history radix. Its paid height forces0<x<B-1, and a typed
prefix whose payload grows by doubling forces its length ell<B-1. The
congruence ell=x modulo B-1 therefore recovers equality exactly.

In complete75 the per-cell B=2^d is a fixed compiler numeral. The variable
q=B^N is the size of the entire cyclic word, not a freely interchangeable
per-row radix. There is no valid fixed restriction x<B-1 for all ordinary
positive inputs. The first sparse translation x'=x-(B-1) is blocked by
its paid positive range, whereas it is allowed for the fixed-port source
whenever x>B-1. Merely calling q the count modulus would not constitute
a proof that the same selector word reduces to its number of marked cells
modulo q-1. Any new variable-radix encoding and all its typing, range and
chronological conditions would have to be supplied separately.

For a simple illustration, if L=1+B+...+B^(ell-1) and ell>B-1, its count
equation accepts both x=ell and x'=ell-(B-1): increase t by1. These are
exact selector/count components, not alleged full75 solutions. The
source-level argument above is stronger because it transfers every
remaining constraint simultaneously under the guard.

## 5. Literal guards and finite evidence

The checker inlines only fixed compiler numerals, reconstructs the two
ports, and permits no use of their private coordinates or partial values
in the remaining body or exported metadata. It checks topological closure
and that every emitted gate is an ancestor of a checked comparison or
output. Its fixed-modulus and period assertions reject witness-dependent,
zero or negative moduli. Period metadata and translation steps must be
positive integers; numerically equal floating-point values are rejected.
All other coordinates are unchanged by(2).

The75 host retains its first fifteen comparisons, dropping exactly the
four input comparisons. The87 host retains its seven noninput factors.
The emitted test hosts attach the count comparison and exercise both
sum-of-squares and anchored finalizers. Word-port fixtures use a supplied
word and several retained fields; these fields are not asserted to be
actual typed loader selectors. An eventual implementation extracting a
selector has the same obstruction if it meets the complete guard.

The author writer and fresh replay audit192 guarded host sources:
1536 complete output/residual/body identities, including768 signed
assignments and768 positive witness translations. Seventeen malformed contracts
are rejected. There are60 explicit fixed-radix selector aliases and256
powers-of-two obstruction fixtures. Two symbolic identities establish(3)
without sampling. The receipt also records the unchanged parent source
hashes and four selected hypothetical source schedules.

```sh
python3 complete75_fixed_modulus_count_obstruction.py
```

These fixtures corroborate the algebra and guard implementation. They are
not full positive Pell witnesses or a new representation theorem. The
established75/87 bounds and the refutation of the distinct weakened86
proposal are unchanged.

Independent native proof/source review and fresh replay passed, including
the final strict integer-type guard. Its separate literal executor and
manual translation checked384 complete body/residual/output identities,
192 signed, across96 additional host contexts. Gibbs's independent full
proof/source review and fresh replay also passed after that guard fix:
512 complete identities (256 signed and256 positive),1008 minimal-period
checks,294 finite downward-residue languages and14 additional guard
rejections. Both reviewers confirmed all five local links. Root's full
proof/source review and fresh replay also passed, including complete
guarded-port closure and the strict integer-period correction. No review
findings remain.
