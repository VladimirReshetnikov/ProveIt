# Raw ordinary input obstructs universality of the filtered carry family

The [polynomial-input extension](input_bridge_filtered_polynomial_obstruction.md)
also excludes repair by any fixed positive even integer-polynomial
initial-value substitution alone. Additional filters remain outside that theorem.

For the exact filtered paired queue of
[the66/71/74 packet](native_controller_paired_filter71.md), a fixed affine
carry controller that accepts every positive even ordinary input x
necessarily accepts **every** positive ordinary input. This remains true
with any fixed paid block alignment of both time and queue width.

Consequently this source family cannot represent the even positive
integers themselves, or an undecidable computably enumerable set
containing all even positive integers. This is an expressiveness
obstruction for the specified source family. It is not a decision
procedure for every language accepted by an individual controller.
No extra filter or changed input encoding is included.

## 1. The exact family and centered controller

The input interface is precisely two positive Boolean ternary queues
I0,I1 with `I0+I1=2x<W=3^m`. Both terminal queues are zero. All four
append/read words F0,F1,F2,F3 are positive. The local filter is

    a0+a1+d0=1.

The last m steps necessarily read10 and append00, and t>2m. The preceding
packet proves that the fixed general controller

    3c'=c+h+u0*d0+u1*d1+v0*a0+v1*a1

can accept unbounded ordinary inputs only if `2cf=h+u0`. Otherwise its
accepted set is effectively finite. Thus a controller accepting all even
x must satisfy this endpoint condition.

Center the carry by k=c-cf and put

    s=cs-cf, alpha=v0-u0, beta=v1-u0, gamma=u1.

The exact source equation and its local interpretation become

    s+alpha*F0+beta*F1+gamma*F3=0,                     (1)
    3k'=k+alpha*a0+beta*a1+gamma*d1,
    k_initial=s, k_terminal=0.                       (2)

The full integral graph is meant, not a chosen subgraph. This is the
same positive projected family whether represented by the71/74 schedules
or by a proved cheaper source with the identical projection. No new
arithmetic operation or modified kernel is proposed here.

## 2. Three explicit even-input tests force a stationary loader

Put

    G=|alpha|+|beta|+|gamma|,
    C=max(|s|,ceil(G/2)), B=2C+|gamma|.

Equation(2) gives |k|<=C at every step. A raw input trit2 forces
`d0=d1=1`, since the two initial Boolean trits sum without carry, and
the filter then forces `a0=a1=0`. Thus along a run of N raw2s,

    3^N*(2k_end-gamma)=2k_start-gamma.                 (3)

Choose any even N>=2 with3^N>B. The integer right side in(3) has
absolute value strictly smaller than3^N, so an integral path through the
whole block requires it to vanish. Both endpoint carries of that block
are therefore `k*=gamma/2`.

Consider these three ordinary inputs, all positive and even:

| Input | Value of x | Low-first trits of2x |
|---|---:|---|
| A | (3^N-1)/2 | N copies of2 |
| B | 3*(3^N-1)/2 | 0, followed by N copies of2 |
| C | 3^(N+1)-1 | 1, followed by N copies of2, followed by1 |

Every indicated trit is read during the initial queue pass, since
`2x<W`; unknown high zero padding does not alter the blocks. Acceptance
of all even inputs includes acceptance of these three specific inputs.

Input A forces `s=k*=gamma/2`. For input B, the first raw0 has physical
read00, so it appends10 or01. The following long2 block forces the
post-step carry back to k*. Substitution into(2) gives

    alpha=gamma or beta=gamma.                        (4)

For input C, the first raw1 has one of two physical reads. If it is10,
the filter forces append00 and the unchanged carry k* requires k*=0.
If it is01, it appends10 or01; an unchanged carry requires alpha=0 or
beta=0. Consequently

    gamma=0 or alpha=0 or beta=0.                     (5)

These conclusions use actual compatible prefixes of accepted queue
paths. They do not assume that all raw-symbol transitions must be
available at every carry.

## 3. Strict positivity makes the nontrivial cases impossible

Suppose gamma is nonzero. Equations(4)–(5) give
`{alpha,beta}={0,gamma}`, and input A gave `s=gamma/2`.
Every variable term in(1) is an integer multiple of gamma. Dividing(1)
by gamma would therefore give `1/2+integer=0`, which is impossible.
This includes negative gamma. If gamma is odd, the earlier requirement
of an integral k* already supplies a contradiction.

Now suppose gamma=0. Then s=0 and(4) makes at least one of alpha,beta
zero. Because **both F0 and F1 are strictly positive**, equation(1)
forces the other coefficient to vanish too. Thus

    s=alpha=beta=gamma=0.                             (6)

The carry stays0 on every filtered path, and the controller equation
imposes no additional restriction. The three-sweep construction in the
preceding packet supplies a full positive filtered witness for every
positive x. Hence this controller accepts all positive ordinary inputs.

The proof actually uses only the three test inputs for a computable N
depending on the controller constants. Every nontrivial controller
rejects at least one of those explicit even inputs.

## 4. Paid fixed block alignment does not change the conclusion

An aligned controller that accepts all even x still has accepted paths
for the same three test inputs, so Sections2–3 force(6). Conversely, fix
any block length ell>=2. For every positive x choose m divisible by ell
and large enough that W=3^m>6x. The same filtered construction has t=3m
and q=W^3. Thus both m and t are divisible by ell, and the two positive
geometric quotients required by the paid alignment exist. It follows
that a trivial aligned controller also accepts every positive x.

For example, let K be a proper nonrecursive computably enumerable subset
of the nonnegative integers. The set

    {2n:n>=1} union {2n+1:n in K}

is a proper computably enumerable set containing every positive even
integer. It cannot be the accepted set of this filtered raw-input family.
This excludes a universal representation compiler whose only variable
program data are the fixed coefficients and endpoints of this family.

The conclusion does not cover an additional relation on the four words,
a changed initial-value formula, a nonzero terminal queue, or a different
local filter. No general decidability claim for the remaining individual
languages is made. The established complete universal bound remains76.

## 5. Evidence

The [checker](native_controller_paired_raw_obstruction.py) audits the
source normalization against the frozen71/74 packet, computes the three
families exactly, and enumerates all locally possible physical prefixes
for bounded signed controller constants. It also checks positive aligned
three-sweep witnesses using the actual paired FIFO semantics. The
[receipt](native_controller_paired_raw_obstruction.json) records the
bounded domains; the proof of the full statement is parametric.
Independent full proof, source and fresh default-replay review passed.
An additional independent proof read also passed.
