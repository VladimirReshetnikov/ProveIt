# Lowering a power congruence through its quotient

Status: exact ordinary algebraic lemma and source-transformation proposal.
No successor source, compiler run, quartic census or operation count is claimed.
The initial application under investigation is the accepted Round15 source.

## Exact interface over arbitrary integers

Fix integer ports A,n,X,Y,m,r. The power relation used by the signed Pell
encoding is

    X+(n-A)Y-m=(2An-n²-1)r.                 (1)

Introduce a single private integer u and use these two quadratic residuals:

    u-nr=0,
    X-m+r+nY-AY-2Au+nu=0.                 (2)

Then (1) holds if and only if there exists u satisfying (2). The unique
choice is u=nr. Indeed the second residual becomes

    X-m+r+nY-AY-2Anr+n²r
      =X+(n-A)Y-m-(2An-n²-1)r.

This is a polynomial identity. It requires no sign, nonzero modulus,
Pell classification, exponent interpretation or bound. It also holds at
n=0, at A=0 and when the displayed modulus is zero. Thus an early signed
bootstrap does not acquire any new number-theoretic premise from this
change of quadratic presentation.

If the main norm already retains z=AY, its shared coordinate may replace
the term AY in the second residual, giving

    X-m+r+nY-z-2Au+nu=0.                  (3)

The row z-AY=0 must remain with its existing uses. Either (2) or (3) has
degree at most two when the displayed ports are affine expressions in the
source coordinates. In particular a base such as F²+1 must use its already
lowered square coordinate; substituting F itself into that abbreviation
would change the degree and is not licensed by this statement.

## Complete private-graph replacement

One explicit old lowering introduces private coordinates a,b,T,c,d with

    a=2An, b=n², T=a-b-1, c=nY, d=Tr,
    X-AY+c-m-d=0.                         (4)

For fixed ports including r, all five coordinates are uniquely determined.
On its zero set, forget them and set u=nr. Conversely, from (2) reconstruct
all five coordinates by (4); its final residual is zero by the identity.
These are polynomial inverse maps on these private graphs at fixed ports.
If AY uses the shared z, fix z as well and retain z-AY unchanged.

An actual source may share a square, modulus or product across requests,
or use an old auxiliary elsewhere. Such a coordinate is not private merely
because its name occurs in this displayed macro. The actual whole-source
occurrence map must decide which coordinates and rows can be removed.
Shared helpers can be retained, or jointly reconstructed for every request
using them; all external rows and sign predicates must be included in the
proof. The lemma does not imply that five coordinates disappear from an
already projected equation. Its monic projector may already remove some.

The source's quotient r is a fixed port here, rather than an old auxiliary
being set arbitrarily. Replacing this relation must preserve its exact
requested base, output and main Pell pair. In particular the two Round15
requests at K must still use the same pair, and any globally used N² gate
must be retained or separately reconstructed. Existing semantic bounds and
the square frame continue to refer to their original affine ports; the new
private u must not be inserted into that frame.

## Shared moduli require a different comparison

The actual Round15 body has only five modulus-definition rows (221, 236,
241, 256 and 262) for its eighteen requests. Later calls share the moduli
at q and q+1. Giving every request a new u is therefore not automatically
an improvement. The entire shared-helper graph must be compared after
projection, rather than treating each congruence as an isolated macro.

There is also a simpler exact presentation of each shared modulus:

    T-2An+n²+1=0.                          (5)

It is already quadratic for an affine n. Thus the two old gates a=2An
and b=n² need not be separate coordinates if their complete occurrence
maps make them private to the definition. Keep T and replace those three
definition rows by (5); reconstruct a and b by their unique products in
the reverse direction. The old N² coordinate 175, for example, also has
external uses and cannot simply be deleted on this argument. It may be
retained with its definition while (5) replaces only the other private
helper. A monic projector could already perform these eliminations; its
chosen order determines whether explicit fusion changes the final count.

These are alternative local presentations of the same relation. Selecting
between a shared T and a per-quotient u needs actual complete source maps
and measurements; this note assigns neither an operation nor variable gain.

## What remains before an equation claim

A finite packet must identify every affected row and coordinate, prove
the complete occurrence/privacy and shared-helper maps, verify the exact
polynomial identities for the actual affine ports, and give both full-source
witness maps. It must rebind every ordinary sign and Pell proof interface,
including the base-one supporting-pair exception. No sign guard may be
dropped merely because its former target was called an intermediate gate.

Only after that source theorem is accepted should the resulting monic
projection, free-coordinate restoration and integer translations be run.
Every resulting residual and coefficient of the collected sum of squares
needs its complete finite certificate. Neither an improvement nor a global
minimality claim follows from the present local lowering lemma alone.
