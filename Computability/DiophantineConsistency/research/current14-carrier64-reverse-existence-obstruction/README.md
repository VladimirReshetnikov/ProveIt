# Reverse-existence boundary for the 64-operation transport proposal

The independently reviewed symbolic construction in
[`../current14-carrier64-current-full-zero/`](../current14-carrier64-current-full-zero/README.md)
provides a **positive zero of the 64-operation candidate at the actual 2011
ports**. It specifies the extremely large witness symbolically; the finite
receipt does not evaluate it in full, and its unbounded mathematical proof
is essential. The separate
[review](../../reviews/current14-carrier64-current-full-zero-independent/README.md)
checks that construction externally. Neither packet produces a zero of the
original displayed 65-operation polynomial.

This existing witness exposes an exact logical boundary. Let `Old(x)` mean
that all fourteen coordinates are positive integers and the literal
[`2011 65-row graph`](../../candidates/one-page-padding-staircase-carrier65-2011/polynomial.json)
vanishes at `x`; let `New(y)` mean the analogous statement for the pinned
[`64-row candidate`](../current14-carrier64-transport-proposal/graph.json),
with exactly the same four fixed 2011 ports. Then, in ordinary external
mathematics,

```
(forall y, New(y) -> exists x, Old(x))  iff  (exists x, Old(x)).
```

For the forward implication, apply the proposed reverse map to the already
constructed `New` witness. For the reverse implication, ignore `y` and use the
assumed `Old` witness. The logical inference is intuitionistically valid; the
reviewed witness's mathematical construction is inherited evidence, not a
new formal proof here. In particular, an arbitrary-witness reverse repair is
not merely a question of finding a better reparameterization: **its existence
is equivalent to the unresolved existence of an old zero**. The existing
candidate zero has negative directly recovered alpha, and the cited review
rules out repair with the same q, rank and w; it does not rule out every
possible change of witnesses.

The candidate uses C in place of alpha, with `C=q-F-alpha` and
`gap=q*(q-F)-C`; after that substitution the candidate value equals the old
value. The forward existence map has its own positive-C sign argument, as
recorded in the proposal. The check here confirms the exact graph rows and
pins the existing proof and review; it does not re-prove the sign argument or
the enormous symbolic construction.

## Formal status and limits

The separately checked [current14 native endpoint](../current14-mf-base-only-endpoint-attempt02/README.md)
asserts, as an outer Lean existence statement, that the specified encoded
iPRA theory derives an equivalence between its `noZeroAt` sentence and the
negation of a mapped native ZFC-refutation predicate. The
[translated endpoint](../current14-mf-translated-endpoint/README.md)
has a corresponding encoded derivability statement involving a
Gödel–Gentzen translation. Neither endpoint proves either side, and the
documented recipe-to-print comparison is not a formal parser of the PDF.

This note does not derive ZFC inconsistency, prove that the original equation
does or does not have a zero, prove an iPRA reverse map, or supply a new
soundness/reflection argument. In particular, an internal assertion of
refutability must not be conflated with an independently exhibited actual
finite ZFC contradiction. The two endpoint statements and their provider and
rendering qualifications remain exactly as documented in their own packets.

Under intuitionistic logic an equivalence of the *two no-zero propositions*
alone yields only double negation of old-zero existence from the candidate
zero; the reverse-witness map displayed above gives old-zero existence
directly. Classical logic removes that distinction, but no classical
reflection or consistency conclusion is needed for the stated obstruction.

Run the read-only source and graph pin check from the DiophantineConsistency
directory:

```
python3 -I -S -B research/current14-carrier64-reverse-existence-obstruction/check.py
```

It checks source hashes and literal row differences, not Lean elaboration,
the symbolic witness's full arithmetic, or any current PDF bytes. No Lean,
build or staging operation was performed.
