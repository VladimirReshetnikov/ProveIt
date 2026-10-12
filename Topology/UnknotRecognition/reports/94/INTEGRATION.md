# Integration contract

## Keep the arithmetic checker separate from source geometry

`prepare(packet)` checks complete *supplied* interval data, validity of the matching,
cover duplication and critical-cell counts. It cannot prove that an omitted cover
was not present in the source. `verify_modular(prepared, proof)` checks every encoded
arrow without expanding it. Neither function accepts or returns an assertion that
the packet is the genuine cellulation of a manifold.

The geometric theorem applies only after a different source checker has established:

1. Binding to the intended source manifold and selected cut piece.
2. A complete regular PL cellulation, with cell charts sufficient for valid free-facet
   collapses, and compact PL 3-manifold status.
3. Exact agreement between that cellulation and every family and cover in the packet.

The generic verifier CLI intentionally reports `source_geometry_authenticated: false`
and `ball_or_knot_verdict: null`, even when a rank verifies and the critical vector is
`[1,0,0,0]`.

## Native exporter not supplied

The maintained `normal_cut_cell_complex` and `verify_normal_cut_cell_complex` use
`normal-cut-cells-v1`. That is not the format of this package. Raw source cells may
have self-identifications and attaching occurrences that cancel as matrix entries.
Never convert such a packet by retaining only nonzero boundary coefficients.

A future exporter must supply source-faithful regularization, a proof that its
family count and integer lengths stay controlled, and independent replay. A generic
claim that barycentric subdivision exists is not an encoded-size theorem. The
source-specific modular-path-times-disk constructors are not a substitute exporter.

## Suggested wrapper outcome types

- `INVALID_CERTIFICATE`: malformed matching or failed arithmetic replay.
- `UNKNOWN`: no certificate found within the chosen template/search budget.
- `CERTIFIED_BALL`: only after independent source authentication plus valid rank and
  one critical vertex. Return the original source/piece identity with this result.

A failed template, or even a directed cycle in one proposed matching, does not imply
that the manifold is a nonball. Do not emit `KNOTTED` or `UNKNOT` from this API.

## Preserve the original boundary pattern

The certificate establishes that the original source is a ball. It does not
replace its boundary by the final Morse vertex. Retain the original authenticated
boundary and its pattern for a separate terminal-pattern check. A relative product
collapse onto a base is a homotopy/PL-collapse certificate, not automatically a
boundary-pattern homeomorphism suitable for handle cancellation.

## Staged implementation plan

First integrate the arithmetic kernel behind its own tests, without changing default
recognition. Next develop an exporter/replayer on actual native pieces, including
self-identifications and nonballs. Add component-local moduli using the article's
composition proposition. Finally benchmark total source export, discovery, replay,
pattern checks and fallback on real knot-derived inputs. The known simple product
family must not be used as the only deployment corpus.

## Certificate transport

`reflect` is a supported exact coordinate relabelling. If an old family coordinate
is `i = rho*j + s`, transport multipliers and phases by `a' = a*rho`, `c' = a*s+c`;
keep the offset. This transports arithmetic, not a topological fibre orientation.

The current JSON format supports one common modulus per proof. The article's
strongly-connected-component composition theorem is not implemented by this format.
