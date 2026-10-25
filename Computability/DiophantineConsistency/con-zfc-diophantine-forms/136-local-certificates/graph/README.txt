UNIT-COEFFICIENT QUARTICS BY LOCAL ALIAS CONTRACTION

Prepared for ProveIt, 24 October 2026, with AI assistance.

This component contains three literal polynomials over unrestricted integers.
Every nonzero coefficient is +1 or -1, every constant term is 1, and every
polynomial has total degree four. The complete equation in each case is P=0.

Profile       Variables  Monomials  Source variables  Graph hubs
matched1252       1252      27738          442            128
principal985       985      95609          306             16
sparse1122        1122      25922          306            128

The matched profile reduces package127's 2215-variable, 30468-term polynomial
on exactly the same 442-variable source. The principal and sparse profiles
also use this report's new 306-variable direct C222 source. The principal has
fewer variables; the sparse profile has substantially fewer monomials. No
global optimality or literature-wide historical-priority claim is made.

For each profile, polynomial.json is the canonical complete coefficient list.
A term [c,[i,j,j]] means c*z_i*z_j^2; [] is the constant monomial. Variable
metadata describes its provenance and introduces no additional unknowns.
polynomial.txt independently exposes every monomial in readable notation.

MATHEMATICAL CONTENT

The inherited graph compiler represents a quadratic residual system by half
the sum of squared graph divergences, with simple equality cycles and a unit
path. A complete source residual list and original graph certificate are
retained for every selected profile.

The new contraction merges only aliases of the same logical source value.
It accepts a contraction precisely when all collected graph-energy
coefficients remain in {-1,0,1}. This uses actual incident edge products and
their exact cancellations, replacing the earlier sufficient global C4-free
restriction. Every equality cycle is reconstructed on the surviving aliases.

When there are two surviving aliases, a third dummy can sometimes be removed
using

  F(a,b)=a^4+b^4-a^3*b-a*b^3=(a-b)^2*(a^2+a*b+b^2).

This polynomial is nonnegative over the reals and vanishes precisely when
a=b. It is used only when complete coefficient collection still gives height
one. The independent checker reconstructs it through

  2F=(a^2-b^2)^2+(a^2-a*b)^2+(a*b-b^2)^2.

The new graph polynomial has an exact bijection of integer zero sets with its
source residual system. Alias and unit guards recover every logical value;
the unchanged free tree flows are uniquely determined by the source values.
The article proves this unbounded statement and composes it with the named
C222/ZF/ZFC calibration to obtain the requested consistency equivalence.
Finite coefficient checks do not establish consistency or replace that proof.

VERIFY AND REBUILD

Python 3.10 or later and its standard library suffice; no network or CAS is
needed. From this component's directory:

  python3 -B verify.py
  python3 -B verify.py --rebuild
  python3 -B -O verify.py --rebuild

Verification imports neither producer. The optional rebuild imports producers
only after independent verification, reconstructs all 18 mathematical JSON
files in memory, and compares their exact canonical bytes with the release.
It does not overwrite any delivered equation or certificate. An optional
--output /absolute/path/receipt.json records the result outside this folder.

For explicit negative controls on the principal profile:

  python3 -B verify_local.py --parent parents/principal985 \
    --artifact principal985 --source sources/source306.json --mutations

The negative controls reject a changed constant, a missing equality class,
a missing unit coordinate, and a cross-class alias identification. Normal and
optimized-Python receipts are retained. REBUILD_VERIFICATION*.json records
byte-identical reconstruction of all selected equations and certificates.

EVALUATE AND LIFT

Supply a JSON array of exactly 985 integers to evaluate the principal equation:

  python3 -B evaluate.py point.json --profile principal985

For a 306-coordinate point of the source system, use --lift:

  python3 -B evaluate.py source_point.json --profile principal985 --lift \
    --output lifted_point.json

This produces the canonical graph witness map L(x) and checks the exact energy
identity

  2 P(L(x)) = sum_i R_i(x)^2 + (sum_i R_i(x))^2.

The formula holds for arbitrary source inputs, not only zeros. LIFT_CHECKS.json
records nine finite transcription controls, not a sampled proof of the
identity. The inverse on zeros reads any surviving alias for each original
source coordinate; all aliases of a logical class are forced equal. These are
evaluators and witness maps, not procedures for deciding whether a zero exists.

CONTENTS AND PROVENANCE

- matched1252/, principal985/, sparse1122/: literal final polynomials, merger
  maps, equality guards, metrics, readable equations and verification receipts.
- parents/: original graph polynomials and their full graph certificates.
- sources/: the complete 442- and 306-variable quadratic residual systems.
- inherited/: unchanged package127 graph constructor, C4-free compressor,
  independent verifier, original proof and notices.
- optimize_aliases.py: deterministic new contraction and quartic-guard builder.
- verify_local.py: separate complete coefficient and correspondence checker.
- verify.py: integrated verification and byte-identical reconstruction.
- evaluate.py: exact evaluation and canonical source-witness lifting.
- PROFILES.json and SOURCE_PINS.json: full source identities and build choices.
- HUB_COMPARISON.json: a finite exploratory comparison; no global minimum.

The inherited graph source is pinned to ProveIt commit
1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61. The new306 source is pinned by its
literal SHA256 identity and its derivation in the enclosing report. Preserve
the inherited license and notices. New code follows the enclosing report's
MIT No Attribution license. Independent review here means separate checks
within an AI-assisted workflow, not external human or formal-kernel approval.
