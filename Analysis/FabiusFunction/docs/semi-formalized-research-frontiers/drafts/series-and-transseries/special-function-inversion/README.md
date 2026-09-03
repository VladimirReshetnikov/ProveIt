# Special-function inversion at infinity

Three independently written articles that invert a rapidly growing special
function at infinity to all orders, filed here on 2026-09-03 as a quick-gate
intake.  They arrived as ZIP archives in commit `5a453e1dc` and were unpacked,
filed, and the archives deleted in the intake commit recorded in
[`../../MANIFEST.md`](../../MANIFEST.md).

They share a method rather than a function.  In each, the map to be inverted
has a dominant *power–logarithmic* phase, so ordinary series reversion does not
apply; the first step is to invert that phase exactly with the Lambert
`W`-function, and the remaining Stirling-type corrections then generate a finer
grid of transseries blocks above that core.  Each article also extracts a
general reversion calculus from its worked case.

This is why they are filed apart from
[`../lambert-inverse-transseries/`](../lambert-inverse-transseries/), whose
three articles all invert the single map `x + W(x)`: the subgroups share the
Lambert-core technique, but that one treats one map in depth while this one
applies the technique across different special functions.  Whether the general
reversion calculi they each develop are the same calculus is exactly the kind
of comparison the intake gate defers.

| Directory | Document | Source receipt | PDF receipt |
| --- | --- | --- | --- |
| `Asymptotic_Inversion_Gamma_Barnes_G/` | *Asymptotic Inversion of the Gamma and Barnes `G`-Functions: Lambert-Core Transseries and a General Reversion Calculus* | 2,376 lines; 83,252 bytes | 29 A4 pages; 646,225 bytes |
| `inverse_k_function_transseries/` | *Inverting the K-Function at Infinity: Lambert–W Normalization, All-Orders Transseries, and a General Theory of Power–Logarithmic Reversion* | 2,259 lines; 66,867 bytes | 29 A4 pages; 349,822 bytes |
| `inverse_subfactorial_transseries/` | *Inverting the Subfactorial at Infinity: Bell-Sector Transseries, Inverse-Gamma Geometry, and a General Reversion Calculus for Rapid Cores with Tiny Oscillatory Tails* | 2,631 lines; 95,404 bytes | 38 A4 pages; 688,626 bytes |

All three arrival PDFs are readable and unencrypted, produced by
pdfTeX-1.40.26 at PDF version 1.7, and every font row is embedded with no
Type 3 font.  All three are A4, which is the canonical page size, so no
re-styling debt is recorded on that axis; two of the three
(`Asymptotic_Inversion_Gamma_Barnes_G/` and
`inverse_subfactorial_transseries/`) carry Libertinus faces, while
`inverse_k_function_transseries/` does not and would need a Libertinus rebuild
if it were ever promoted to canonical styling.

All three sources are LF with a final newline, so no line-ending normalization
was applied and the filed bytes are exactly the submitted bytes.  None of the
three loads the shared notation file `docs/fabius-notation.tex`; each uses
document-local notation, so all three are outside the corpus notation
migration and free of its defect classes.

Nothing beyond title, abstract, and package metadata was read at intake.  Claim
comparison against the corpus, deduplication against
[`../lambert-inverse-transseries/`](../lambert-inverse-transseries/) and
[`../../lambert-w/`](../../lambert-w/), proof checking, numerical
reproduction, editorial consolidation, and Lean crosswalking are all deferred;
nothing here has been merged, rewritten, or verified.

One connection worth recording for the deferred phase, and *not* acted on:
the corpus already carries a Lambert-W layer of its own — the analyticity of
both real branches, the lower-branch bracket and its explicit remainder rate,
and the Fabius saddle expansions — so the "Lambert core" these three articles
build on is formalized here to a degree they do not assume.  Whether any of
their reversion machinery is already available in that layer is unexamined.

See [`../../MANIFEST.md`](../../MANIFEST.md) for the group record.
