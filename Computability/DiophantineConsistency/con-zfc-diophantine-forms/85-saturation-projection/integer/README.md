# Transport-coordinate projection of the joint-sign family

All witnesses are **unrestricted integers**. This packet gives four explicit
fixed Diophantine polynomials, each with an exact integer-polynomial
projection/restoration to its incoming joint-sign predecessor:

| New variables | Exact degree | Live binary operations | Parent variables / degree / operations |
|---:|---:|---:|---|
|18|88|105|19 / 88 / 109|
|19|32|108|20 / 32 / 112|
|20|20|111|21 / 20 / 115|
|21|16|114|22 / 16 / 118|

The main equation is `transport18_degree88.json`, a sum of six squared
residuals. `section.tex` prints the full equation, proves the projection,
explains degree and operation accounting, and states the inherited proof
boundary. No named register introduces a new quantified variable.

## What is new and what is inherited

The complement-coordinate substitution `C=q-F-alpha` makes the transport
equation monic in F. Set `F=(K0+W)C-z(q-1)` and restore
`alpha=q-F-C`. This removes one coordinate and one residual. Source73,
*Guard reanchoring*, already introduced this method for an older system;
it is explicitly credited. The new work composes it with the much newer
incoming joint-sign projection family and checks the resulting four whole
equations. No general-method priority or global simplicity minimum is claimed.

The six actual coefficient numerals are unchanged: the source34
`mixed-parity-unrounded-1064921` tuple, plus determinant scales
`2^1113` and `2^666104`. Raw payload size is 615,883 bytes. The high mask MF
is already shifted. Its literal bytes and complete finite construction
are retained, together with the literal machine and tile table.

The new projection theorem is elementary and unconditional over arbitrary
integer port values. Its connection to Con(ZFC) composes with the retained
ordinary Pell/native/refutation calibration. No new end-to-end Lean/Rocq
or exported object-ZFC derivation is claimed. Existing incomplete formal
calibration obligations remain inherited. Finite algebra checks do not
discharge those unbounded semantic obligations.

## Reproduction

Python3 standard library only; no network or external algebra package:

```sh
python3 build.py
python3 verify.py
python3 -O verify.py
```

The checker is independent of the new builder. It authenticates retained
sources, binds each original DAG to its parent polynomial, validates all
new residual identities by exact sparse algebra, checks the zero deleted
row and sum-of-squares finalizer, verifies exact degrees and topology,
regenerates every actual numeral from the complete source recipe, and
rejects an operation-preserving identity corruption. Optimized mode uses
explicit checks rather than removable assertions.

`SOURCE_PINS.json` pins the input archive at repository commit
`c1a102936aca437e9999530a0111e6ddab56dc6d`, every retained source byte,
and source73's earlier method. The SHA256 hashes authenticate the included
bytes; the polynomial is defined by the actual literal bytes and finite
recipe, not by hashes alone. New source outputs live at this packet root;
the `upstream/` tree is retained unchanged. The output receipts are finite
verification records, not consistency decisions.

`evaluate.py` optionally evaluates one supplied DAG at a literal integer
input tuple, either exactly or modulo a specified positive modulus.

## Integration

`section.tex` is a standalone section for inclusion in a larger LaTeX report
using amsmath, amssymb, amsthm, booktabs, and theorem/proposition environments.
It uses the report's `\Z`, `\ZFC`, and `\Con` macros. It has no preamble or
document wrapper. All labels begin `int-`.

Preserve the whole coefficient tuple and the inherited notices in any
repository integration. No remote repository was modified by this packet.
