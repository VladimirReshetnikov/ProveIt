# Independent review of the complete length2011 masks

Result: PASS for the finite mask definitions, their printed-recipe identities,
and their `NativeSourceMask.Interface`. ROOT authored the three modules;
`controller_certificate` independently read all 332 lines, the invoked mask
interface, and the actual maintained TeX formulas. This review did not modify
the modules or the displayed equation.

| Reviewed source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentMasks2011.lean | 72ec99ac052c4d244f22f2590fb5645cebbe9ffe3a18fd89fe1cb8db7248fe06 |
| CurrentMaskRecipes2011.lean | 6dfe8ca1a8eaf16b74767cade35572d234d76ac22b409dc68f90cb87d904fbe3 |
| CurrentMasks2011Checks.lean | 753c77841952564deb445effa6c829bd9314b17bed2c6fd9dad0eae73d84ad89 |

The reviewed maintained `equation.tex` and the preserved
`candidates/one-page-padding-staircase-carrier65-2011/equation.tex` are
byte-identical, SHA-256
`a48ac1f5bc498bfdbf300c7050332ecaa28af1fc43f27d86b0879a79bd38714e`.
The Lean formulas agree with its entire low and high mask recipes; the
fourth port is the native high mask plus beta exactly once.

The low support is the disjoint union `0..950`, `960..985`, and `{1004}`,
with 978 elements. The definition is sealed for elaboration efficiency,
but its exact defining equality is proved and audited. Its integer value
is `beta-G951-rho^960*G26-rho^1004`. Natural subtraction is justified by
the existing mask lemma and the support bound, rather than assumed to
coincide with integer subtraction.

The high digit list has origin digit4; 916 digits8 at positions1..916;
nine digits1 at960..968; eight digits1 at987..994; marker digit1 at1004;
and clause digit`2^45-4` at1005. Every other digit through2010 is zero.
Its complete population is `1+916+9+8+1+43=978`. The geometric-series
identity merges the origin and padding into `8*G917-4` with no missing
term. All high digits are below `rho=2^47` and its 1006-digit prefix gives
the strict high-mask bound below beta.

The derived low population is93539, so the two populations sum to
`47*2011=94517`. Both masks are positive and strictly below beta. The
low residue modulo rho is `rho-2`, hence its residues modulo2 and4 are0
and2. The high residue modulo8 is4. These facts discharge every field of
`NativeSourceMask.Interface` for arbitrary nonnegative integer K. The
extra modulo4 result is proved from the full low mask, not supplied as
an assumption for the thirteen-variable argument.

As an independent finite cross-check, a newly authored standard-library
calculation reconstructed the complete support and all2011 high digits
without importing any project module. The complete resulting integers
match the preserved page's decompressed coefficient files byte for byte:

| Port | Raw bytes | SHA-256 |
|---|---:|---|
| beta | 11815 | a22ea3808ae016284c057d90f1bf2b76db1be2d34d11c0856f3315f6577d4b27 |
| MC | 11815 | 2b5c9296e32616260e64a051c92892645b9aa1bf0bf4c0d931e464080702ca9f |
| MF_source | 11815 | 5c15fc24e4978b878ed531abf30b2dcfe255083372034612b759b65eee1f0c25 |

Each of the three reviewed modules was independently compiled freshly
using `lake env lean -M6000 -j1 -o ...`, with outputs confined to
`/tmp/current-masks2011-peer/`; no shared object or dependency scheduler
was invoked. All three exited0. The mask module reports two benign
exponentiation elaboration warnings for exponent1007 and the recipe
module one for exponent257; no proof was rejected. Source hashes were
rechecked after the runs and remained those above.

| Independent log | SHA-256 |
|---|---|
| masks.log | 9767f21c9b7cdc2335e0ca62042e674cc573e3c97975168a69d340d912e241c5 |
| recipes.log | 0e4344c2f5752d48f2647218f8103eb43b734b9b56fbb5c0957f72c5a614dc28 |
| masks-checks.log | 9ece9a7df6edaeaccfd27658033c1b27b42f63f2ae2530198065af08f8d6632f |

All seven axiom reports, including the sealed-support equality, both
printed recipes, populations and complete interface, contain only
`propext`, `Classical.choice`, and `Quot.sound`. Boundary checks cover
both support intervals, the isolated marker, residues, and the single
source-port shift.

This closes the concrete finite-mask interface and its ordinary binding
to the displayed recipes. K remains a parameter here. It does not bind
the decimal machine to the native tableau, prove the displayed equation
has no positive zero, or supply the remaining Con(ZFC) equivalence.
