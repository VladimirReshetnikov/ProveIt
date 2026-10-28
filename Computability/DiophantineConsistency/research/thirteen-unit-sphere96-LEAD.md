# Prospective unit-sphere reduction from 76 to 75 operations

26 October 2026. This is a mathematical/source audit, not a materialized or
compiled candidate. Existing sources and graphs remain unchanged.

The exact parent is `thirteen-shared-squares96/polynomial.json`, SHA-256
`3de1d43a810e694cb2f87fb15330e1decc6f5944c2302a18088cb8d3cfd15b36`.
Its ordinary proof is
`ed2d33cca9c948c5d9ce8c96997caee6b5e4b8305ae2616e19c9eab929c28fe3`.
Retain every definition, all thirteen positive coordinates and all four
whole current2011 integer ports from that proof. In particular, write

\[
 Z=f^2-\Delta(bic^2)^2,\qquad
 U=\Delta(f^2-1)(V^2-y^2)+y^2.
\]

Replace the parent equation by

\[
 \boxed{(PQ)^2+U^2+Z^2-3=0.}
\]

## Complete proposed positive-zero argument

For arbitrary integers A,B,C, `A²+B²+C²=3` forces each square to equal one.
Indeed each square is at most three, hence its integer root is in
`{-1,0,1}`; three summands at most one can sum to three only when each is
one. This does not require separately excluding zero norm values.

For the actual carrier, `P≠−1` holds on every positive assignment with
positive beta. Both `Q≠−1` and `Z≠−1` follow without positivity from their
discriminant being one below a square. Consequently `PQ≠−1`: a product
equal to −1 has unit factors, and excluding −1 from both factors excludes
that product. Thus the sphere equation first forces `PQ=1` and `Z=1`.

Only after deriving `Z=1`, substitute

\[
 \Delta(f^2-1)=\bigl(bi\Delta c^2\bigr)^2=S^2.
\]

The auxiliary factor becomes `U=S²(V²−y²)+y²`, which cannot equal −1
modulo four. Hence the remaining unit square forces `U=1`. These three
equalities give the accepted72 product equation `PQ U Z−1=0`.
Conversely, the accepted entire-positive-zero theorem for72 gives
`PQ=U=Z=1`, which satisfies the proposed sphere equation. Both witness maps
are the identity. This is a zero-set equivalence, not a polynomial identity.

## Exact existing Lean bindings

Use `d := ThirteenCarrierSoundness.data p v` and
`y := ThirteenLVCarrier.y p v`.

- `ThirteenCorrectedStrong.first_ne_neg_one p v hb hv` supplies `d.P≠−1`;
  `hb : 0<p 0` and `hv : ∀j,0<v j` are its only assumptions. Its proof uses
  the actual restored parent with the harmless positive placeholders
  `z=y=1`, and `ConsecutivePell.norm_ne_neg_one`.
- `Carrier65.delta_shape p (ThirteenCarrierSoundness.parent p v 1 1)` gives
  `d.delta=(d.a+2)^2−1`. `ShortEquation.strong_ne_neg_one d.a d.D d.c`
  therefore supplies `d.Q≠−1`. The same lemma at
  `d.a,d.f,d.i*d.c²` supplies `Carrier65.strong d≠−1`. These exclusions
  have no positivity or previously assumed norm equation.
- After `Carrier65.strong d=1`, ring arithmetic gives
  `d.delta*(d.f²−1)=d.S²`. Then
  `ShortSystem.square_aux_ne_neg_one d.S d.V y` supplies `U≠−1` with no
  positivity, nonzero, or size premise for S,V,y.
- `ThirteenGroupedSquares96.residuals_of_positive72_zero` supplies the
  reverse direction's exact three unit equations, on the same assignment.

Source SHA-256 pins:

| Source | SHA-256 |
|---|---|
| ThirteenCorrectedStrong.lean | `57729066535acf1909d30ea5de0b4b78e1ac6f1ae11a126e1c2c4526cc546efe` |
| ShortEquation.lean | `2d447a166a33dedb90c8acdf0755d584a9d057bf46a047e0a454bf150f628b68` |
| ShortSystem.lean | `a9d50c6d8268df4d854d056c83995b3e0547c483fd800993471b2c718201d44a` |
| ThirteenGroupedSquares96.lean | `1b9aca9cb96c390ab074001c36680567969c6a33b6e556798b8394500d3cd424` |
| ThirteenSharedSquares96.lean | `7f09a4e8448d643e09c5bfb2289f2d7640b1a0a5a2b2600fc53cce07d640eb97` |

## Proposed schedule and remaining validation

Keep `h=f²−1` for the auxiliary coefficient. Change the strong residual
row to compute `Z=f²−strong_term` directly. Remove the `PQ−1` and `U−1`
rows, square PQ,U,Z directly, retain the two additions, and add a final
subtraction of three. This predicts 75 paid operations:42 multiplications,
18 additions and15 subtractions. All highest homogeneous forms are
unchanged, so the proposed exact degree remains96 with the same135-term
leader and selected coefficient256*beta^48.

Before accepting those finite claims, a separate new graph/auditor must
check all rows, liveness, entire leaders, literal dependence and complete
ports. Its formal algebra test should compare the graph with the new
sphere formula, not with the distinct parent polynomial. Negative controls
should include replacing3 by2 or4, omitting the Z normalization, and using
the old residual instead of a raw norm in a tested square. A separate Lean
leaf should prove the integer sphere lemma, all sign steps and identity
positive-zero maps, then inherit the actual external ConZFC endpoint.
No new internal HA/PA/ZFC theorem or minimum claim follows from this lead.
