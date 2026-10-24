# Raw integer bijection and pointwise extension to the frozen parent

Let r_0,...,r_1176 be the original raw quadratic residuals. For each
of the 79 exact raw guard indices v in domain_certificate.json, add
G_v=v-a_v^2-b_v^2-c_v^2-c_v, with private fresh integer variables.
The unprojected polynomial is

    Q1496=sum_i r_i^2 + sum_v G_v^2.

The retained profile stores all 4995 collected monomials, of degree 4
and height 427. Its rows have height 8. All coefficients originate in
the unchanged raw source or the literal guard equations.

## 1. Exact zero bijection with the compact 904 equation

The original raw builder has a canonical set of 667 retained coordinates
and 592 omitted affine gates. The full metadata correspondence is
checked, not inferred from shortened names. Each omitted coordinate is
uniquely determined by a triangular integer affine expression. Hence
the 592 recipes define an extension over Z without any sign assumption.

Substitute these recipes into every original row. Exactly 592 defining
rows become identically zero; the other 585 become the literal compact
body residuals. Restricting the raw tuple and then restoring gives back
every raw value at any raw zero, because the recipes follow from monic
defining equations. Restoring and then restricting is identically the
identity. All 592 polynomial identities and all 667 retained identities
are checked independently.

The raw and compact equations have the same 79 guarded body values.
The raw values are selected by the exact retained-coordinate map.
Copying each raw triple to the corresponding compact triple identifies
every guard row coefficient for coefficient. The full inverse map
therefore consists of all 592 raw affine recipes and the same guard
witnesses. BRIDGE904.json contains the complete 1256-row partition:
592 zero defining rows and all 664 literal compact rows, each exactly
once. Its full coordinate restriction has 904 distinct entries and
restriction after restoration is identity on all 904 coordinates.

This proves a Z-zero bijection Q1496 <-> Q904. There is no auxiliary
choice, order assertion, source power interpretation or coordinate sign
change in this first map.

## 2. Exact composed extension to the literal 967 equation

At the Q904 zero, apply the frozen ordered guard-consequence theorem
in research/main-root-and-modulus-signs. Its hypotheses are precisely
the same 79 raw guards. The proof first recovers all 643 semantic-prefix
signs independently of omitted private guards. All 15 actual exponents
are strictly positive. Carrier bounds, the signed-index theorem and
the actual small-output residues recover all 15 X signs and five T
signs before source power interpretation. The independent positive-base
pow1 call then makes raw87 positive and recovers the final T sign.

The 21 omitted values are thus nonnegative at the same raw tuple.
No raw or retained body value is changed. For each omitted value choose
integers a,b,c with v=a^2+b^2+c^2+c, using exactly the same Legendre
conversion as the frozen parent. Copy all 79 retained guard triples
and insert these 63 new witnesses into the precise missing literal967
slots. BRIDGE967.json gives this complete composed map. Its checker
recollects every one of the 100 target guard rows after selecting the
actual raw body values and copied/fresh witness slots. All target
auxiliary slots are covered once.

The original raw body reduces to the literal967 body by step 1, so
every target row vanishes. Only now is its inherited ordinary
normalization/calibration theorem invoked. Conversely, a literal967
zero restricts to Q904 by forgetting exactly the 21 omitted triples;
step 1 restores a Q1496 zero. This establishes the complete integer-zero
existence equivalence. Step 2 is existential in the 63 fresh Legendre
witnesses; step 1 itself remains a bijection with no fresh witnesses.

## 3. Signed projections and exact coefficient checks

Each projected equation carries its complete monic elimination/inverse
certificate. The independent verifier authenticates its source and
checks every inverse over arbitrary signed integers. No coordinate is
removed as unconstrained. It verifies that every removed residual is
the actual monic defining equation and that the full remaining residual
list after substitution is exactly the child list. Thus zeros restrict
forward and reverse through the complete integer recipes.

For soundness always reverse this signed projection first, including
all guard variables, to obtain a literal Q1496 zero. Apply step 1 only
after that restoration; then step 2. None of these maps replaces signed
integer inversion by natural subtraction or derives signs from intended
source meanings prematurely.

The complete sum-of-squares coefficients are independently recollected
for every stored profile, establishing the full polynomial equality,
exact degree 4, support size and coefficient height. Off-source signed
inverse controls accompany these identities; they are not sampling
proofs. Corrupted row partitions, metadata, inverse coefficients,
complete coefficients and copied/fresh witness slots are rejected.
Both normal and optimized Python retain all validations. The source
uses the same ordinary calibration as the frozen967 chain; no new
Lean or internal-ZFC transfer is claimed.
