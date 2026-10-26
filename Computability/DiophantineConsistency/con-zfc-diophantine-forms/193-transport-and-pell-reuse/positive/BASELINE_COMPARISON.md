# Bounded comparison ledger

Repository snapshot: `cdfea7d90176775d74c1c30afbe49fa78ade9897`.
The relevant snapshot contains placed packages through 178 and five incoming
archives. The ledger is a comparison with inspected material, not a claim about
all existing or possible Diophantine equations.

## Ten strictly positive variables

| Construction | Exact degree | Live binary operations | Status at snapshot |
|---|---:|---:|---|
| Package172 free-quotient inverse chart |214|87|Placed; immediate parent|
| Package178 whole-product center |208|116|Placed; source of center identity|
| Incoming Affine Horizons, A+1 center |210|89|Incoming|
| Incoming Affine Horizons, A center |206|90|Incoming; lowest inspected prior ten-positive degree|
| This work, quotient center |202|99|New companion|
| This work, folded weighted square transport |190|118|New principal endpoint|

Thus degree190 is lower than the degree206 incoming comparison, at28 additional
binary operations. It is also lower than package178's degree208 at two
additional operations. The companion degree202/99 offers another tradeoff.
None of these claims establishes a global simplest polynomial.

The literal counts charge addition, subtraction and multiplication, including
squaring and multiplication by fixed integers. Constants are free leaves and
shared registers are reused. These counts therefore do not measure evaluation
bit complexity or hide the size of the four-number coefficient tuple.

A structured inspection covered169 matching ten-positive JSON graph files in
the checked-out DiophantineConsistency tree. It required a top-level list of
ten witnesses/variables/inputs, a domain string containing `positive`, and an
integer exact-degree/degree/total-degree field, and skipped files over2MB.
The minimum found there was package178's208; incoming archives were inspected
separately. This scan is corroborating evidence with a stated schema scope,
not a completeness theorem about the repository. The top-level README files
of packages160–178 and the active research's current README and latest review
were also inspected. Active candidate subtrees outside the sparse checkout
were not exhaustively materialized.

Exact relevant paths:

- `con-zfc-diophantine-forms/172-pooled-powers-round21/part2/ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/positive10/positive10_degree214_ops87.json`
- `con-zfc-diophantine-forms/178-polynomial-centers/whole_product/equation.json`
- `docs/incoming/ConZFC_Affine_Horizons_Centered_Certificates_2026-10-26.zip`,
  member `ConZFC_Affine_Horizons_Centered_Certificates/positive/late172/centerA_radix67.json`.

The first two paths are relative to `Computability/DiophantineConsistency/`.
All incoming-member comparisons refer to the archived files at the fixed
snapshot, not to a later branch head.

## Other domains and complexity regimes

| Inspected construction | Domain | Variables | Degree | Other measure |
|---|---|---:|---:|---|
| Package101 boundary-complete |Strictly positive integers|9|997810|1057 operations|
| Package101 boundary-simple |Strictly positive integers|9|1472168|420 operations|
| Package82 quartic37-direct |Unrestricted integers|37|4|24 squared residuals|
| Incoming Pell Carrier65 |Strictly positive integers|14|150|65 operations|
| Incoming Affine Horizons roots |Unrestricted integers|14|85|110 operations|
| Incoming Affine Horizons roots companion |Unrestricted integers|14|87|108 operations|
| Package177 direct oriented powers |Unrestricted integers|87|8388612|2447 operations; C222 route|
| Incoming Mixed Base Pooling |Unrestricted integers|112|24|49 squared residuals; C222 route|
| Incoming Diagonal Growth |Unrestricted integers|214|4|5656 collected terms; height219813; C222 route|
| Incoming Affine Horizons |Nonnegative integers|202|4|154 squared residuals; C222 route|
| Incoming Affine Horizons octic |Nonnegative integers|200|8|Separate higher-degree endpoint; C222 route|

Nine-positive-variable equations already exist. The present ten-positive
construction does not improve that variable count. The37-integer quartic
already supplies a low-degree alternative with a calibrated fixed tuple;
the newer C222 quartics are interesting because of their different coefficient
architecture and proof-calculus route, not because214 is the globally smallest
quartic dimension. The14-positive65-operation equation has fewer operations
and a lower degree than the new principal, with four extra variables.

## All five incoming archives

1. `ConZFC_Affine_Horizons_Centered_Certificates_2026-10-26.zip`:
   supplies the degree206/90 ten-positive comparison, integer215 quartics,
   natural202 quartics, natural200 octic, and14-integer degree85/87 forms.
2. `ConZFC_Cofinal_Pell_Compression_2026-10-25.zip`:
   supplies integer229/228 quartics and integer206 degree24 and207 degree16
   pooled equations, without further monic dimension reduction.
3. `ConZFC_Diagonal_Growth_2026-10-25.zip`:
   supplies214-integer quartic,153 rows,5656 terms,height219813.
4. `ConZFC_Mixed_Base_Pooling_2026-10-25.zip`:
   supplies143/8,119/16,112/24,107/32,102/64 integer variable/degree points.
5. `ConZFC_Pell_Carrier65_2026-10-25.zip`:
   supplies14-positive65-operation degree150 primary and domain translations.

The new principal retains the original whole BFS943/radix67 tuple. The incoming
Affine Horizons archive also gives a separately calibrated Start-marker4177
tuple with smaller stored constants; no independent port from that tuple has
been substituted here. A source-calibrated tuple replacement would require its
own preserved reconstruction and completeness proof.

## Logical boundary

All comparisons above concern supplied polynomial definitions and the source
ordinary proof claims. They are not new replays of every historical formal
development. This work proves its new arithmetic bridge by ordinary arguments
formalizable in ZFC and performs exact finite graph/algebra/coefficient checks.
It does not freshly compile an end-to-end Lean/Rocq derivation, assert
consistency, exhibit a root, or prove a global minimality theorem.
