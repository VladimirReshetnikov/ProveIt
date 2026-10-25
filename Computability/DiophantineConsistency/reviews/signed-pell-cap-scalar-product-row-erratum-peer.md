# Independent review of the scalar-product row-address erratum

Reviewed by intake_e13 on 24 October 2026. The complete outside erratum
`signed-pell-cap-scalar-product-row-erratum.md`, SHA256
`a97d2312c775a5987f43164a90ea39ab2814be5e32a3fe7c2897d9c90a630587`,
was read against both complete frozen source JSON files. **Approved: the
corrections are exact and preserve the ordinary argument.**

My earlier author-side literal audit checked selected rows and semantic
port data separately and missed the row-to-call mismatch. Its earlier
binding claim must be read with this erratum. No sealed proof, binding,
source, peer record or manifest has been edited to hide that error.

The old source whole SHA is
`725f72f96d418639412b05541160c6793472be35e25d35133d8a639d32c2dc84`.
The refined source whole SHA is
`fdb5b9adaf91541a9235964e10ac8c107bac4a7b35cba900a781f0ce1184f673`.
Their closed manifests53244a0a... and73a5b427... and the affected
scalar-product manifest53b206b9... authenticate, including every actual
payload member. The corrected old rows292/307 are exactly refined291/306.
Old297/312, refined296/311, instead belong to calls12/15.

Independent inert inspection checked every one of the erratum's eighteen
ledger entries against the actual `pow<call>.power_congruence` label and
compared each WHOLE old row to its refined counterpart. The exact old
row sequence is

    227,235,240,248,254,259,267,272,277,
    282,287,292,297,302,307,312,317,322.

Every refined address is one less, and all eighteen whole residuals are
otherwise identical. The complete five-term rows displayed for calls11,
12,14 and15 match both literal sources coefficient-for-coefficient, with
no additional constant or nonlinear term.

For call11 all five old rows288..292 match refined287..291; for call14
all five old rows303..307 match refined302..306. Besides comparing their
literal coefficients, independent sparse collection verified the exact
lowered request identities:

    r292+r288-r290+r291
      =v333+(v179-v246)*v334-v211-v289*v336,
    r307+r303-r305+r306
      =v351+(v179-v246)*v352-v223-v289*v354.

The corresponding norm rows, after their exact A*Y gate ideals, are
X^2+(1-A^2)Y^2-1. The common q modulus is v289: old rows249..251,
refined248..250, define v290=2*v179*v246, v291=v179^2 and
v289=v290-v291-1. This confirms the erratum's Tq formula and does not
assume the power semantics being proved.

Thus the y+1 request really is q-base call11 with outputv211 and
pair333/334; the x+1 request is q-base call14 with outputv223 and
pair351/352. The unchanged retained remainder-bound row191 still gives
v223=q*v225+v226+2, so the positive-output premise in the x recovery is
unchanged. The correction supplies the actual requests used in the proof;
it introduces no new sign graph, power assumption or composition theorem.

The denominator, negative-index and eight-factor proof is approved with
these corrected literal addresses. This is an ordinary/source-interface
correction only. No successor equation, compiler, grouped materializer,
incoming executable, runtime checker or Lean was executed. Only read-only
JSON/hash inspection and exact coefficient collection were used.
