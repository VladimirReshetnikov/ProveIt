# Row-address erratum for the current-cap scalar-product proof

The sealed current-policy scalar-product argument has two incorrect power-row
addresses. Its intended base/exponent/output ports and ordinary proof steps
are correct, but those ports were not coupled to the claimed actual row.
My earlier independent review missed this mismatch. This outside erratum
corrects that literal binding claim without changing either sealed parent.
No project program, compiler or Lean was executed to obtain this correction;
the actual frozen JSON rows and labels were read directly.

The affected packet is research/signed-pell-cap-scalar-product, seal
53b206b990c9b1ea1a9cdda4822887010f796253a907eede2ee00bc9037890da.
Its PROOF.md is016bade28e80b4a829f8812ec7f21844bd6023781a041c3e6ef7bd1ab34642fa;
BINDING.json is2d0a0fb3c8717b69fef332c10a14a9313abfe4b0a66385ac51f57983602b2afb.

## Corrected references and complete literal terms

The immutable old source is research/signed-pell-cap-source/source.json,
SHA725f72f96d418639412b05541160c6793472be35e25d35133d8a639d32c2dc84.
The just-closed refined source is research/signed-pell-cap-refined-source/source.json,
SHAfdb5b9adaf91541a9235964e10ac8c107bac4a7b35cba900a781f0ce1184f673.
Its manifest is73a5b427338c33cb5ff0365fc64a994b796b16837d9bdc2a987d63d5eef8ed51.
Every coordinate in the four residuals below is unchanged by its body map.

| Call/actual label | Old row | Refined row | Exact complete residual |
|---|---:|---:|---|
|11 / pow11.power_congruence|292|291|-v211+v333-v335+v337-v338|
|12 / pow12.power_congruence|297|296|-v217+v339-v341+v343-v344|
|14 / pow14.power_congruence|307|306|-v223+v351-v353+v355-v356|
|15 / pow15.power_congruence|312|311|-v229+v357-v359+v361-v362|

These term lists bind the WHOLE rows: all five terms are linear with exactly
the displayed coefficients, and there are no omitted constant or nonlinear
monomials. Every label is included in the table. Thus no normalization or
serialization convention for a row-only hash is needed.

Call11 has base q=v179, target y+1=v2+1 and output Qy=v211, with pair333/334.
The norm uses v335=A*v334, and its exact request lowering is

    v337=q*v334, v338=Tq*v336,
    v333+(q-A)*v334-v211-Tq*v336=0.

These are old rows288..292, refined rows287..291. Call14 has base q,
target x+1=v1+1 and output Qx=v223, with pair351/352. Its exact lowering is

    v353=A*v352, v355=q*v352, v356=Tq*v354,
    v351+(q-A)*v352-v223-Tq*v354=0.

These are old rows303..307, refined rows302..306. The shared q modulus
is coordinate289, Tq=2*A*q-q^2-1, defined at old row251/refined250.

Rows297/296 instead request (q+1)^(v21+1), outputv217, pair339/340.
Rows312/311 instead request (q+1)^(v23+1), outputv229, pair357/358.
They cannot serve as the q-power requests for y+1 and x+1.

Specifically, correct PROOF section3's call11 row297 reference to292,
and its call14 row312 reference to307. Correct BINDING.x_request.power_row
from312 to307; bind the complete lowered row ranges above. The old
BINDING.literal_rows copies of297 and312 are accurate copies of those
OTHER calls, and must not be described as certificates for calls11/14.
This is an erratum instruction, not an edit to the closed packet.

## Whole eighteen-call row ledger

| Call | Old row | Refined row |
|---:|---:|---:|
|0|227|226|
|1|235|234|
|2|240|239|
|3|248|247|
|4|254|253|
|5|259|258|
|6|267|266|
|7|272|271|
|8|277|276|
|9|282|281|
|10|287|286|
|11|292|291|
|12|297|296|
|13|302|301|
|14|307|306|
|15|312|311|
|16|317|316|
|17|322|321|

Each actual label is pow<call>.power_congruence. The refined deletion of
old body row217 shifts all these row addresses by one. Calls0,4 and6,
which supply the t/base-one/derived-t+1 stages, were already correctly
addressed in the old proof.

The ordinary proof uses q^(y+1) and a q-base x+1 request with output>=2.
Both requests are present in the literal source at the corrected addresses,
with exactly the stated ports and retained anchors. Hence the denominator,
negative-index and eight-factor arguments remain valid after correcting the
references. No new power assumption or graph is introduced. The previous
inert checks established selected-row equality and semantic-port equality
separately; they did not establish the erroneous row-to-call membership.
Subsequent literal interfaces must explicitly check that membership too.
