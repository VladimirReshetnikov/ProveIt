# Fourteen positive unknowns, exact degree 24

Supply E as an additional positive coordinate in the positive13 circuit,
use it wherever the old computed product X*Y occurred, and add the
residual E-X*Y. The five squared residuals define p14_degree24.json.

The new zero set is exactly the graph E=X*Y over the old positive zero
set. Projection and this unique extension are inverse polynomial maps.
Thus no additional Pell or native source assumption is needed.

The residual degrees are 12, 11, 12, 12, and 2. The selected coefficient
of i^4 eta^8 E^4 Y^8 is 81 beta^4>0, proving exact degree 24.
The delivered circuit has 101 live gates: 26 additions, 17 subtractions,
58 multiplications. Its five-residual core has 92 gates.

The improvement is degree 26 to 24 at fourteen positive variables,
with nine more gates than the inspected 92-gate construction.
At degree 24, it saves one positive variable relative to the inspected
15-positive, 89-gate construction, with twelve additional gates.
This is an elementary retained-register consequence of the new P13
construction, rather than an additional conceptual innovation.

ACTIVE_BINDING.json binds the entire same compact source-44 tuple,
whose actual payloads are shared with ../positive13/native/.
The local p13_degree28.json is a frozen parent copy for the lift builder;
its SHA-256 is identical to the main parent packet.

Run the root verify_all.py to verify the source, both positive circuits,
exact identities, coefficient binding, and literal degree certificates.
The local builder and checker are also standard-library programs:

~~~sh
python3 build14.py
python3 check14.py
~~~
