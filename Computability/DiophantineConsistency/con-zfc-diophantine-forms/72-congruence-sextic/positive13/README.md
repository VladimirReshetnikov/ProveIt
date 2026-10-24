# Thirteen positive unknowns, exact degree 28

The exact polynomial is specified by p13_degree28.json: 13 strictly
positive integer witnesses, four fixed coefficient ports, six derived
fixed numeral leaves, 98 live binary arithmetic gates, and one output.
Its four residuals have exact degrees 13, 13, 13, and 14.

PROOF13.md and section13.tex give the complete new arithmetic proof.
ACTIVE_BINDING.json binds every source numeral to an actual relative
path and raw-byte SHA-256. MF is already shifted by beta.

The leading homogeneous form is

    81 beta^4 i^4 (eta+zeta)^8 X^4 Y^12.

The selected monomial i^4 eta^8 X^4 Y^12 has coefficient 81 beta^4>0,
so the degree remains exactly 28 at the authentic coefficients.

Run the root verify_all.py for complete finite verification, or:

~~~sh
python3 build13.py
python3 check13.py
python3 independent/check_independent.py
python3 verify_coefficients.py
~~~

The two algebra checkers do not import the builder. The second uses a
separate sparse Laurent-polynomial implementation over rational numbers.
Coefficient regeneration uses the unchanged native generator in a
temporary directory and compares actual integer bytes.

SOURCE_DEPENDENCIES.md names the inherited native and Pell interfaces.
Immediate source texts are included in upstream/ and native/. The full
transitive proof-assistant development is not bundled or rebuilt.
Finite symbolic checks do not prove the unbounded consistency equivalence.
