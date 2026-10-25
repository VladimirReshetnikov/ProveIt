# Independent strict-horizon power-interface audit

The source `../direct/source/raw_source.json` passes the
independent checker `../code/check_power_interface.py`. Its SHA-256 is
`5897bea71039b06249aa0786555908b8df8de255689cc6a39e473e36b7645e9e`.
The ordinary and `python3 -O` receipts are byte-identical.

The checker imports only Python standard-library modules. It independently
states all seventeen requested scalar powers, the five shared base moduli,
the fourteen principal Pell pairs, and the pooled signed-index equation.
It verifies the 34-atom square frame after the proved identification of
the first base with `t`; the squared copy of that redundant base is absent,
whereas the square of the actual index `t` remains. All first-power,
radius, beta, and affine-radix equations are checked exactly. The obsolete
`q^(t+1)` output, addition-pair gates, private quotient, and former second
remainder ratio are confirmed dead.

The audit goes beyond the inherited power-table checker. It verifies the
full signed cap, the anchor's dominance over all thirteen other principal
ordinates, the six affine rows assembling the inherited derived label,
and the exact normalized binomial-digit identities. All ten range rows
have the common modulus `N D`, with `D=q^x`. The four schema-parameter
ranges and the derived-label range now use `D/q^t`, as does the previously
strict row-index range. The two state ranges retain `D/q^(y+1)`; the two
beta-quotient ranges retain denominator `D`. All eleven remainders occur
with coefficient four in the same strict squared budget.

Twelve deliberate corruptions are rejected, including deletion of a
radix square from the frame, restoration of the duplicate base square,
substitution of the wrong *live* denominator ratio, a changed common
modulus, a damaged principal norm, an omitted pooled index, a shifted
anchor, an omitted ordinate in the dominance bound, a revived obsolete
power, a weakened affine radix, a squared radius, and a shifted range
remainder. These controls test the checker's sensitivity to the actual
interface changes, rather than merely whether a file checksum matches.

## Semantic delta

Replacing the five bounds `0<=a<=t` by `0<=a<t` strengthens soundness.
The usual prime-power range lemma uses lower binomial index `t` in place
of `t+1`; all existing precision bounds are sufficient for the smaller
factorial denominator. Completeness is preserved by choosing the cofinal
padded horizon strictly larger than every parameter and every entire
derived label sum in the finite refutation, including the fixed truth
padding tuple. This choice precedes the construction of the majorant,
beta code, CRT representatives, and self-sized radix. The evaluated
constructor expression used as the signed Pell anchor is retained; it
must not be replaced by a decoded local label or bounded by the horizon.

## Scope

The checker proves exact finite polynomial identities. It does not prove
Pell classification, prime-power range theorems, the C222/ZFC calibration,
or preservation of zero sets through the later projection. Those are
separate mathematical or certificate obligations, stated in the main
proof and the inherited sources. The source identities checked here
establish that the final strict-horizon interface is the one used by
those proofs.
