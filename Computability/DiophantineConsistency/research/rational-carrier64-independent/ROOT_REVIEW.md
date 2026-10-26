# Independent root review of the rational-leaf64 evaluator

PASS for the stated rational-leaf metric and exact polynomial identity.
ROOT did not author this packet. ROOT read the entire README, auditor,
64-row literal graph and complete deterministic receipt, then ran the
auditor normally and with Python optimization. Both read-only checks
reproduce the exact graph and receipt. No submitted executable was run.

The rank identity follows directly from q-1 = beta*J. Expanding the new
rank gives the old rank, including the source-mask shift exactly once.
The full retained prefix and suffix agree as literal rows. Therefore
equality at R propagates to tau and every norm and to the entire output;
it is an identity on all inputs, not a finite-sample or zero-set assertion.

The complete degree-zero leaves are beta, K0, MF/beta and MC-MF. The
denominator is fixed and positive. The coherent tuple makes MF/beta
strictly between 1 and 2; hence G+MF/beta is the sole nonintegral computed
register on integer inputs. Its next product cancels the denominator
using q^2-1 = beta*J*(q+1). All subsequent computed registers are integral.
The sparse Laurent calculation verifies both integral cuts and the
complete ten-term rank polynomial.

ROOT checked the whole gate substitution: six old rank-tail rows become
five, and the rest remain literal copies. The full census is 36 products,
16 sums and 12 differences. All 64 gates, 14 witnesses and four runtime
leaves are live and backward-referenced. This is a 64-operation evaluator
when fixed rational leaves are free. It does not lower the maintained
integer-leaf count of 65. Forming the analogous integer-only factored
rank requires six tail operations.

The exact main-norm cancellation is checked on its entire 323-term
polynomial, lowering apparent degree 22 to 18. Every complete factor
leader and the entire 56-term output leader agree with the accepted
Carrier65 certificate. The nonzero coefficient -8*beta^88 proves exact
degree 150 at the actual positive beta. The six negative controls test
the rank denominator, sign, offset denominator, invalid shorter tail,
q-squared subtraction and the actual downstream carrier sign.

Every raw and compressed port is bound to the complete reversed2521
certificate. The integer-source tuple totals 59297 bytes. This is not
the storage cost of encoding the derived rational/integer runtime leaves.
The actual mask populations 117509 and 978 sum to the odd d = 118487;
they rule out the suggested Wrank = -beta shortcut. The argument is
uniform, but this saved graph and its finite binding are specifically
reversed2521. The current sorted2501 page remains a separate record.

| Artifact | SHA256 |
| --- | --- |
| Complete proof README | `6662461637a9d8ef206ffa0a14ed7eedd4f561124914357ef661df0064591d65` |
| Auditor | `2ea18539c524f14ec1c96fa985c544b6c3a1372c3b562939a0f5869e476837a2` |
| Complete graph | `8fd205a43c4045914d88f4117ba263cf7a232ac26c64dcf09a1c37a8d88e7b27` |
| Complete audit receipt | `5c6faddaf7eaf798587a8fcd3fbacd20527439e849073b6c802d3ae4dd0c4167` |

The exact identity transfers the accepted parent's zero correspondence
without new witnesses. Its ordinary native and syntactic calibration
remains unchanged. No consistency decision, global minimum, coefficient
storage improvement or new formal-kernel/internal-ZFC replay is claimed.
