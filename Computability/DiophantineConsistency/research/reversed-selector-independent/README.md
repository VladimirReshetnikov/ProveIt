# Reversed selectors at length2521

[PROOF.md](PROOF.md) gives the complete ordinary construction with
marker1004, sole doubled clause1515 and cell length2521. The new selector
map is explicit: physical0 represents old tile0, and physical j represents
old tile943-j for1<=j<=941. It permutes exactly the942 admissible tiles;
the old forbidden tile1 remains absent. The initializer is now14. Every
action, state, color and computation is preserved by the complete index
bijection, with all packed words encoded afresh.

This ordering puts a small complete coefficient tail at the high indices.
The actual doubled tail512..1004 sums to57463969448796. Together with
the global carry bound57, that bound resets every field0..1003 before
any count or phase interpretation. Marker1004 needs only zero incoming
carry: all reflected weights are even, so its parity test first forces
an integral field rotation. The sole clause then decodes at most one
selector and all34 labels, even with a Boolean temporal summand and the
extra bare contribution x_511.

Decoded Start excludes every remaining offset. Offset20 contradicts the
new physical tile941's south-bit0. Offset19 requires a global argument:
all nine copy parities yield the doubling graph on south colors, with
only the additional edge510 to509. Its only directed cycle is0, which
contradicts Start's south510 on every finite temporal permutation. No
prior occupation or unique-Start assumption enters this argument.

The916 low padding tests now use bit3, with native low mask
`8*G_917(rho)-4`: origin bit2 remains unchanged. Each reflected source
at fields1..916 is a selector, so after count recovery there is at most
one such contribution. Its residue modulo2048 is0 or2; the three
possible unit contributions raise that residue only to0..5. Thus every
bit3 test is zero even though the whole digit may be large. This includes
all safe Boolean dummy subsets. Product field2519 resets, leaving the
single zero top field2520 and the strict representative bound `F<q/rho`.

The full proof includes the actual collision `DC_1004=1+c'_511`, every
copy parity, the predecessor `Aadj+x_510`, the physical zero-weight
marker and dummy, the source-mask shift exactly once, actual binary
rank, ordinary safe increments and the complete controller. It proves
both positive P66 witness maps and explicitly composes with the
[uniform Carrier65 theorem](../carrier65-independent/PROOF.md) at the
same four new fixed ports. That corollary has14 positive inputs,
65 integer-leaf operations and exact degree150. It uses the established
canonical converse, including its signs and positive rank.

All four constants together occupy59,297 minimal unsigned bytes,
10,152 fewer than the scaled2953 tuple. This is a new tuple and
specialized polynomial. The whole printed and rendered page, decimal
seed notation and equation-variable naming are separate candidate
artifacts; no page-size claim follows from this raw-integer count.

The final [certifier](certify.py) and [certificate](certificate.json)
bind the complete proof, authenticated whole language, both3297-entry
coefficient arrays and every port. The proof author read the entire
certifier before running its normal and optimized read-only checks;
both reproduced the artifacts exactly. Explicit exception guards remain
active under optimization. The checks include all1004 low-reset arrays,
all916 overlapping padding arrays, all935 support-compatible phase
cases, every218,776 count quadruple, the entire512-state graph and all
942 decoded tile transitions, actual shifted mask/rank controls and the
complete modular routes. These finite checks do not replace the ordinary
unbounded proof.

| Artifact | SHA256 |
| --- | --- |
| Proof | `81e9dc739834d385a0134b23cdb6744ad7df2228af05a3ad66956fb17cdb28e8` |
| Certifier | `c01832bbf7a3e356e46241959ac10ecb474208fff749ba6ac539841bcd50fb4f` |
| Certificate | `e778823a2ff489789db769189e6e217c8e8d1db955b15232eddd8d473b3e36ed` |
| Complete scaled array | `a3145e015691f63261165c2ab7880e915bac0028321f4192104ff0533a739618` |
| Complete base-Phi array | `536d32acbef01b9c9b6d8cf306a14e51acd40b35e51e860427143c42725dfdd3` |

Finite premise Pcrv and the exact full-tail facts are discharged. Prime
L2521 gives squarefree d118487=47*2521. The exact orders of2 and B
are23 and1260=`2^2*3^2*5*7`, both coprime to d. Their least common
multiple28980 divides lambda-1 for prime lambda231841. The valuation-one
lift is19327888648=`1+231841*83367`. The full H residues are34,1660,56592
modulo47,2521,231841. Printed base-Phi, doubled dense polynomial,
direct decoded-tile and whole-integer K evaluations agree.

| Port | Bits | Minimal unsigned bytes | SHA256 |
| --- | ---: | ---: | --- |
| beta |118487|14811|`b4a60833a4b9a15626af6d0672cda5a644e10707d4d93e528af471048311eea3`|
| K |118911|14864|`05862bb738b9ec0e25739a0286f23db1bff4130d8d915df60d96d34f691684bc`|
| MC |118487|14811|`d16c2b7baa32be42de7cc2c90352230c56c05bf42c94086723ec042424c15e93`|
| MF_source |118488|14811|`72d134ca88b90d419900344cfbcb1db2c1f75d01c53dcd3fd577ff3b7a501334`|

Independent mathematical review is coordinated separately by ROOT.
The ordinary equivalence retains the named complete arithmetic,
syntactic-refutation and foundational calibration contracts. No
consistency decision, actual unsolvability, global minimum or fresh
end-to-end formal-kernel/internal-ZFC replay is claimed. The negative
controls for center1514 and bit2 padding show limitations of the stated
local bounds, not native counterexamples. Accepted predecessors remain
frozen.
