# One-addition prime-selector recentering in both complete U21 sources

The [complete sources and receipt](residue_affine_sparse_prime_recenter.json)
cost **466=171M+295A** for the one-program interface and
**465=171M+294A** for the two-program interface. Both retain **67 positive
witnesses** and degree upper bounds **5091** and **5160**, respectively.
Each source saves one addition from its own immediate
[joint-recoding parent](residue_affine_sparse_joint_recoding.md).

This time every state code is unchanged. The new complete polynomial is
identical to its own parent's polynomial over every commutative ring, at
the same supplied coordinates. The result uses a paid selector identity
to replace two private additions by one subtraction. It does not change
the universal84 bound or assert any arithmetic minimum.

## 1. Paid selector identity

Write E_i=`edgei_hat-1`. Exact expansion of the actual paid base gives

    G17 = prime_selector_113 = E5+E8+E9+E14+E15,
    A3  = prime_selector_111 = E5+E8+E9,
    D9  = E14+E15,
    D14 = control_codes__duplicate_state_8 = E24+E25.

Thus G17=A3+D9, as an all-ring identity in the actual supplied hats.
The parent current-control word includes the contribution

    17*G17+(D9+D14).

Recenter it as

    18*G17+D14-A3.                                    (1)

The scalar multiplication remains one multiplication. Both A3 and D14
are already live in the retained noncontrol base. The parent's D9+D14
uses two private additions, while the replacement needs one subtraction.
All other contributions to the current word and the entire target word
remain the same. Negative intermediate words need no supplied positive
witness; every original supplied coordinate keeps its original domain.

Equivalently the prime17 weight changes from 17 to 18; the state9
correction +1 disappears and state3 and state5 corrections become -1.
This leaves all 23 codes literally unchanged:

    0,1,15,21,9,17,13,11,5,18,8,38,30,32,10,3,12,4,40,2,6,7,14.

Their injectivity, loader code0, halt code14 and maximum40 are therefore
inherited, not newly presumed. The helper checks both full 36-edge current
and target coefficient vectors against the unchanged literal edge table.

## 2. Exact edit of each full parent array

The [standalone helper](residue_affine_sparse_prime_recenter.py) reads both
full arrays directly from the authenticated immediate-parent receipt.
It guards these literal definitions and the private consumer relations:

    joint_8  = 17 * prime_selector_113
    joint_1  = edge_14 + control_codes__duplicate_state_8
    joint_2  = joint_1 + edge_15
    joint_21 = joint_20 + joint_2
    joint_22 = joint_21 + joint_11.

Only joint_2 consumes joint_1; only joint_21 consumes joint_2; and only
joint_22 consumes joint_21. The emitted transformation is:

* Change joint_8's scalar from17 to18.
* Delete joint_1 and joint_2.
* Set joint_21=joint_20+control_codes__duplicate_state_8.
* Insert `recentered_current_prefix=joint_21-prime_selector_111`.
* Replace joint_22's first operand by that restored prefix.

Every other retained instruction remains literal and in an acyclic paid
schedule. The new prefix equals the old joint_21 by (1), including the
change propagated through joint_18, joint_19 and joint_20. Accordingly,
the only retained registers whose values change are exactly

    joint_8, joint_18, joint_19, joint_20, joint_21.

The restored prefix, joint_22 and all its downstream consumers have the
old values. In particular current word joint_24, target word joint_61,
their transport residual, all other residuals, the native product and the
complete output are unchanged at arbitrary supplied values.

The helper also proves this through a complete source interpretation.
It interns exact expression tuples, normalizing every globally affine
value over the actual supplied ports, including its constant term. The
old and new outputs have identical expression IDs in a shared exact
dictionary. No hash collision assumption stands in for an algebraic
identity. This checks every source row and the enumerated retained-value
exceptions. Separately, full sparse expansion of both current and target
words through all 36 actual hats proves their equal coefficients, and
all 20 comparison/finalizer rows remain literal. Their complete formal
expansion is U*(1+sum of six residual squares)-1, with every cut bound to
equal actual computed values.

## 3. Complete costs and unchanged interfaces

Outside the retained base, the current word decreases from24=9M+15A
to23=9M+14A. The target word remains37=12M+25A. Their single shared
29*D11 product remains paid once. Thus their live union decreases from
60=20M+40A to59=20M+39A. The further producers B*N,14P,C+14P still
cost2M+1A; the comparison subtraction is counted in the remaining
finalizer.

| Disjoint stage | One program: M,A,total | Two programs: M,A,total |
|---|---|---|
| Retained noncontrol base, including five residual producers |142,247,389|142,246,388|
| Private control producers |22,40,62|22,40,62|
| Remaining finalizer |7,8,15|7,8,15|
| Complete source |**171,295,466**|**171,294,465**|

All 931 emitted rows and all supplied ports are live. Excluding all20
comparison/finalizer rows gives certificate costs446=164M+282A and
445=164M+281A, respectively, with seven comparisons and67 positive
witnesses in the inherited convention. No comparison or finalizer cost
is omitted from the full bounds.

The one-program interface retains fixed E=3^e, ordinary positive input x,
and h=E+x+eta, B=64h, with eta>0 and B>=192. It has69 supplied ports.
The two-program interface retains fixed E=3^e and fixed dyadic C with
C>=64 and C>E, h=x+eta, B=Ch>=128. It has70 supplied ports. The same67
witnesses remain positive in each. The helper checks every actual height
and radix definition literally. It separately verifies that the two
complete arrays differ only by the parent's deleted height83 row and
two height/radix definitions; no positive-coordinate map between these
different interfaces is asserted.

Since each entire polynomial is unchanged, each entire supplied positive
zero set is unchanged without reselecting witnesses or proving a new
native bootstrap. The fixed-program conditions, ordinary-input prefix,
payload meaning, chronology and universality theorem are inherited from
that same immediate parent. There is no new theorem for invalid fixed
parameter slices or arbitrary signed compiler inputs.

## 4. Degree and validation scope

All72 native rows and all20 comparison/finalizer rows are literal. The
helper freshly expands the actual main-norm cancellation

    (X+ac+G)^2-(a^2+4a+3)c^2
      = X^2+2acX+2GX+2acG+G^2-4ac^2-3c^2.

The same computed boundary degrees give norm bounds816 and827, native
product bounds4993 and5062, and outer sum-of-squares bound98. The guarded
complete bounds remain5091 and5160; naive propagation gives5157 and5227.
No exact-degree claim is made. Full polynomial equality also transfers
every valid parent degree bound directly.

The receipt contains the two complete sources, exact row/consumer guards,
full control-word expansions, selector identity, whole-source identity
checks, complete ledgers/liveness, retained-value exceptions, and degree
checks. Sixty-four signed modular whole-source comparisons supplement
the exact proofs:32 per interface at two primes, with all supplied ports
varied. They check the restored prefix and every retained value outside
the five proved exceptions. Sampling does not certify any identity.

The candidate arose from a bounded search over decompositions of fixed
codes into prime weights and state corrections, in addition to other
joint-schedule experiments. Only the selected exact edit and its full
cost are claimed here. No exhaustive lower bound or optimum is inferred
from failure to find another saving.

The three authenticated inert dependencies are:

| Immediate-parent file | SHA256 |
|---|---|
| `residue_affine_sparse_joint_recoding.py` | `386f00228dd250a1c582a3bf93724e9732db71cdd8d4fea6828d0b78d06fe443` |
| `residue_affine_sparse_joint_recoding.json` | `a3b00883d84e7c8e9a6aea04ec3e54776fe927f7193f60a04050246f32039284` |
| `residue_affine_sparse_joint_recoding.md` | `16d4a9e60343eb4f8f4ee78e8d60e7aeb2ee73b8d045241dd4951e124cf7b404` |

The helper verifies the parent's helper and complete-array bindings and
leaves its canonical in-memory data unchanged. It imports only standard
library code; no predecessor is imported or executed. Strict JSON and
explicit checks remain active under optimization, receipt creation is
exclusive, and replay requires exact type-sensitive receipt equality.

Fresh normal and optimized exact replays from working directory `/` passed:

```text
python3 /tmp/residue_affine_sparse_prime_recenter.py --root ABS_WIP --expect /tmp/residue_affine_sparse_prime_recenter.json
python3 -O /tmp/residue_affine_sparse_prime_recenter.py --root ABS_WIP --expect /tmp/residue_affine_sparse_prime_recenter.json
```

The helper SHA256 is
`c5d8b2690f1e2a9b50aa063a95f81297ff388b276ab83ce487aa4cbaacc46798`.
The receipt SHA256 is
`e35399b892850ace2bf860fd37f0e3e9f8af34dd8e516f66718547e0689fe26c`.
