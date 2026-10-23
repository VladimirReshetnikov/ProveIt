# Wave-7 arrival review at an exact source pin

Repository: VladimirReshetnikov/ProveIt.
Commit: `4b4349064a750ba6347293b55874a7f92abdd0db`.
The commit adds eight ZIP files under `docs/incoming`; these are arrivals,
not assigned collection package numbers. All eight exact archives have
been materialized, their Git blob hashes and ZIP CRCs checked, and their
contents retained as inert sources. `SOURCE_PINS.json` records paths,
URLs, byte lengths, SHA-256 hashes and member counts. No upstream program
was imported or executed.

The seven peer reports and the prior round-7 package all use the arithmetic
construction baseline `124c07c0b77a9e20e84676514d8b1ff78536ea3f`. One peer
also records a separately identified later formalization-status update.
Archive titles, rather than invented package numbers, identify sources here.

## Main reported constructions

Each entry below is **operations / exact-degree claim**. Domains are part
of the theorem. Gate counts were independently recounted; degree claims
were read with their supplied proof/certificate boundaries and were not
universally rederived by this intake review.

| Archive basename | Nine positive | Ten unrestricted integers | Other important results |
|---|---:|---:|---|
| `ConZFC_Sparse_Support_2026-10-23` | 651 / 25936016; 670 / 23878392 | 662 / 71151176; 675 / 65506504 | Sparse supported-pair labels239 or220; 15-positive degree44 at75 or76 gates |
| `ConZFC_Support_Sensitive_2026-10-23` | 651 / 30947584 | 653 / 56593864 | 11-positive115 /954; 14-positive79 /56; quotient absorption with early large-index bootstrap |
| `ZFC_Diophantine_Selective_Quadratic_2026-10-23` | 738 / 7344328; 734 / 12023320 | 659 / 21111400 | Sparse signed-borrow padding; calibrated popcount threshold; Sun-free13-integer759 /57866184; 11-positive117 /958 or115 /962; 15-positive72 /80 |
| `con-zfc-selective-2026-10-23` | 606 / 19615180 | 640 / 35876184 | Packed positivity word, raw support62/94 records; new complete native tuple215492 bytes, not composed into main equations; 15-positive74 /68 |
| `con-zfc-sparse-pell-124c07c0b7` | 548 / 15502748; 603 /10486092; 655 /10127484 | 582 /50822936; 637 /34378296; 689 /33202776 | Prior round7; 11-positive113 /954; 12-positive108 /897; complete tuple295388 bytes |
| `con-zfc-support-majorants-2026-10-23` | 562 /29157244; 568 /24399300; 599 /20754916; 618 /21823612; 624 /18262476; 655 /15534796 | 595 /53325896; 651 /39914856 | Higher division-free square-root majorant; its principal degree certificate is D^16 times the primary equation, not the primary equation |
| `con_zfc_sparse_arithmetic_2026-10-23` | 682 /33332620 | 709 /54768104 | Radical separator(1,b,bK); squared-modulus auxiliary quotient: 15-positive66 /157,68 /113,72 /80,74 /68 |
| `con_zfc_sparse_support_2026-10-23` | 652 /32568568 | 653 /59564744 | 11-positive117 /990 or115 /994; 15-positive76 /44 |

Positive/nonnegative coordinate translates can have different gate costs.
Fixed coefficients and register reuse are free under the stated arithmetic
circuit convention; binary scalar multiplication is not free. Register
names never create new quantified witnesses. This metric is not bit
complexity or expanded polynomial length.

## Actual low-variable frontier among these eight arrivals

For nine positive variables, the four nondominated displayed points are

- 548 operations, degree15502748, prior round7.
- 603 operations, degree10486092, prior round7.
- 655 operations, degree10127484, prior round7.
- 738 operations, degree7344328, Selective Quadratic.

For ten unrestricted integers, the three nondominated displayed points are

- 582 operations, degree50822936, prior round7.
- 637 operations, degree34378296, prior round7.
- 659 operations, degree21111400, Selective Quadratic.

In particular Selective Quadratic's ten-integer point dominates the old
round7 degree-oriented689 /33202776 point. Its nine-positive result has
the best reviewed degree but not the best cost. These are finite-catalogue
Pareto comparisons, not assertions of worldwide or global optimality.

The prior11-positive113 /954 beats the peer115 /954 and all reviewed
other11-positive main points on these two metrics. Distinct historical
moderate-degree, higher-variable points should still be retained when
variable count is allowed to increase. The new66 /157 result is a genuine
one-gate improvement over the historical67 /155 scalar operation record,
at a cost of two degrees, subject to its ordinary mathematical proof.

## Highest-value synthesis directions

1. **Replace the carry threshold, not merely the target labels.**
   Selective Quadratic proves that with binary block size L=2^u and
   S+T<L, the two-block word has popcount
   `u+popcount(T)+1-carry_count(S,T)`. The tested central-binomial
   threshold is therefore `2^(u+popcount(T)+1)`, much smaller than a
   uniform block-size threshold. Its Jones calibration chooses L with an
   existing b factor so this exponent is even and its square root remains
   a polynomial. Compose this with the strongest sparse source rather
   than importing its weaker weight/target instance unchanged.

2. **Use sparse target padding and allow signed borrows explicitly.**
   The source `2(1+g)^2 D + sum B^target` has signed formal digits.
   With coefficients strictly below B/4, every incoming borrow is -1 or0.
   At a target, a normalized digit avoids B-2 exactly when the intended
   residual is zero, regardless of the incoming borrow. This needs both
   D(B)>0 and an unconditional bound before decoding, not an assumption
   that the formal coefficients are nonnegative.

3. **Compose the improved arithmetic separator.**
   Sparse Arithmetic replaces the general ten-integer weights with
   `(1,b,bK)`. A coprimality argument first forces r0 square, including
   an explicit b=1 parity exception. Afterward the Pell remainder
   `(Pn^2-4)K^2+4` and divisibility of the third radicand by4 exclude
   two-root cancellation. This proof is independent of the weaker
   support layout in its own main equation and should be combined with
   the best source/carry wrapper.

4. **Rebind the entire complemented-receiver tuple.**
   The selective archive's local decoder resolves the old factorized
   receiver empty-cell gap. Its B=2^429959 tuple occupies215492 raw bytes,
   versus295388 in round7. `NATIVE_ADAPTER_REVIEW.md` records an ordinary
   proof review and independent finite reconstruction. The source archive
   does not compose it into its main equations. A new composition must
   replace all four ports and regenerate every fixed derived leaf.

5. **Combine two independent short-circuit savings.**
   The squared-modulus substitution is a pullback
   `P66(T)=P67(fT)`, with a constructive converse rebuilding both T and
   the auxiliary Pell ordinate using the authentic phase R=3 mod4.
   The selective archive independently replaces three unit-norm residual
   squares by their minimum-sum equality. Composing these suggests a
   degree68 /73-operation15-positive point, not just choosing between
   their separate74-operation points. The new composition needs its own
   explicit graph and degree/zero-equivalence checks.

6. **Keep the Sun-free alternative distinct.**
   Selective Quadratic seeds the positivity guard with an existing
   radicand, reducing a three-root Jones norm to two roots and giving a
   13-integer companion without Sun2026. It is not a10-integer theorem
   and should not be blended into the Sun-based variable-count claim.

## Independent checks completed here

`check_literal_ledgers.py` parses inert JSON and rederives liveness and
paid gate counts for133 actual circuit files across all eight arrivals.
It finds no dead paid gate and no discrepancy with supplied gate counts.
The file `LITERAL_LEDGER_CHECKS.json` makes clear that its naive degree
walk is only an upper bound; it does not certify cancellation-sensitive
exact-degree claims.

`check_separated_tuple.py` reconstructs the complete native tuple directly
from declarative formulas and the inert430-action table. It verifies37960
basis identities,1479 occupied decodings,65076 single-bit mutations,
all131072 empty payloads, the exact942 admissible tile language, carry
and support conditions, populations, four raw payloads, and the actual
rank-controller residues. See `SEPARATED_TUPLE_CHECKS.json`.

## Errors, cautions and nonclaims

No mathematical error has been established in the reviewed new local
arguments. All eight are ordinary mathematical proposals with finite
artifacts, not new end-to-end proof-assistant certificates of the explicit
native compiler. Their unbounded compiler, Jones/Pell or Sun, and K215
calibration dependencies remain imported. Finite arithmetic success
does not decide consistency or prove those unbounded dependencies.

Source31 and source45 differ in the transport row: the shifted difference
is `-beta*(x_J+1)`. They have closely related supports, but a finalizer
cannot silently exchange their residual lists or coefficient recipes.
Every new composition must identify its exact parent and bridge contract.

The two-block lemma requires S+T<L, not just S<L and T<L. Sparse positivity
and this bound must hold before the reverse arithmetic bridge has
established a binary base. Constant factors in L change the exact
popcount threshold. Jones's square-root threshold N need not equal L;
confusing them changes the polynomial.

The higher-majorant auxiliary certificate evaluates D^16 times its primary
equation. Counting certificate operations or reporting its degree as the
primary degree is incorrect. The source itself states this distinction.

The squared-modulus quotient is an existence reduction, not an equality
of arbitrary old and new witness sets. No claim that every old T is
divisible by f is valid or needed; completeness chooses a fresh Pell
ordinate and quotient. Its R=3 mod4 phase comes from the authentic compiler,
not from four arbitrary fixed integer parameters.

Several readmes say the67-operation scalar remains unbeaten. Those are
comparisons against their common pre-arrival baseline, not an up-to-date
comparison across all eight new ZIPs; the same wave contains the66-gate
construction. This is a catalogue/comparison issue, not a mathematical
contradiction in the local proofs.
