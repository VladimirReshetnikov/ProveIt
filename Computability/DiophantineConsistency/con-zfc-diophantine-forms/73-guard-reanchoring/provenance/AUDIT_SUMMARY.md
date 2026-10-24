# Independent repository audit at 9cca523d9f27ad39d52993f4065cbd7e58f8bdd4

This is a source review, not a fresh Lean build or a complete replay of every package.

## Important baseline correction

The collection README still summarizes waves 5--8. Wave 9 is already present in sources 60--67 and changes the frontier materially. Active research README/STATUS are more careful about proof scope than the collection's headline: the closed executable Lean nine-natural equation has no compiler hypothesis, but its numerical coefficients are not materialized. The compact paper circuits have ordinary proofs with explicit inherited native compiler and calibration dependencies. The internal object-language ZFC derivation is still open.

## Wave-9 measured points

| Domain | Unknowns | Degree | Operations | Source |
|---|---:|---:|---:|---|
| Positive | 9 | 1,845,940 | 444 | 66/nine/generated/H2082_simple_positive.json |
| Positive | 9 | 1,834,516 | 449 | 66/nine/generated/H2068_simple_positive.json |
| Positive | 9 | 1,825,540 | 451 | 66/nine/generated/H2057_simple_positive.json |
| Positive | 9 | 1,738,228 | 457 | 65 cheaper shared-target variant |
| Positive | 9 | 1,675,396 | 458 | 65 primary |
| Positive | 9 | 1,520,178 | 476 | 66 refined H2082 |
| Positive | 9 | 1,510,770 | 481 | 66 refined H2068 |
| Positive | 9 | 1,503,378 | 483 | 66 refined H2057 |
| Positive | 9 | 1,494,006 | 487 | 67 lower-degree alternative |
| Integer | 10 | 3,547,076 | 490 | 66/integer/alternative_low_cost/generated/integer10.json |
| Integer | 10 | 3,507,876 | 494 | 66/integer/generated/integer10.json |
| Integer | 10 | 3,327,556 | 519 | 67 signed108trim |
| Positive | 12 | 118 | 104 | 61 p12 product |
| Positive | 12 | 172 | 103 | 61 p12 SOS |
| Positive | 13 | 34 | 93 | 61 p13 |
| Positive | 13 | 114 | 83 | 62 positive13 |
| Positive | 14 | 26 | 92 | 65 p14 |
| Positive | 14 | 30 | 83 | 64 positive14 |
| Positive | 15 | 24 | 88 | 66 algebra |
| Positive | 15 | 26 | 87 | 66 algebra |
| Positive | 15 | 30 | 78 | 66 algebra |
| Integer | 41 | 4 | not optimized | 64 integer41 |
| Integer | 35 | 6 | not optimized | 62 quartic42/companions |
| Integer | 30 | 8 | not optimized | 62 quartic42/companions |

The 66-operation / degree-157 / fifteen-positive form remains the operation incumbent. No package lowers nine positive or ten unrestricted unknowns.

## Q41 mathematical review

I read source64 PROOF41 and PROOF44, their literal quartic41 JSON, source36 ODD_SCALE_27_PROOF and SIGNED_DOMAIN_29, the ordinary strong-rank proof in PELL_RELAXED_AUXILIARY_PROOF, and the auxiliary plus-stepdown proof in EXPLORATION_FIXED_MINUS_INDEX_PARITY.

No error was found in Q41's new argument relative to those inherited interfaces:

1. F alpha>0 and F C>0 force the three summands F,alpha,C of q to have the same nonzero sign. This permits the absolute-radix bound q(q²-1)<R<q⁴-2 with q replaced by Q=|q|.
2. The global guard X=2u² and the main norm exclude X=0 before any rank argument. X=4 q w_scale then gives X>=4Q and |E|>=4Q⁴>3R+1.
3. For eta,zeta both negative, k=-K, K=2 psi_(2XY²+1)(n), and k=R+1+hE imply n>R. Absolute main coordinates give p>n. Growth establishes the relaxed strong-rank and half-modulus hypotheses before rank recovery.
4. The signed auxiliary congruences V=-c mod f and V=-R mod c recover p=R regardless of c's sign, contradiction.
5. With eta,zeta positive, the inherited signed-scale proof can replace its q-based numerical bounds by Q=|q| without importing q's sign prematurely. It first establishes Y>0 and X=2^R.
6. Only then q|2^R and q=1 mod(2^d-1) exclude q=-2^t, using -2^t !=1 mod(2^d-1) for d>=3.
7. Canonical completeness uses q=2^t, t odd, R odd and R>t. Thus w_source=2^(R-t) is divisible by4, so w_scale exists.
8. The correct source transport is (K0+4w_scale)C=F+z(q-1), with z>0. The older unshifted positive source coordinate is z+1.

This does not reprove the native computation compiler from first principles and does not upgrade its ordinary proof to an object-ZFC derivation.

## Composition with source62 does not automatically save an extra variable

Applying source62's favorable sextic transformations to Q41 removes six coordinates (P after a tau gap, F2, g, X, N, C2), giving 35 variables. Its source42 removes an additional w through w=4u², giving the same 35 count. Q41 has no such monic w_scale definition.

Likewise the best literal source62-style octic elimination removes eleven coordinates from41, giving30. Source42 removes twelve, also giving30. The initial one-variable saving is exactly consumed by the absent monic w definition.

Shifting L=q²-1 to S=q² does not itself lower dimension. Eliminating L in the quartic makes qL and FL cubic; thus a claimed quartic40 needs an additional algebraic idea.

## Minimal explicit coefficient recipe for Q41

Source64 integer41/build_verify44.py contains a self-contained finite constructor (function build_coefficients) using only:

- source34/coefficients/wang943_tiles.json (12,551 bytes; Git blob a57902a6862352727fd925be406fa76371dd7edb);
- source34/coefficients/payloads/COEFFICIENT_BINDING.json (Git blob 523be4c527520a1225751feaf5d3f46fc1621d38);
- the constants b=121,L=8801,d=1064921 and displayed shifts/weights.

It regenerates beta,K,MC,MF_source, matches the authentic hashes, and checks MC%4=2, MF_native%8=4, total population d, and the mask intervals. This avoids any need to download binary payloads, but retaining the full native semantics requires the identified source proofs and machine calibration.

The exact nine source mappings are in audit/64-structural-reductions_integer41_SOURCE_PINS.json. The mapped source bytes are available in audit/upstream/.

Recommended mathematical dependency documents to retain:
- 64-structural-reductions/integer41/PROOF41.md and PROOF44.md;
- 36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md;
- 36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md;
- 36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md;
- 34-integer14/coefficients/COEFFICIENT_PROOF.md;
- Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md;
- Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md;
- Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md.

The current formal progress document NATIVE_PELL_STEP_DOWN.md explicitly matches the signed minus-form auxiliary interface used here, and says its main-index bootstrap/native calibration remain caller obligations.

## Positive-carrier composition

Source61's first transport carrier gives q³|Y and C>0 before rank recovery. Source65's smaller nested main carrier can therefore replace source61's q⁵ carrier, provided the earlier bootstrap is rechecked (for example X=x+q). This yields a plausible thirteen-positive degree30 form and twelve-positive product degree114 form. The algebraic_compression worker is pursuing the stronger q²Y version; no independent final equation claim is made in this audit.

