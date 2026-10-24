# Pinned baseline review for round 14

## Snapshot and scope

Public repository snapshot: `84e16e43092614bae262ca59651cb9d77e31a255`, main checked 2026-10-24 at about 19:27 UTC. Latest ordinary mathematics incorporated in this snapshot includes commit `bb642c8350d6f8b09e8f04fb18b85a0d5e2cb7af` (75-guard direct quartics, 19:17:28 UTC). The manuscript collection README is intentionally archival and is materially behind the active research.

Primary comparison: [active frontier](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/PROPOSAL_REVIEW_LATEST.md).
[Active README](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/README.md).
[Recent commit](https://github.com/VladimirReshetnikov/ProveIt/commit/bb642c8350d6f8b09e8f04fb18b85a0d5e2cb7af).

Two authoritative supplied Library archives remain ahead of public main in their direct branch: Prime Power 375/553 and Shell Reciprocal 660. Both inspect repository snapshot `ec80841c07e91be8956ce6ed4af9a9c0b782d3d9` and inherit logical calibration at `08200eb10fde2db408c69dffd840d6920a569b1f`. The latest matching Library items found were shell at 04:59:09 UTC and prime-power at 04:48:03 UTC. A narrower post-05:00 search and a second unfiltered title search found no newer matching contributions. This is a bounded search result, not a guarantee about all possible filenames.

## Literal direct quartics

All unknowns independently range over the stated domain. N includes zero. Every polynomial is the fully collected sum of squares of quadratic residuals. Operations have not been normalized or optimized in these packets, so residual count must not be reported as operation count.

| Source | Domain | Variables | Degree | Residuals | Monomials | Exact coefficient height |
|---|---|---:|---:|---:|---:|---:|
| Supplied prime-power | N | 375 | 4 | 294 | 7907 | 4951760157141530951222074278254 |
| Supplied prime-power | Z | 553 | 4 | 348 | 7911 | 534790096971332833190424347930 |
| Supplied reciprocal, old syntax | N | 363 | 4 | 291 | 6674 | 83842716 |
| Supplied reciprocal, shell syntax | N | 364 | 4 | 292 | 6613 | 7002666 |
| Supplied shell, signed | Z | 660 | 4 | 386 | 6408 | 3877579 |
| Current public 75-guard, raw/default | Z | 604 | 4 | 372 | 9676 | 2445790974704 |
| Current public 75-guard, affine support 16 | Z | 609 | 4 | 377 | 8823 | 964213 |

These seven lines were independently verified here, reading JSON as data only: every quadratic residual was expanded and summed, every resulting coefficient compared with the delivered expansion, every variable checked to occur, and degree/support/height recomputed. Audit: `LITERAL_AUDIT.json`; reproducible independent code: `audit_literal_polynomials.py`. No archive or repository script was imported or executed. This validates literal polynomial metrics, not semantic zero/refutation equivalence.

Additional current public tradeoffs (source-reported, not reexpanded here): 399N/8286 monomials/height83843274; 608Z/8739/45769499; 630Z/8850/737653; 837Z/3780/4750; 1484Z/4948/432. The older 1493Z/4981/427 remains a slightly lower-height tradeoff than the newer retained 1484Z/432.

Source for the public 75-guard family:
[README and complete files](https://github.com/VladimirReshetnikov/ProveIt/tree/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/research/factorial-radius-output-sign-profile).

### Honest Pareto conclusions

- The supplied 363N reciprocal equation improves the supplied 375N prime-power equation in variables, residuals, support, and height, at unchanged degree. The 364N shell version has one more variable than 363N but fewer terms and much smaller height.
- The supplied 553Z remains the fewest-variable point among these direct, small-literal-coefficient packages. Its coefficient height is 99 bits, dramatically larger than the 20-bit public 609Z and 22-bit supplied 660Z points.
- Public 609Z beats supplied 660Z on variable count and coefficient height but has more monomials (8823 versus6408), so it does not dominate on all three measures.
- Public 604Z and supplied 553Z trade variables against height. No global simplicity or universal record follows.
- There are much smaller-variable quartics on a different route: the retained determinant construction has 37 unrestricted integer variables and24 residuals, with 31-variable sextic and26-variable octic companions. Their six fixed constants occupy615883 raw bytes; this is payload size, not maximum expanded coefficient height. Thus neither553Z nor604Z is a general fewest-variable quartic record. Source: retained `RESIDUE_AND_DETERMINANT.md` at the link below.

## Small-variable arithmetic-circuit baselines

Arithmetic operations mean live binary addition, subtraction, multiplication, including squaring and scalar multiplication. A named register is not an additional unknown. A dash for coefficient height means no comparable full-expanded height was obtained in this review, not small coefficients.

| Domain | Unknowns | Operations | Exact degree (source proof) | Coefficient-height status |
|---|---:|---:|---:|---|
| Positive integers | 9 |405 /413|1191570 /1316546| Not measured here; different whole tuples |
| Positive integers |10|99|368| Not measured; four compact44 fixed ports |
| Positive integers |10|105|340| Not measured; same compact44 tuple |
| Positive integers |11|111|211| Not measured |
| Positive integers |12|96|70| Not measured |
| Positive integers |13|88|51| Not measured |
| Integers |10|471|1245324| Not measured |
| Integers |10|475 /478 /512|1179788 /1114252 /1080888| Not measured |
| Integers |12|145 /141|1200 /1456| Not measured; source34 six-port tuple |
| Integers |13|135|536| Not measured |
| Integers |14|117|312| Not measured |
| Integers |15|128 /124|204 /352| Not measured |
| Integers |16|119 /132|112 /108| Not measured |
| Integers |17|110|88| Not measured |

The 145- and141-operation twelve-integer counts and105-operation ten-positive count were independently recomputed from the full live DAGs here (`CIRCUIT_AUDIT.json`). For scalar12 the syntactic upper degrees also recompute to1200 and1456. Exact attainment uses the source's nonzero leading-coefficient proof; this audit does not pretend that a syntactic bound alone proves exact degree.

The scalar12 fixed beta has1064921 bits; compact44 beta has590069 bits. These are sizes of fixed supplied constants, NOT the height of the expanded output polynomial. Individual ports must not be mixed between tuples, and MF is already shifted.

Sources:
- [Scalar-carrier12](https://github.com/VladimirReshetnikov/ProveIt/tree/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/candidates/scalar-carrier12).
- [Ten-positive99/368](https://github.com/VladimirReshetnikov/ProveIt/tree/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/candidates/ten-positive-zero-offset).
- [Ten-positive105/340](https://github.com/VladimirReshetnikov/ProveIt/tree/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/candidates/ten-positive-direct-zero-offset).
- [37Z quartic and signed bootstrap](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/candidates/scalar-carrier12/source/RESIDUE_AND_DETERMINANT.md).

## Proof boundaries and rejected lead

The public research explicitly separates an ordinary mathematical proof, a finite literal-algebra audit, and a newly kernel-checked or encoded object-language ZFC derivation. Internal formalization remains open and Lean is paused. No count checker establishes the unbounded Pell, compiler, or consistency calibration. The direct supplied packages name `KEndpoint.c222_iff_zf_refutation` and `ConstructibleChoice.zf_refutation_iff_zfc_refutation`; their ordinary formalizability argument and retained calibration are inherited proof obligations, not facts certified by polynomial expansion.

The shared-projection83 universal proposal is now REFUTED for the original powers-of-five modified75 compiler recipe. The counterexample is a quantified family of positive zeros at unbounded ordinary inputs for a genuine fixed three-state empty-language program. It does not merely exhibit extra witnesses at an accepted input. The result does not refute every83-operation polynomial, other coefficient recipes, or the separate independent-gamma83 proposal. The valid universal operation baseline remains84 operations, degree187,18 positive witnesses. A valid alternative is92 operations, degree325,17 positive witnesses. None of these universal input/witness counts is a fixed-ZFC coefficient-free direct-certificate count.

[Full shared83 rejection](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete83_rejecting_compiler.md).
[Local norm unit guard92](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete92_norm_unit_guard.md).

## Scalar12 dependency chronology checked

A targeted review read the actual retained `signed-quadratic-proof.md` sections2–5, `RESIDUE_AND_DETERMINANT.md` section4, and `INTERPOLATION12.md` section5. The main projection is NOT used in their pre-projection rank/ratio prefix:

1. Strong and auxiliary Pell roots plus the unsquared residue modulo the strong abscissa give absolute folding, hence |c|=psi_|a+2|(p).
2. The determinant and eta*zeta guards give sign-free native packing and the |c|/|k| strip. First Pell classification gives p>n>=24 before projection.
3. c^2 divides I; Lucas strong divisibility and the multiplication formula give p divides m and |c| divides m. This works for an arbitrary nonzero multiplier, not only an odd one.
4. Auxiliary residues force R=plus-or-minus p modulo |c|; the rank bounds force p=R, then R=2r0+1.
5. The sign-uniform ratio gives |H|>2^(2R+2)|X|^2.
6. Only then H divides K makes the entire product (sigma X-2^R)(2^R sigma X+1) vanish, restoring gamma=(d-X-ac)/H.

Thus no local circular use of gamma was found in this inherited prefix. This is not a complete new audit of every transitive native/compiler/calibration proof. In particular the invalid normalization r_old=(Delta*s*r-1)/2 is expressly rejected by INTERPOLATION12; its generalized signed kernel must be used.

## Structural opportunities worth pursuing

- Compose the newer sign-recovery chronology with the reciprocal or prime-power direct syntax instead of only optimizing the old407/888 source. Public75-guard algebra shows C=r+s+1 and fC=N+s imply N=f*r+(f-1)*s+f. Retained f>=2,r,s>=0 recover N>=2 before power/factorial semantics, deleting one redundant guard without a new wire. Any transplant must bind the actual new source rows and prove chronology, not reuse raw coordinate numbers.
- The two direct CRT engines solve different obstructions. Prime-power binomial saturation licenses t! and drastically reduces independent sign seeds, but creates large literal constants. Reciprocal moduli D_i=1+(H!)^2/i yield an exact product binomial and cheaper syntax. A hybrid must reprove pairwise coprimality, row-index lifting, and signed power orientation; counts cannot be combined arithmetically.
- Scalar12 replaces an algebra-valued carrier by the homogeneous intersective quintic Phi_H(z)=(z^2+3H^2)(z^3-19H^3), obtains H|K from valuation dominance, and deletes the main root before projection. Possible further work should respect the full-residue interpolation quantifier order: fix one strong I,f first, then select the auxiliary residue.
- The universal92 local-unit argument uses P5(K+1)=1 and even B in K=A^2-DB^2 to rule out the negative unit modulo4. This is a potentially portable norm-finalizer principle, but the signed-root positivity theorem applies only on its exact positive compiler slice. A blanket transplant to unrestricted scalar12 is not licensed.
