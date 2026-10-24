# Wave 11 baseline audit

## Immutable input and audit scope

The repository checkpoint is `2605669a532342f153b13eb6b4a0af4b54f5fa37` (24 October 2026, 00:56:40 UTC). The eight wave-ten originals are authenticated against arrival `9513bd88cefb762dc07e1872be3078d14aca63fe`; their placement is `d79b41884dbb0a2ad292ca6afc4999aca4d80dc8`. `../INCOMING_PINS.json` records archive URL, Git blob, SHA256, byte length and local extraction path. All archive paths were screened for traversal and symlinks before extraction.

All 1,183 entries in the eight release manifests authenticate independently (`MANIFEST_CHECKS.json`). All 144 Python files were parsed; imports, subprocess calls and dynamic-load targets were inspected. No network, package-install, system-shell or arbitrary-code-evaluation operation was found in the replay surface. The only process launches in replay are the listed local Python checkers. Inherited inputs are kept unchanged; changes are confined to clean temporary replay copies.

All fifteen supported root replays pass: eight normal roots and seven optimized roots. The signed-bootstrap root intentionally rejects `-O` and instead runs its own selected optimized phases. All original trees remained byte-identical. `REPLAY_RESULTS.json` and the corresponding stdout/stderr files give exact commands and hashes. These are finite algebra/data/reproducibility checks, not a new Lean build, universal correctness theorem, consistency test or internal-ZFC derivation.

A separately written reader checks topology, complete liveness, witness declarations and charged binary operation counts for 21 primary literal circuits (`FRONTIER_COUNTS.json`). Degree values in that receipt are released metadata covered by the source replays, not new independent degree proofs. Scalar multiplication and squaring each count one multiplication; fixed numeral leaves and register reuse are free. A named register is not an extra quantified variable.

## Selected frontier entering this iteration

- Unrestricted integers: 38 variables / degree 4, 32 / 6, and 27 / 8, independently in weighted-cone source 69 and determinant source 71. These are distinct polynomials, not duplicate encodings. Source 68 supplies 26 / 16 and ten integers / degree 1,576,864 / 481 operations.
- Eleven positive integers: source 70, degree 325 / 113 operations.
- Twelve positive integers: source 69, degree 82 / 102 operations; source 74, degree 110 / 100 operations or SOS degree 164 / 99 operations. The 82/102 point dominates source 70's 84/103. The centered source-74 forms dominate the corresponding source-71/73/75 points.
- Thirteen positive integers: source 72, degree 28 / 98 operations; source 73, degree 30 / 92 operations. Source 74's 30/93 is the same polynomial with one extra gate. Source 70/75's 30/94 is another polynomial, dominated in these metrics.
- Fourteen positive integers: source 72, degree 24 / 101 operations.
- Nine positive integers: source 71, degree 1,379,730 / 478 operations is the lower-degree alternative. The repository's compact54-sharp H2082 candidate remains the lower-cost target, degree 1,845,940 / 443 operations (450 on natural coordinates). Their degrees, coefficients and costs trade off.

This is a selected comparison, not a full historical Pareto set or global optimality result. In particular, earlier 12-positive degree258/89 and 15-positive degree157/66 forms remain relevant to cost. Natural and strictly positive domains are not interchangeable without an explicit translation. None of the nine-positive entries gives a nine-integer result.

## Mechanisms and compatible combinations

1. **Joint positivity (68).** The nearest-square lemma `x,y>0 iff exists t: xy-(t^2-x-y+1)^2>0` replaces two ternary positivity guards by one such guard plus one new square witness. Its nested variant trades degree for a 26-integer endpoint. The free-Lucas reduction to ten integers uses a special congruence slice and a new fixed-residue orientation lemma; it is not an unrestricted deletion of the old Lucas divisibility condition. Its local commutative certificate and branch relations are not completed global consistency polynomials.

2. **Weighted cone (69).** The three signed quantities `beta*F`, `Walpha*alpha`, `WC*C` are forced into a common strict sign by `2(xy+xz+yz)-x^2-y^2-z^2>0`. Completeness constructs canonical native witnesses inside a factor-two box. The weights are `Walpha=2*T*rho^3296`, `WC=T*beta`, `T=K0-beta*rho+1`, `rho=2^121`. This uses the whole source34 tuple, not arbitrary ports. Its six payloads require 881,696 raw bytes versus 532,479 for the four-port parent. The rational Pell merger separately uses the compact44 tuple and a genuine adjacent-coefficient rational-integrality descent, not just a formal resultant identity.

3. **Residue orientation and root transfer (70).** After signed Pell classification and odd-index recovery, `X=3*X3-1` selects the positive power of two and removes its private square witness. An alternate restriction preserves monic elimination. Canonical completeness is required, rather than coordinatewise preservation of all old zeros. Its eleven-positive root transfer uses a three-root norm and an explicit denominator exclusion: pairwise distinct radicands, a nonzero signed sum, and coprimality between the root denominator and a strong multiplier. These are reusable proof obligations for any further merger.

4. **Determinant (71).** `U*V-(q-U-V)^2>0` forces `q,F,C,alpha` to have a common strict sign. Canonical leading-block bounds are `q/2<=U<4q/5` and `q/2<=V<3q/5`. It shares 24 of 25 quartic rows with source 69 but has different weights and guard. Its six payloads use 615,883 raw bytes, smaller than source 69, but not the 295,388-byte compact44 tuple. The exact pure-J^4 coefficient has 6,924,100 bits, a lower bound on maximum expanded coefficient height, not the maximum itself. The nine-positive form combines the shared-taps source, earlier majorant, and a power rewrite.

5. **Congruence and reanchoring (72/73).** Source 72 first recovers the congruence of q from integrality of the normalized strong root, then uses the adaptive main modulus and retained divisibility by q. A possible gcd factor three is preserved in the argument. Reanchoring changes equivalent common-sign products to permit monic coordinate projection. Its compact sextic has a separately checked whole-tuple adapter; replacing source34 with compact44 is not justified by matching a few size inequalities.

6. **Centered gaps and signed bootstrap (74/75).** Centering reduces norm degrees but must handle a zero denominator separately and prove only the positivity needed for canonical completeness. Source 75's signed-power proof removes the square witness after classifying both signs, excluding negative q through the fixed Mersenne congruence and recovering an integer transport quotient. Thus a combination with a cone/determinant guard requires checking the exact common-sign premise and canonical completeness simultaneously. Equal endpoint counts alone do not establish composability.

All three guard families 68/69/71 use related quadratic-form geometry. The idea is already present in this intake and should not be advertised as a new discovery of this iteration. The incoming root-transfer, Pell-descent and signed-power arguments may nevertheless be combined into genuinely new literal equations, provided restoration and the common canonical family are proved.

## Formal state at the checkpoint

The repository has materially advanced beyond the previous wave-ten report:

- The actual H2082 443/450 circuits are bound in Lean to their coherent polynomial/source recipe. Their degree bound `<=1,845,940` is kernel checked; the exact-degree lower bound is still a finite audit.
- Native source arithmetic now includes exact main/first index, binary scale, half-binomial/mask recovery, sparse assignment extraction and exact local clause bands from all 1,045 stencil terms. It does not yet complete whole-payload high-mask/K binding, phase synchronization, global finite tableau interpretation or native completeness.
- `AnnotatedRefutationPR.exists_refutation_iff` supplies an actual closed unary numeric checker accepting some raw certificate iff the original sealed theory proves false. Its source-program tree counts are 83,281 raw and 76,313 after certified optimization. These are not Diophantine variable or operation counts. No gigantic compiled graph is claimed to have been materialized.
- Internal omega arithmetic is now a checked semiring, and the literal pairing, predecessor, tree-projection and zero-test quartics have arbitrary-model semantics. The residual-square conjunction and literal tree-to-quartic compiler have actual sealed-ZFC derivations.
- The full checker interpretation for arbitrary nonstandard internal syntax/proof codes remains open. The final object-language biconditional between `ObjectCodeSeal.consistencySentence` and `ObjectEquation.unsolvabilitySentence` remains open. External no-zero equivalences, even unconditional ones, do not close this internal obligation.

`FORMAL_SOURCE_PINS.json` authenticates eighteen selected source documents to their Git blobs. This review reads pinned source documentation and does not independently rebuild Lean. Historical status paragraphs inside the incoming archives must not be mistaken for the current checkpoint.

## Reproduction

Run `python baseline/check_manifests.py`, `python baseline/count_frontier.py`, and `python baseline/replay_archives.py` from a release tree containing the eight original extracts. The latter regenerates receipts in `baseline/` and temporary copies only. To recover the originals from public immutable URLs, `baseline/fetch_archives.py` authenticates them before extraction; this downloader is separate from the offline checks.
