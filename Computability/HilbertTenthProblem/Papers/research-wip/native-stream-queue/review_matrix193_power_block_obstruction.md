# Independent bounded cross-read: matrix193 power blocks

**PASS, with no requested author change.** I read the complete new helper and companion, authenticated their receipt and three predecessor pins, and read the complete `group_directed_semigroup193.md` finite-input/word-interface proof. This review preserves its inherited free-basis and finite-tape U15 universality dependencies; it does not independently reprove the U15 compiler.

The reviewed `matrix193_power_block_obstruction` files are frozen at:

| Extension | SHA-256 |
| --- | --- |
| `.py` | `a6c77d2625d760d5435723c9124eb187201c17c378e386ad62faf3c0cf351fc9` |
| `.json` | `16985a6eac0ff6df74cfc2a141e24d150f581134e547916d1a5eaace3fd8fc34` |
| `.md` | `60f442caa77c68f11c73a4995fbebc4582a0ef64b3a9e41dfd68c27d8782d978` |

The predecessor directory is `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`. Its checked pins are `group_directed_semigroup193.json` = `c802f1ca0fde3cfcc856dd0f14ea2bf6270e1a9a924fe9743ee00c4336891639`, `group_directed_semigroup193.md` = `75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e`, and `review_incoming_matrix_grill.md` = `14c0c3042558b212db8ee5885338f9a7af983d57a702f0c7af2b3d352a657cb8`. The last is authenticated provenance, not a newly repeated complete intake review.

I reconstructed each generator using the closed formula `E_j=(1+4j,2;-8j²,1−4j)` and separate flat 2-by-2 arithmetic, rather than the author's free-word evaluator. All 193 full matrices, hence 3,088 entries, match. Both inverse order and the lower `P^-1 E_i^-1 P` conjugation agree. The terminal remains `[J1]` and the ordinary finite input spelling remains `[reverse(ell) A0 r]`.

The unary target calculation independently gives the four displayed constant/slope pairs. Expansion of the eight actual rows verifies 4M+4A, closure, liveness, and exact degree one; the determinant's three coefficients are `(1,0,0)`. Binary exponentiation checks the target at 13 signed exponents `−17,−2,−1,0,1,2,3,7,16,31,64,128,257`; the ten nonnegative cases also match literal repeated-letter words. The exact nilpotence calculation, not these samples, establishes the all-integer affine identity. The lower block is fixed P. The eight-gate count correctly presumes fixed signed coefficients and is not a complete membership certificate or an optimality claim.

The decision proof has the required order protection: distinct exponent-occurrence letters restricted to `a1* ... ak* #` give one word per exponent vector. A finite-control pushdown construction inserts each fixed inter-block word exactly once, including across empty blocks, and freely reduces on its stack. Constructive Parikh semilinearity therefore gives the exact projected solution set. Intersecting the two free-group projections, further equations and shared-variable equalities is effective Presburger arithmetic. I checked the cited statement of [Esparza–Ganty–Kiefer–Luttenberger, Theorem 1.1](https://arxiv.org/pdf/1006.3825), and [Lohrey, Section 5 and Theorem 8.1](https://arxiv.org/pdf/1807.06774); they support the imported effective semilinearity step. I did not audit those papers' complete proofs or reproduce a semilinear-decision implementation.

Consequently, a total computable bound on powered-block patterns sufficient for every accepted finite U15 input would decide the inherited undecidable relation, as claimed. For a fixed finite template family on the unary slice, treating x as another exponent of the known fixed letter gives a semilinear set of accepted x, hence ultimate periodicity. Input-dependent template families only yield decidability. These statements require known word coordinates for targets and constants; they do not supply a decoder for arbitrary integer matrices. Nonlinear exponent relations and witness-dependent bases are correctly outside scope. Universality of `[1^x A0]` remains unproved, so the conditional C+8 discussion gives no new universal operation bound.

The separate portable [review helper](review_matrix193_power_block_obstruction.py) has SHA-256 `6df9c0ccb5476349ba875b9e29635cb7d98ac17f6e20174761bc209ac26c2bdd`; its [receipt](review_matrix193_power_block_obstruction.json) has SHA-256 `1882e6624df11481ac7fb5eb0c209df8180c0e51f41ab20f5730f91c3958be44`. It uses only Python's standard library, reads pinned author and predecessor data, and compares receipts recursively with exact JSON types. It authenticates the author receipt's self-source hash. This is a bounded research CLI, not a general matrix compiler or hostile-packet API.

After installation beside the author and predecessor packets, run from any working directory:

```sh
python3 /absolute/path/native-stream-queue/review_matrix193_power_block_obstruction.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/native-stream-queue/review_matrix193_power_block_obstruction.json
```

The mutually exclusive `--output FILE` writes a new receipt. `--author-root DIRECTORY` optionally supplies an explicitly pinned staging directory for the author trio; it does not change predecessor lookup under `--root` or any expected hash. Fresh normal and optimized exact-receipt replays from `/` passed. No archived or predecessor Python was executed, and no repository or frozen author file was changed.
