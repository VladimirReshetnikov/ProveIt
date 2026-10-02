# Independent review of the complete U15 packed two-tape compiler

Result: **PASS, no unresolved finding** on the frozen 653-operation baseline. This is a complete, fixed-arity alternative to the 744-operation GPCP history route, with an explicitly paid ordinary input loader. It is not claimed to improve the established global bound of 87, nor every other explicit U15-related route.

Reviewed source: `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/u15_packed_two_tape_history.py`, SHA-256 `ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318`. Reviewed loader: `u15_raw_half_tape_loader.py`, SHA-256 `90b5cdf912b34b57cebe6a1b9c9bd3d5bcfd44c234c80e4d3ae774f8d696ce00`. The complete imported AND descriptor is authenticated by `d8bc3b92ac1a6715f9afc6df8957b9ef69bcfc2025848be824bae3724c637f49`.

## Proof audit

The natural/positive input contract is used in the required order. Positive edge hats make every decoded edge word nonnegative and give the computed identity J=sum E_i. D=L0+R0+height is positive, B=64D is at least64, and P=(B-1)J+1 is positive before any equation. The retained aggregate bound makes J positive and bounds all five supplied tape/selected words by P. Since S<=J before instruction typing, BU=S+P gives U<=J<P without assuming that U has Boolean digits. Every displayed joined input/output chunk is therefore below P before the AND theorem is invoked. All imported ports are positive after their mathematical +1 shifts. This prevents a circular appeal to already typed AND lanes.

The prescribed-scale native theorem then implies B*P^34 is dyadic. Its positive integer factors B and P are dyadic. Divisibility B-1 | P-1 gives P=B^t and J=(P-1)/(B-1), for a single t>=1. The 29 controller lanes type E_i as subsets of J. Their computed sum is J and 29<B, so coefficient induction gives exactly one actual instruction per time cell. This pays the controller and duration without an external horizon, oracle, or second geometry kernel.

The two copied range lanes force every tape digit below D; the three selection lanes give dL, dR and dr. These range lanes are necessary for the coefficient-two recurrences: merely bounding tape digits below B permits the explicit invalid-pop alias retained by the checker. The head equation recovers initial bit0, adjacent head bits and final bit1. The state equation gives initial A, correct adjacent states and final J. The two packed tape equalities have constant coefficients of magnitude below2D and interior coefficients of magnitude below4D<B. Integer coefficient induction recovers all local recurrences; the top coefficient forces the exact endpoints without requiring an a priori endpoint bound. The only undefined instruction is J1, so the recovered finite execution is its actual first halt.

The positive rather than hatted history fields preserve completeness. Every real halt ends H0,I1; the last incoming left tape is 2Lf+1, the last incoming right tape is positive, and the final direction/popped bit are both1. Thus H,G,U,ZL,ZR,ZU are positive. The final right tape is also positive because I1 writes1 moving left. For any genuine finite halt one may choose a sufficiently large dyadic D, set the complete histories and take beta=P-H-G-ZL-ZR-ZU>0: each cell sum is at most4(D-1)+1<B. The full existing positive AND converse then supplies its 15 private coordinates. The compiler's genuine-run fixtures intentionally do not materialize these enormous Pell extensions; the proof imports the reviewed uniform theorem.

The specialization from positive virtual hats to raw joined ports is exact off zero. Each original virtual hat has exactly one scaled consumer, and each scaled register has exactly one padded consumer. Replacing the three padded constants gives 16A+12,16M+10,16Z+8 with all 64 native rows and all nine comparisons retained. The independent residual reconstruction retains the actual strong auxiliary expression `(i*c*c)^2*(u*u-y*y)-(1-y*y)`; it never substitutes a norm equality that only holds at a solution.

## Ordinary loader and universality scope

I independently read the full loader source/note, its actual encoding functions, and the ordinary-input universality sections of the retained Neary-Woods interface note. The physical half-tape orientation matches the source encoder: the current head is c, L0 is the reversed program prefix, and R0 is the low-bit-first encoding of the marker/data/tail suffix. The represented recognizer may effectively be chosen to read least-significant input bits first, using the stated swapped pair convention and ignoring trailing zero padding. This choice does not introduce an unpaid bit reversal into the arithmetic interface.

The literal width32 block values, prefix and tail clear to `16711935*R0+program_D=program_A*Q+program_B*z`, with four fixed positive program numerals. The complete 133-gate recoder and five loader gates are preserved. Aliasing L0 directly to program_L removes precisely its identity comparison; the shared positive initial R0 is counted once. The loader's input padding length and the history duration are separate quantities with disjoint private coordinates. Consequently the soundness/completeness composition holds on every effective valid program slice. No universality claim is made for arbitrary positive parameter quadruples.

I did not newly reprove the primary universal-machine simulation or the previously reviewed generic-width recoder/Pell theorem in this bounded review. Their complete existing statements are imported. The new composition, ordinary orientation, exact arithmetic source, and all-value packed-history proof were reviewed.

## Exact source and public API audit

The independent helper establishes 26 formal compositional polynomial identities for the computed geometry, fixed table projections, joined words and all five outer residuals. Register cuts occur only after proving each register definition, so these identities compose. It then checks the complete literal 64-row native source and nine comparison substitution, and the entire 138-row loader prefix plus raw suffix and retained comparison lists. This is a full structural proof of the emitted source composition, supplemented by independent numerical reconstruction; it is not a claim to expand the enormous final multivariate polynomial monomial by monomial.

The public `build`, `checked` and `evaluate` interfaces preserve exact scalar/container types and the declared domains. Every packet field is canonically compared with type sensitivity. Returned nested structures are defensive copies; mutating source or metadata does not poison the private cache. Every source reference is declared before use, every output register is unique, and all emitted gates reach the final polynomial. Products by integer coefficients and program numerals are counted. Signed evaluation is explicit and supplies only an algebraic service; semantic conclusions require the natural/positive domains. Low-level DAG and fixture helpers are outside the documented hostile-input API.

| Interface | Certificate | Comparisons | Positive witnesses | Complete SOS |
|---|---:|---:|---:|---:|
| Natural raw L0,R0 |369=133M+236A|14|54|410=147M+263A|
| Positive ordinary x, fixed program numerals |507=206M+301A|49|105|653=255M+398A|

Each comparison contributes its difference and square, followed by the sum: the finalizer costs3e-1 operations. Independent formal degree propagation gives1936 in both modes, both when fixed program numerals have degree0 and when they are treated formally as degree1. This certifies an upper bound only; the packet correctly makes no exact-degree assertion.

The companion note was read completely through Section8. Its pretyping order, 34 lanes, chronology and first-halt proof, direct positivity argument, ordinary loader composition, operation/witness ledgers, upper-degree qualification and fixture limitations agree with the source. A later state-relabeling optimization is outside this frozen baseline review.

## Fresh independent replay

Portable command (Python with SymPy):

```sh
python /tmp/review_u15_packed_history.py --source /absolute/path/to/u15_packed_two_tape_history.py --receipt /tmp/review_u15_packed_history.json
```

The helper authenticates both source files before importing, refuses optimized Python, and resolves dependencies from the supplied compiler directory. Final receipt status is PASS:

- 26 formal prefix/register/residual identities; complete native and complete ordinary graph substitutions.
- Two complete source/count/closure/liveness audits and four degree-upper-bound propagations.
- 256 independently reconstructed complete residual/SOS cases, including128 signed assignments:14 residuals per raw case and49 per ordinary case.
- 90 malformed assignment/packet/flag rejections and two nested defensive-copy checks.
- 90 literal source-encoder/loader orientation fixtures across three program shapes, ten inputs and three padding choices.
- Four genuine outer first-halt fixtures with positive fields and exact joined AND equality. They are not represented as full native Pell zeros.

These finite checks supplement the all-value proof and inherited uniform extension theorems; they do not establish an arithmetic minimum or exhaust the unbounded witness set.
