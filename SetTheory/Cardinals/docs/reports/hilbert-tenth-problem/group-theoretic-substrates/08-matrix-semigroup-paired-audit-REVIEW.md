# Independent review: bounded paired-matrix Diophantine interface

Status: final review passed. No unresolved mathematical or implementation findings. The final compiler and proof are bound by SHA-256 below.

## Source and execution boundary

The reviewer read the literal `data/semigroup.json` and `PROOF.md` from the fixed source packet. The literal JSON SHA-256 is

`506144b361b2bea634d468a94921644d91868dc089a257fe289a0bf51b74cec9`.

No Python or other executable from the source packet was imported or executed, and no source file was modified. The reproducible literal-data check defaults to this sibling packet's hash-identical `data/semigroup.json`. `audit/source_literal_check.py` is newly authored independent code, in this sibling packet. It passes with normal Python and `python -O`, using explicit exceptions rather than optimization-removable assertions.

The source check verifies all 229 literal matrices against their formulas, all 114 tile associations, integer types, block diagonality, pairwise distinctness, and determinant one using an independent Leibniz expansion. In particular,

- `C_top = [[157,4],[-6712,-171]]`
- `P = [[1,2],[0,1]]`
- maximum absolute entry of any `A_i` upper block is 63,038,000
- maximum absolute entry of any inverse `B_i` upper block is 11,924,776
- maximum absolute row-sum norms of `U`, `V`, and `D` are respectively 64,675,047, 12,234,453, and 6,883
- all 912 entries of the 114 `U` and 114 `V` matrices are nonzero
- the exact coefficient-source JSON size is 117,288 bytes

Results are recorded in `audit/source_literal_check.json`. These checks establish consistency with the source proof and literal data; they are not a new machine-checked proof of the source universality theorem.

## Mathematical interface reviewed

All natural variables range over nonnegative integers, including zero. For fixed `r >= 0`, put one selector `e_(s,i)` for each of 114 tiles at each step. The equation `sum_i e_(s,i)=1` over this domain uniquely selects one tile, with no separate Boolean equations needed.

Each of the eight entries of the two 2-by-2 state matrices `H_s,G_s` is represented by two natural parts `p,n` with signed value `p-n` and residual `p*n`. The condition `p*n=0` makes the parts uniquely determined by the signed integer. Initialize both matrices to the identity. Use the literal `A_i` upper blocks for the `H` recurrence and the inverse literal `B_i` upper blocks for the `G` recurrence, accumulating on the right in forward tile order.

For a tile sequence `i_1,...,i_r`, those recurrences give

`H_r = A_(i_1)^top ... A_(i_r)^top`

and

`G_r = (B_(i_1)^top)^(-1) ... (B_(i_r)^top)^(-1)`.

The reversed `B` order in the paired normal-form word is therefore exactly `G_r^(-1)`. Its upper block is `H_r C_top G_r^(-1)`, so the four terminal residuals from `H_r C_top - T G_r` vanish precisely when the upper block is `T`. The normal-form lower block is `P`, and the complete nonempty semigroup word has length `2r+1`.

The single polynomial is the sum of the squares of the selector, complementarity, recurrence, and terminal residuals. Over integers, its zero set equals the simultaneous zero set of the residuals.

## Counts and degree

For the signed external target `T` with four ordinary integer entries:

- auxiliaries: `r*(114+2*8) = 130r`
- residuals: `r*(1+8+8)+4 = 17r+4`
- total degree: 2 at `r=0`; exactly 4 for every `r>=1`

These degree statements count the external target entries as polynomial variables before target specialization. At `r=0`, fixing the target leaves a constant polynomial in zero auxiliary variables.

The degree-four upper bound follows because every residual has degree at most two. For `r>=1`, a complementarity square contains a monomial `p^2*n^2` with coefficient one, which cannot cancel against any other residual-square contribution to that monomial.

The optional all-natural target replaces four external integer entries with eight external canonical natural parts and adds four target-complementarity residuals. It still has `130r` auxiliaries, but it has `17r+8` residuals and total degree exactly four for every `r>=0`, including `r=0`. Calling this variant degree two at zero would be incorrect.

## Fibers and invalid targets

At a fixed external target, zero fibers are in bijection with the tile sequences of exactly length `r` having paired product `diag(T,P)`. Every such tile sequence has a unique full auxiliary tuple. Two distinct tile sequences are allowed to give the same matrix target. Thus the number of solutions is bounded by `114^r`, without any asserted target uniqueness.

For `r=0`, there are zero auxiliaries. The empty auxiliary tuple is a root exactly when `T=C_top`; the corresponding semigroup product is the single generator `C`, not the empty product.

The recurrence matrices have determinant one, and the terminal equation forces `T=H_r C_top G_r^(-1)`. Consequently every integer target with determinant other than one has no roots, without a separate determinant residual. Invalid dimensions or noninteger encodings are outside the four-integer parameter domain and should be rejected at any software boundary. In the all-natural-target version, a negative part is outside the domain, while two simultaneously positive parts are valid natural inputs but fail the target-complementarity residual.

Taking a union over `r` gives the relevant paired-target semigroup-membership equivalence, by the source marker lemma. This is a family with unbounded arity as `r` grows; it does not give one fixed-arity finitefold representation, nor a unique-witness representation of unbounded membership. Finite verification cannot replace those distinctions.

## Compiler and coverage review

The reviewer inspected `paired_compiler.py` and `tests/check_all.py` directly. The matrix recurrence, terminal indices, inverse order, zero-length specialization, sparse monomial aggregation, natural-variable validation, and CLI certificate reconstruction are consistent with the proof. No theorem-affecting implementation gap was found.

The new independent test program `audit/independent_interface_check.py` passes both normal Python and `python -O`. It uses literal-data generic 4-by-4 products and a separate direct weighted-matrix residual oracle, rather than using the compiler's certificate or sparse-polynomial construction as its correctness oracle. Its coverage is:

- 366 certificate checks against generic literal 4-by-4 products, including every one-tile choice and sequence lengths 0 through 9, in both target modes
- 80 arbitrary non-solution assignments checked residual-by-residual and by SOS value against an independently structured direct matrix oracle
- 10 exact operation-count checks using instrumented integer arithmetic for `r=0,...,4` and both modes
- 791 auxiliary or target tamper checks
- 24 malformed/domain-invalid input rejection checks

Results are in `audit/independent_interface_check.json`. Normal and optimized runs produced identical reports.

The reviewer also independently executed the author's complete test suite under `python -O`, with results in `audit/authored_tests_optimized.json`. It passed, including all 12,996 length-two literal products, both modes' local zero-length target cubes, certificate/target/selector/complementarity mutations, invalid determinant targets, literal export evaluation, and the pinned 94-tile accepting example. The suite finds 12,994 distinct targets at length two and two target collisions, as permitted by the statement. For example, sequences `[20,109]` and `[110,20]` have equal targets and distinct auxiliary tuples; this directly illustrates why target uniqueness is not claimed.

The reviewer separately ran the final CLI verifier on `examples/accepting-94-certificate.json`: its 1,602 residuals all vanish, as recorded in `audit/cli_accepting_94_check.json`. A natural-target zero-length CLI certificate also verifies, with eight residuals; that result is recorded in `audit/cli_r0_natural_check.json`.

### Exact ledger review

For `r>=1`, the signed-target residual monomial histogram by degree 0,1,2 is

`[r, 130r+928, 3656r-3632]`.

The natural-target mode adds 20 quadratic monomials. These are monomials across the residual list, before squaring or expanding the SOS, not an expanded-SOS monomial count. The reported maximum coefficient is likewise a residual coefficient bound, not an expanded-SOS coefficient bound.

Under the documented generic evaluator convention, the signed-target counts for `r>=1` are `11246r-9036` multiplications and `3804r-2700` additions. Natural mode adds 64 multiplications and 24 additions. At `r=0` the signed counts are 16 multiplications and 12 additions; the natural counts are 40 and 24. Instrumented arithmetic confirms these counts without relying on the ledger's counting formula. They exclude parsing, validation, comparisons, dictionary operations, loop control, construction, bit complexity, and optimized evaluation; none of those is silently represented by this arithmetic-operation census.

### Quantitative proof checks and resolved findings

The reviewer checked the expanded-SOS coefficient bound `R*(458*63038000)^2`, the `100r(r+1)+r` canonical-auxiliary magnitude-bit census, the `50r+14` target-entry bit bound, and the arbitrary-assignment residual/SOS growth estimates. The stated asymptotic bit costs are conservative and correctly separate the fixed numerical parameter `r` from its binary encoding length. Prefix, supplied-target, and default-target construction charges are distinguished.

Independent arithmetic instrumentation confirms that the final 2-by-2 multiply uses exactly eight multiplications and four additions per call. A determinant-one inverse uses exactly two multiplications, one subtraction, and two unary negations. Instrumenting the final fixed loader records exactly 572 inverse calls, establishing its stated 1,144 multiplications, 572 subtractions, and 1,144 negations, excluding the separately disclosed nonarithmetic work.

Three issues found during review are resolved:

1. `target_values(target, mode)` now rejects unknown modes itself; a regression case is included in the independent checks
2. The proof explicitly defines degree jointly before specializing the external parameters and gives the correct signed `r=0` evaluator counts, 16 multiplications and 12 additions
3. The matrix multiply helper now uses an explicit two-term formula, so certificate-construction addition charges match the implementation and do not omit additions to an initial zero

These corrections do not change the construction's mathematical zero sets or its variable/residual counts.

### Review boundary

The finite checks support the construction and catch numerous indexing, sign, domain, and bookkeeping mistakes. They cannot prove the absence of roots for all invalid targets or establish general universality, both of which depend on the stated algebraic arguments and the separately identified source theorem. No formal proof assistant was used. The reviewer read the complete final `PROOF.md` and `README.md`; their per-r versus unbounded scope limitations are explicit and correct. All final independent normal/optimized checks refer to the frozen implementation bound below.

## Final version binding

- `paired_compiler.py`: `d40f69194f14da7b8b02095ba77327aaa9b938b13f1d33d29641f24a57df66fd`
- `PROOF.md`: `51fee9e3e720370fb235558215d8f045ce1ce0d0a6a338c4f51505a6e2330899`
- `README.md`: `a3fa763eba8d275a297522a9b3f5cc58e6d8999b7e5aa65dd325830fdd275aae`
- `tests/check_all.py`: `166c1df6d13d5007fd07c1098ca1b833fa516684ea440cdae71997451edb1170`
- coefficient data: the source pin stated above

The independent report also embeds the reviewed compiler hash. Audit scripts and reports are newly authored and modify only this sibling packet. The original source packet remains unchanged.
