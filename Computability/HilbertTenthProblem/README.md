# Hilbert's tenth problem: Jones's articles on Diophantine representation

Corrected editions and a Lean 4 formalization of six articles on Hilbert's
tenth problem, Diophantine representation of recursively enumerable sets and
universal Diophantine equations by James P. Jones and coauthors:

| Year | Authors | Title | Journal | Engine |
|---|---|---|---|---|
| 1974 | J. P. Jones | Recursive Undecidability—An Exposition | *Amer. Math. Monthly* 81, 724–738 | pdfLaTeX |
| 1976 | J. P. Jones, D. Sato, H. Wada, D. Wiens | Diophantine Representation of the Set of Prime Numbers | *Amer. Math. Monthly* 83, 449–464 | pdfLaTeX |
| 1978 | J. P. Jones | Three Universal Representations of Recursively Enumerable Sets | *J. Symbolic Logic* 43, 335–351 | LuaLaTeX |
| 1980 | J. P. Jones | Undecidable Diophantine Equations | *Bull. Amer. Math. Soc. (N.S.)* 3, 859–862 | pdfLaTeX |
| 1982 | J. P. Jones | Universal Diophantine Equation | *J. Symbolic Logic* 47, 549–571 | XeLaTeX |
| 1984 | J. P. Jones, Yu. V. Matiyasevich | Register Machine Proof of the Theorem on Exponential Diophantine Representation of Enumerable Sets | *J. Symbolic Logic* 49, 818–829 | pdfLaTeX |

## Layout

- [`Papers/`](Papers/README.md): the corrected editions
  (`<year>/jones<year>_corrected.tex` and `.pdf`), each with its consolidated
  editorial notes (`<year>/jones<year>_editorial_notes.md`: every discrepancy
  between a naive OCR reading of the printed article and the edition, with its
  classification and justification), the dated log of revisions and checks
  `EDITORIAL_NOTES.md`, the satellite article on the operation count of the
  1980 Theorem 5 (`1980/jones1980_theorem5_operations.pdf`) with its proofs
  and explorations, and the verification programs in `verification/`.
- [`Lean/`](Lean/README.md): the Lean 4 / Mathlib formalization, the library
  `Diophantine` of the root Lake workspace, with its status register
  [`STATUS.md`](Lean/STATUS.md), the [MRDP guide](Lean/MRDP.md) and the axiom
  audits in `Lean/checks/`.

## Highlights

- **MRDP in both directions.** `Diophantine.mrdp`: every recursively
  enumerable set of naturals is the projection of the natural zero set of one
  integer polynomial with finitely many witnesses, including input zero;
  `Diophantine.mrdp_iff` proves the converse, and `Diophantine.mrdp_dioph_iff`
  states it through Mathlib's `Dioph`.
- **The universal pair `(58, 4)`** of the 1980 and 1982 articles on positive
  inputs, from the complete (D1)–(D37) system of 1982 §5; the three printed
  1982 systems represent every r.e. set with 12, 14 and 28 positive witnesses.
- **Prime-representing polynomials** of 1976: an integer polynomial on twelve
  natural coordinates whose positive values are exactly the primes, and one of
  exact degree 13697; the 87-operation primality certificate.
- The 1974 exposition (Busy Beaver functions on ProveIt's machine model), the
  1978 Bounded Quantifier Theorem and Divisor Lemma, and the 1984
  register-machine encoding.
- The formalization introduces no axioms and no `sorry`; transitive axiom
  audits are in `Lean/checks/`. Coverage per article and the statements still
  open are in [`Lean/STATUS.md`](Lean/STATUS.md).
- The editorial review found and corrected errors in the printed articles;
  every correction is justified in the per-article notes.
- The smallest established complete universal straight-line certificate
  (satellite work on the 1980 Theorem 5) uses **75 operations (41 multiplications and34 additions/subtractions)**,
  with30 positive witnesses and19 equations; see
  [the complete proof](Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md).
  Three independent integration reviews and focused source/component checks
  pass. The [signed-projection refinement](Papers/research-wip/native-stream-queue/complete75_signed_projection_elimination101.md)
  retains75 operations with **20 positive witnesses and nine equations**.
  Its degree-84 polynomial is evaluable in **101=50M+51A operations**, with
  fixed compiler numerals and ordinary input. Conditional positivity is
  proved on the zero set; every original positive solution is preserved.
  The newer [bounded-projection polynomial](Papers/research-wip/native-stream-queue/complete75_bounded_projection_elimination99.md)
  costs **99=49M+50A**, with **19 positive witnesses** and degree84.
  Its comparison system costs76 with eight equations; a proved canonical
  compiler margin preserves the same accepted ordinary inputs.
  The [positive Pell-root coordinate](Papers/research-wip/native-stream-queue/complete75_positive_root89.md)
  gives **89=47M+42A**, with the same19 positive witnesses and exact
  degree148. It is bijective on positive solutions with the
  [reversed auxiliary degree160 source](Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md).
  Integer unit obstructions, displaced Pell indices and the new root-gap
  positivity proof justify the unsquared product. Its comparison circuit costs88.
  The [positive-root partitions](Papers/research-wip/native-stream-queue/complete75_positive_root_degree_tradeoffs.md)
  give **94 operations at degree84**, **93 at degree118**, and **92 at degree122**.
  In particular the degree84 option improves its preceding96-operation bound.
  The [coupled index/linear product](Papers/research-wip/native-stream-queue/complete75_coupled_index_linear88.md)
  now gives **88=47M+41A**, with **19 positive witnesses** and exact degree151.
  Sharing k-hE removes one subtraction; the compiler masks exclude the
  remaining negative sign through a population-count contradiction.
  Its positive zero set equals the89 source's under the full compiler contract.
  Its [grouped variants](Papers/research-wip/native-stream-queue/complete75_coupled88_degree_tradeoffs.md)
  give **91 operations at degree130** and **93 at degree90**, retaining the
  full strong equation and the same positive zero set. The93/90 option
  supersedes93/118. The [linear input modulus](Papers/research-wip/native-stream-queue/complete75_linear_input_modulus89.md)
  gives **89=47M+42A at degree135**, with a proved positive coordinate map
  to the discriminant-modulus construction. Its [degree tradeoffs](Papers/research-wip/native-stream-queue/complete75_linear_input_degree_tradeoffs.md)
  give **90/132,92/114,94/80,95/72,96/62 and97/56**; all retain19 positive
  witnesses. The [positive auxiliary-gap coordinate](Papers/research-wip/native-stream-queue/complete75_auxiliary_gap_degree_tradeoffs.md)
  further gives **90/131,91/128,98/54 and99/52** with the same witness count.
  The75 comparison bound and88 polynomial bound remain distinct.
  These optimized results are not yet Lean formalized.
- A [group-commutator substrate](Papers/research-wip/native-stream-queue/group_commutator_universal_substrate.md)
  represents every computably enumerable positive set by membership in a
  finitely generated SL(4,Z) subgroup, with a fixed quadratic ordinary-input
  curve costing five scalar operations. One fixed universal subgroup serves
  all programs with a six-operation program/input loader. The group embedding
  theorem is cited explicitly. The [complete matrix compiler](Papers/research-wip/native-stream-queue/group_complete_matrix_compiler.md)
  now pays every history, selection, control and duration predicate. It
  composes canonical history47, prescribed selected-source119, a regular
  macro controller and a47-operation repunit-population geometry kernel.
  For m=2^h fixed controller edges and p selector additions, its certificate
  costs **7m+3h+p+273**, with60 equations and m+87 positive witnesses.
  One polynomial costs **7m+3h+p+452**, of exact degree **max(112,12m+16)**.
  This is complete for a fixed macro table and yields an alternative
  universal construction through the fixed subgroup theorem. The universal
  alphabet has not been numerically instantiated; the75/88 numerical
  frontiers are unchanged.
  Its [computed-port successor](Papers/research-wip/native-stream-queue/group_computed_selector_ports.md)
  combines one shared typing kernel, sparse state flow and common powers,
  then eliminates the eight positive selector coordinates. Its certificate
  costs **C=3m+3h+p+222+f_flow-3min(h,3)**, with39 equations and m+59
  positive witnesses, where f_flow is at most twice the total macro length.
  The polynomial costs **C+116**, of exact degree **12m+112**.
- A [seven-dimensional Gram/mortality interface](Papers/research-wip/native-stream-queue/group_gram_zero_mortality.md)
  represents universal membership by a scalar zero using a12-operation
  positive input column, or by mortality with one nonnegative input matrix
  loaded in **13=5M+8A**. All other generators are fixed. A fixed-word
  polynomial has degree8; a uniform selected-word certificate remains open.
- The [projective endpoint](Papers/research-wip/native-stream-queue/group_projective_zero_mortality6.md)
  replaces matrix equality by an affine vector-action query. Its6D scalar
  and mortality input matrix costs **3=2M+1A**. The
  [range-typed compiler](Papers/research-wip/native-stream-queue/group_range_projective_compiler.md)
  pays the uniform vector histories with one AND kernel, removing the
  separate duration-height kernel. Its certificate costs
  **C=3m+3h+p+185+f_flow-3min(h,3)**. The
  [computed-kernel refinement](Papers/research-wip/native-stream-queue/group_projective_computed_kernel_fields.md)
  gives20 equations,m+34 positive witnesses and a **C+59** polynomial of
  degree24m+444. A degree12m+232 alternative uses22 equations,m+36 witnesses
  andC+65 operations. The fixed universal table is still uninstantiated.
  The [padded-program successor](Papers/research-wip/native-stream-queue/group_projective_padded_program_margin.md)
  combines a reflected boundary, a norm/checksum product and scalar
  projections. With controller-mask reuse and computed P, it gives
  **3m+3h+p+228+f_flow-3min(h,3)** polynomial operations,15 equations and
  m+31 positive witnesses, at degree136m+798. This requires m>=8 and a
  fixed numeral margin supplied by an explicit padded universal enumeration.
  Some lower-degree alternatives retain additional equations. The illustrative
  ten-letter table costs302; it is not a numerical universal alphabet.
  The [joint-bound and first-root composition](Papers/research-wip/native-stream-queue/group_projective_joint_first_norm.md)
  saves five more polynomial operations and one witness, giving
  **3m+3h+p+223+f_flow-3min(h,3)** operations,13 equations and m+30
  positive witnesses, at degree160m+928 for the same options. The
  illustrative table gives **259 certificate operations or297 polynomial
  operations**, with46 witnesses. A wider radix makes the joint bound
  sound; deleting the output bound is separately proved unsound.
  The [coupled index/linear successor](Papers/research-wip/native-stream-queue/group_projective_coupled_linear_unit.md)
  saves another three additions: **3m+3h+p+220+f_flow-3min(h,3)** polynomial
  operations,11 equations,m+30 witnesses and degree164m+920 for those
  same options. The illustrative table reaches **262/294 operations**
  with46 witnesses. Its extra native sign branch restores positive
  witnesses for the same ordinary input; the numerical75/88 bounds remain.
  Computing the [two input fields](Papers/research-wip/native-stream-queue/group_projective_computed_input_fields.md)
  and [checksum field](Papers/research-wip/native-stream-queue/group_projective_computed_checksum_field.md)
  then saves seven polynomial operations and three witnesses. Using the
  [retained strong coefficient](Papers/research-wip/native-stream-queue/group_projective_strong_coefficient.md)
  lowers the six-field degree by eight at unchanged cost. At that stage the bound
  for the same options is **3m+3h+p+213+f_flow-3min(h,3)** polynomial
  operations,9 equations,m+27 witnesses and SOS degree156m+872. The illustrative
  table is **261 certificate / 287 polynomial operations**,43 witnesses,
  SOS degree3368; without mask reuse it is262/288 at SOS degree2760.
  The [unsquared outer product](Papers/research-wip/native-stream-queue/group_projective_unsquared_outer_product.md)
  uses `Punit*(1+SOSouter)-1` with exactly the same positive zeros and
  operation/witness counts. Its degree is **110m+616** when both options are enabled,
  giving **2376** in the example, or **1944** without mask reuse. The
  previous degree3368/2760 polynomials remain SOS alternatives; the
  four-field variant is unchanged.
  The [factored native index](Papers/research-wip/native-stream-queue/group_projective_factored_native_index.md)
  removes four additions without changing the polynomial, taking the example
  to257/283 at degree2376. The
  [shifted native quotient](Papers/research-wip/native-stream-queue/group_projective_shifted_X_quotient.md)
  removes a bound witness and comparison through a positive bijection,
  saving three more polynomial operations. Write
  C=3m+3h+p+185+f_flow-3min(h,3)-epsilon, L=m+18 or2m+10 according to
  mask reuse epsilon, and nu=1+chi for the computed-P option chi. Its
  six-field bounds are **C-1 certificate operations,C+25-3chi polynomial
  operations,9-chi equations and m+27-chi positive witnesses**, at degree
  **nu(44L+9m+135)+44**. The ten-letter example with both options is
  **257/280 operations,8 equations,42 witnesses,degree4298**. Disabling
  mask reuse gives281/degree3594; retaining P gives283/degree2171 with
  mask reuse or284/degree1819 without it. Lower-degree factored-parent
  options remain286/degree1211 and287/degree995 with44 witnesses, or
  four-field293/degree802 with46 witnesses. The universal numerical
  alphabet is still uninstantiated, so75/88 remain unchanged.
  The [shared history right-hand sides](Papers/research-wip/native-stream-queue/group_projective_shared_history_rhs.md)
  save one multiplication with the full polynomial unchanged, making the
  shifted-X example256/279 at degree4298. The
  [strong-unit successor](Papers/research-wip/native-stream-queue/group_projective_strong_unit_product.md)
  then preserves the integer zero set and polynomial cost while absorbing
  the strong comparison. Its generic certificate costsC+1, with8-chi
  equations,m+27-chi witnesses and aC+24-3chi polynomial of degree
  nu(36L+7m+105)+44; idle-only supplied-P tables have degree two lower.
  The example is **259/279 operations,7 equations,42 witnesses,degree3502**.
  Without mask reuse it is280/degree2926; supplied P gives282/degree1773
  with mask reuse or283/degree1485 without it. Shared lower-degree parent
  choices remain285/degree1211 and286/degree995 with44 witnesses, or
  four-field292/degree802 with46 witnesses.
- A [four-dimensional reset interface](Papers/research-wip/native-stream-queue/group_two_reset_mortality4.md)
  loads its affine input matrix in two operations. Exactly two resets
  represent universal membership, but unrestricted mortality accepts every
  input with at most three resets. The regular word restriction is explicit;
  its uniform Diophantine control remains unpaid.
- A [ten-dimensional unrestricted-mortality interface](Papers/research-wip/native-stream-queue/group_affine_guarded_mortality10.md)
  also loads its single affine input matrix in **2=1M+1A** operations.
  A weighted growth guard prevents invalid loading words from creating
  scalar zeros, and a fixed rank-one reset preserves synchronization under
  arbitrary repetition. All other matrices are fixed. This saves one loader
  operation relative to6D by increasing dimension; uniform word/history
  arithmetic is not included.
- The [nine-dimensional successor](Papers/research-wip/native-stream-queue/group_affine_guarded_mortality9.md)
  retains that loader with a three-coordinate guard. For a fixed selected
  duration n>=2 over s letters, its paid positive certificate costs
  (16n-8)s+9n-11 and its polynomial costs(16n-8)s+24n-20, with6n-3
  witnesses and degree at most2s; n=1 costs8s+5 polynomial operations.
  Under the compatible subgroup and input congruence, its unrestricted
  mortality predicate reduces exactly to the paid uniform four-history
  compiler. The packet imports the257/283 factored-index example, and the
  shifted-quotient theorem gives280 by composition; the later shared-history
  and strong-unit results give279 at degree3502 under the same equivalence.
  This is an existence reduction, not verification of an arbitrary supplied
  mortality word.
  The [exact-series rank obstruction](Papers/research-wip/native-stream-queue/group_guarded_mortality_rank_obstruction.md)
  proves physical rank6 and guarded rank9 for the actual universal fibre
  subgroup. This forbids fewer linear coordinates for those identical
  scalar values, including merging physical and guard states. It does
  not forbid another zero-equivalent construction or lower arithmetic cost.
- The [first-norm ratio audit](Papers/research-wip/native-stream-queue/complete75_first_norm_ratio_obstruction.md)
  rejects an apparent87-operation rewrite: after losing the upper ratio
  slack, an explicit CRT and positive Pell construction supplies zeros for
  every ordinary positive input at every fixed compiled constant tuple.
  The complete numerical bounds remain75/88.
- The [zero-offset modulus audit](Papers/research-wip/native-stream-queue/complete75_zero_offset_input_modulus_obstruction.md)
  rejects an88-operation degree135 candidate: modulus a forces
  2d*x+b=psi_2(v), leaving only O(log N) possible inputs up to N for each
  fixed compiler tuple. The [native divisibility audit](Papers/research-wip/native-stream-queue/native_binary_X_divisibility_obstruction.md)
  rejects a standalone55-operation selector at q=48 after dropping
  q divides X. That scale is excluded by the stronger joined matrix
  interface; neither result is a general arithmetic lower bound.
- The [independent-quotient87 candidate](Papers/research-wip/native-stream-queue/complete75_independent_gamma87_alias.md)
  remains **unresolved**. Deleting gamma=rho+sigma gives a literal87-operation,
  degree151 relaxation containing all parent zeros, but the input-index bound
  v<R is lost. A conditional alias and positive main component at R=11
  expose the proof gap; R=11 is outside the full compiler range R>=3q+1,
  q>=16. This neither proves nor refutes the full87 candidate and supplies
  no full counterexample. The established numerical bounds remain75/88.
  The [exact period criterion](Papers/research-wip/native-stream-queue/complete75_independent_gamma87_period.md)
  now characterizes both input-Pell parity branches on each fixed genuine
  history. From a parent zero at x0, transfer to x is equivalent to a
  positive shifted width witness and g dividing2d*(x-x0), where
  g=gcd(2Delta,ord_H(2)), Delta=(a+2)^2-1 and H=4a+3.
  A ternary-index class forces6 to divide g.
  This conditional history theorem supplies no full false-input instance
  and leaves87 unresolved; computing the order is not a free circuit step.
- The [Heisenberg audit](Papers/research-wip/native-stream-queue/heisenberg_two_generator_membership.md)
  gives a uniform four-positive-witness certificate for two fixed generators
  in H^r, at18r+10 graph operations or27r+12 polynomial operations and degree
  at most4. That whole family is decidable. Explicit three-letter targets
  show that pair counts and weighted-triangle bounds do not enforce order.

## Building and checking

From the ProveIt root (one build at a time, as the repository guidance
requires):

```powershell
$env:LAKE_JOBS = '1'; $env:LEAN_NUM_THREADS = '2'
lake build Diophantine
lake env lean Computability/HilbertTenthProblem/Lean/checks/MRDPAxioms.lean
```

Rebuild an edition with its engine, two passes, in `Papers/<year>/`; run a
checker with, for example,

```powershell
$env:PYTHONUTF8 = '1'; py Computability/HilbertTenthProblem/Papers/verification/round4_1984_checks.py
```

## Scope

The editorial notes compare each edition with the journal scan and its raw
Mathpix OCR, which they cite as `original/<year>/jones<year>.pdf` and
`original/<year>/jones<year>.tex`; these inputs are not included. The Lean
library uses ProveIt's `PAListCoding` for finite traces; its module
`PAListCoding.ExactTrace` keeps the Foundation library out of this
library's imports. Dated records in the editorial log and in
`Lean/STATUS.md` cite files by an earlier layout: `lean/` is `Lean/`,
`current/` is `Papers/`, and `vendor/pa-list-coding` is `PAListCoding`.
