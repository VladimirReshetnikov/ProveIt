# Independent audit of the three-witness bounded-halting packet

**Verdict: the displayed main theorem and its stated resource upper bounds are sound. No mathematical correction to the frozen packet is required.** The optional gap composition is sound conditional on the explicitly pinned Pell theorem pair; the physical interpretation remains conditional on the separately retained physical theorem. Neither imported theorem was executed or formally rebuilt in this audit.

Audit date: 4 October 2026. This is a separate review artifact, not a modification, new version, or renumbering of the source packet.

## 1. Exact source boundary

Reviewed packet: `three-witness-bounded-halting-20261004`.

- `PROOF.md`, SHA-256 `233b0f67ce13e81a41132017214db5b34d10c965cd9a3ef56d1cbc9d280ac33c`
- `MANIFEST.json`, SHA-256 `cc8a653802570dac6744cc00d490213f34d0d6604a1bd74588173724895a7a55`
- All 14 manifest entries and all 6 dependency pins verified against their exact bytes
- Pinned inert Pell source SHA-256 `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`

The entire main proof and the author's static checker were read as inert text. The relevant positive-domain POWER derivation in the retained native-gap proof and the actual theorem statements in the retained Pell source were inspected. No author, prior-packet, upstream-science, counter-interpreter, physical-simulator, saved-schedule, or Lean code was imported or executed.

Only the newly written, inspected `check_external.py` and ordinary file/hash/JSON operations were executed. That checker independently reconstructs rational Lagrange interpolation by synthetic division of the full node polynomial and then clears denominators. It does not import the source's polynomial implementation.

The source packet was never written, renamed, or retimestamped. `source_before.json` and `source_after.json` record the same bytes, sizes, modes, modification/change timestamps, and inodes for its files and directories. Read-access timestamps are not asserted or used as integrity evidence.

## 2. Clipping and the exact horizon boundary

Source: `PROOF.md` lines 29–49.

For native counters, clipping each initial value to `min(a,T)` is valid. If a counter was below T, its representative starts identically. If it was at least T, the representative starts at T and, after t common transitions, is at least `T-t`. At every instruction-entry time `t<T`, this is strictly positive. The original counter differs from its representative by a fixed nonnegative offset along that common branch sequence, so both give the same zero-test result. This induction establishes every branch through transition T and every control state `q_0,...,q_T`, including loops and the virtual halt suffix.

The proof makes exactly the right distinction at the endpoint: the representative can become zero after transition T while the original remains positive. Neither equal final counter values nor equal final zero status is needed or claimed. No statement about transition T+1 follows.

With positive coordinates `A=a+1`, the representative is `min(A,T+1)`, so `K=T+1` is correct. The smaller native threshold T−1 fails uniformly: in the zero-test/decrement self-loop, starting from T−1 first enters H on transition T, whereas starting from T does so on transition T+1. This verifies sharpness of this uniform clipping threshold only. It proves no degree, coefficient, description-size, or witness lower bound.

At T=0 there are no transitions. Only whether `q_0=H` matters. An initially halted program remains accepted for the by-horizon predicate and is excluded from first-halt-exactly-T when T>0.

## 3. Finite preprocessing is real work

Source: lines 51–68, 169–205.

There are exactly `N=(T+1)^2` clipped input pairs. Their code `i=(u−1)K+v` is a bijection between `[1,K]^2` and `[1,N]`. The acceptance set is a fixed N-bit table for the selected program, initial state, halt state, horizon, and either by-horizon or exact-first-halt predicate.

In principle, computing that table decides all N clipped bounded instances, with at most N·T native transitions and the initial-state check. Each simulated representative counter is at most 2T. This is an effective finite algorithm, not an oracle. No such interpreter was run in this audit. The table contains no dependence on the eventual unbounded inputs A,B: after compilation, they only select their clipped class.

The correct description is a separately compiled, T-indexed fixed-arity polynomial family, with a uniform effective generation procedure. Calling its polynomial presentation “nonuniform in the horizon” must not be confused with noncomputable advice or an absent uniform generator. The expensive finite preprocessing cannot be treated as free work, and no unconditional faster method for a single bounded-halting instance follows.

Acceptance bits are fixed coefficients/data during construction. Treating an unknown or freely adjustable table as another polynomial input would change the predicate; allowing the table to choose its own accepting class would destroy the intended halting condition unless a separate correctness encoding were paid for.

The first-halt-exactly-T version legitimately changes only this table. For the decrement/zero-test loop at T=2, by-horizon acceptance consists of codes 1–6 and exact-T acceptance of codes 4–6. These are closed-form declared fixtures, not generated traces.

## 4. Integer interpolation and the three-witness equivalence

Source: lines 70–140.

At node i the product of differences is `(-1)^(N-i)(i-1)!(N-i)!`. Multiplying its reciprocal by `d=(N-1)!` gives exactly the integer coefficient `(-1)^(N-i) binom(N-1,i-1)` in the displayed basis. Therefore `U_0(i)=d u_i` and `V_0(i)=d v_i`, with no input-dependent denominator and no hidden variable.

The six residual slots are fully specified and their squared sum has integer coefficients. Zero of a sum of integer squares forces every listed residual to vanish. The range product first fixes j to a node. At that node, the A conditions reduce to

`(A-u)(u-K)=0` and `A-u=r-1≥0`.

If u<K, the product forces A=u. If u=K, the positive slack forces A≥K. Thus u is exactly `min(A,K)`. The same reasoning fixes v, hence j, and the linear equations uniquely fix `r=A-u+1`, `s=B-v+1`. Positivity of r,s is essential and is correctly part of the domain. The acceptance product has exactly the roots in S, with empty S giving the constant 1 and no solutions.

Conversely, those formulas provide a positive witness whenever the clipped class belongs to S. They give the advertised bounds `1≤j≤N`, `1≤r≤A`, `1≤s≤B`. There are exactly three declared witness variables and six presentation slots, not necessarily six distinct or nonzero constraints. There are no hidden trace or selector witnesses.

At T=0 the two product residuals vanish identically. The accepted polynomial is `2(j−1)^2+(A−r)^2+(B−s)^2`; the rejected one is `(j−1)^2+(A−r)^2+(B−s)^2+1`. Both have degree exactly two and nine nonzero monomials. Accepted inputs have the unique tuple `(1,A,B)`.

## 5. Degree, coefficients, support, and expanded size

Source: lines 142–197, including the final support-bound addition.

All degree statements are joint in the five variables A,B,j,r,s. For T≥1, `N≥4` and `m=N−1`. The range square has degree 2N, the acceptance square at most 2N, each linear square at most 2m, and each classification square at most 4m. Since `2N≤4m`, the stated bound `deg P≤4N−4` follows. No equality is needed or claimed.

Set `L=K·2^(N−1)·(N+1)!`. The product norm bound and the binomial sum give `||U_0||_1,||V_0||_1≤L`; also `||R||_1,||H_S||_1,dK,d≤L`. Each product residual has norm at most `4L^2` and each linear residual at most `4L`. Consequently

`||P||_1≤2L^2+32L^4+32L^2≤66L^4`.

The bound applies also at T=0. For nonzero integer coefficients, `7+4 ceil(log_2 L)` unsigned magnitude bits suffice; an explicit sign bit is separate. This is `O(N log(N+1))` magnitude bits uniformly in M.

The support calculation is correct and does not use a dense five-variable count. The permitted disjoint monomial types have ceilings:

- pure j powers: `4m+1`
- A² or B² times j powers: `2(2m+1)`
- A or B times j powers: `2(3m+1)`
- r or s times j powers: `2(m+1)`
- r², s², Ar, Bs: 4

Their sum is `16m+11=16N−5`. Lower-degree contributions from the slack squares are already contained in these types. Cancellations can only decrease support. Thus O(N) stored monomials, O(N log(N+1)) coefficient bits, and O(log(N+1)) exponent bits per fixed-length exponent vector give `O(N² log(N+1))` bits for the described expanded representation. This is an upper bound, not an optimality or compressed-information claim.

The source's direct construction bound of O(N³) integer arithmetic operations is a valid loose bound. Its intermediate coefficient bit lengths remain O(N log(N+1)) by the same product/triangle estimates. It is explicitly not a unit-cost bit-complexity theorem or a polynomial-in-log(T) claim.

Fresh computed examples confirm that replacing the degree bound by equality would be wrong: at T=2 the tested polynomials have degree 28 rather than the ceiling 32; at T=4 they have degree 92 rather than 96. No artificial degree padding occurs.

## 6. Optional native-gap composition

Source: lines 207–315; retained `native_gap_PROOF.md` §3; retained `pell-source.lean` lines 760–766 and 860–864.

Each POWER copy pays for all 26 positive leaves, including its output, and all 15 residuals. The index C is the already counted A or B. The natural aliases are substituted as positive leaves minus one, while alpha and beta are positive leaves plus one. The two copies have disjoint leaves.

The actual pinned theorem statements support the specialization. E1–E9 enforce the positive-index Matiyasevic characterization. E9 supplies `y_p≥C≥1`, excluding its zero-index alternative. E10–E15 supply the power theorem's base 2, exponent C, target 2o, strict modulus inequality, and congruence. E13 with w≥2 and g≥1 implies alpha>w≥2, so the source's natural subtraction `alpha−2` agrees with ordinary subtraction. Its natural-subtraction Pell equations equal 1 precisely when the ordinary integer equations have the displayed form.

Completeness retains positivity: the power theorem's auxiliary g cannot vanish because alpha>1; the Pell x,u,s are positive; y≥C≥1 and v>0 force q_v>0; beta>1 forces q_b>0; `t≡C mod 4y` with `1≤C≤y` rules out t=0; and the strict modulus bound gives J>0. Signed congruence quotients can be split into paired naturals. This also covers C=1, the semantic exponent-zero case. These arguments are text-level verification against the pinned theorem dependency, not a new formal proof of that theorem.

Adding the two gap equations therefore gives exactly 57 positive witnesses, 60 total variables, and 38 residual slots. The two module E13 squares retain separate degree-twelve monomials with coefficient one; P uses none of those module leaves. Hence `deg F=max(12,deg P)` exactly, including degree 12 at T=0. The upper bound for deg P remains an upper bound.

Positive gap inputs force positive decoded denominators. The quotients p,q are uniquely determined by the gap triple; their powers-of-two exponents uniquely fix A,B, after which the native proof fixes j,r,s. This is unique decoded projection only. Adding any natural integer to both alpha_1 and alpha_2 in one module preserves all equations and positivity, yielding infinitely many full tuples for every accepted input. No finite-fold or single-fold conclusion is available for this composed formula.

The physical transport is explicitly conditional. This audit does not re-establish the physical compiler or its timing/collision bounds, and does not extend the claim to unencoded triples or replace an instruction horizon by a collision horizon.

## 7. Uniformity and excluded conclusions

The horizon indexes different polynomials: degree, factorial constants, interpolation products, and acceptance coefficients all change with T. Writing an outer existential quantifier over horizons does not make this family one polynomial. An arithmetic encoding of its varying generation procedure and table correctness would be additional work, with additional variables and uniqueness obligations.

Accordingly the packet establishes none of the following: a single fixed-polynomial unbounded-halting representation; a new single-fold MRDP result; a universal-polynomial bound; optimal three-witness arity; exactness or minimality of the degree/support/bit upper bounds; novelty or priority. Its explicit scope restrictions are correct.

## 8. Independent finite evidence and external checker

`independent_results.json` records a completed fresh run:

- 140 interpolation-node identities, covering T=0 through 6
- 28 native expanded polynomial instances with degree, coefficient, support, and monomial-shape checks
- 64,064 class-code assignment checks and 2,380 expanded canonical assignments
- 91,800 literal positive witness triples for every acceptance subset at N=1 and N=4, comparing each expanded polynomial to the residual sum of squares
- All 512 acceptance tables at N=9, with 18,432 canonical assignment checks
- Nine hand-declared semantic fixtures, including exact-halt exclusion, initial halt, T=0, looping, and tail inputs
- 12 complete gap compositions, with the degree identity, two retained leading monomials, exponent-zero fixture, changed-gap rejection, and common quotient-pair shifts
- Eight malformed or changed external candidate classes rejected

These finite checks support the symbolic audit. They do not prove arbitrary-machine table correctness, all-exponent POWER equivalence, or the physical compiler. All-input conclusions in this report come from the proof reconstruction and the clearly identified imported theorem statements.

The portable, standard-library-only checker accepts data-only JSON containing external expanded coefficients and optionally all residual coefficients. It recomputes the exact native or gap polynomial and compares every coefficient, validates declared variable order and source pin, and can verify the complete frozen source manifest. No candidate code is evaluated. Its explicit acceptance-table limitation appears in every successful external-check result. See `README.md` for commands and schema.
