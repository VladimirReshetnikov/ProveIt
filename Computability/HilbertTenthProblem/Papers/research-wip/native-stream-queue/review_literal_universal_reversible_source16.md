# Report 16: a literal reversible source, and the remaining arithmetic interface

**Scoped result: no source-interface or arithmetic contradiction found.** Report 16 closes the missing literal-source and clean-nonblocking obligations of the earlier five-particle compiler. It does not supply a smaller complete unbounded Diophantine circuit. Its explicit quartic certificates still have an externally fixed horizon and horizon-dependent arity.

This intake uses the original ZIP at historical commit `55d248dc504cff215684773123b3b03a8b8ebbe3`, path `docs/incoming/Literal_Universal_Reversible_Source_Package.zip`, SHA256 `20e6ee57b305ce7648fffa9c590c02807fecfb3fff8fc77885e0fdbab342be5d`. The [independent helper](review_literal_universal_reversible_source16.py) reads it as data with `zipfile`, authenticates 16 selected members and three current comparison files, and executes no archived Python or build scripts. The [receipt](review_literal_universal_reversible_source16.json) records every pin. No eager universal CA, full universal run or historical macro suite is executed.

The main source proof, independent macro proof, three-counter dependency proof, copied binary-compiler proof and primitive-certificate proof were read in full. The permanent placement preserves these under `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/`. References below give those filenames and line anchors; the executable intake binds the original archive members, not potentially revised landing prose.

## The concrete theorem and exactly what it fixes

The literal source is `source/source.json`, SHA256

    38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a.

It is a fully expanded partial-injective two-natural-counter machine M. For natural L,R,T and positive C coprime to 2310, its clean start is

    (START,C*2^L*3^R*5^T,0).

It reaches HALT exactly when the Neary–Woods 15-state/two-symbol machine, started in state A scanning 0 with nearest-head-first binary half-tape values L,R, reaches its undefined J1 transition. Standard finite-tape loading takes T=0,C=1. The scratch exponent T is cleared during the simulation; history and work start with exponents zero at primes 7 and 11. Arbitrary initial work is not covered. Global partial injection, by contrast, is asserted on every natural pair, including malformed encodings. See `16-literal-source-PROOF.md:7` and `:41`.

The [primary Neary–Woods paper](https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf), Definition 3.1 and Table 1 on printed p. 112, puts the U15 head on the final symbol of its finite separator, which is c=0. Thus the fixed A0 convention includes the published universal finite-input family. Its printed p. 121 Table 16 has the sole undefined u10,b cell. I checked these locations in the locally supplied primary PDF text and independently transcribed all 30 table cells for the helper; this is not a claim of a new visual PDF audit. The program-to-tape reduction remains the published universality theorem. Report 16 implements the subsequent finite tape-to-counter loader exactly.

The three-counter simulation has 528 literal instructions, including a scratch-clear prologue. Separate tests/moves and a fresh entry yield 995 rows and 763 controls; indegree normalization yields 1,024 rows and 792 controls. History recording yields 5,451 rows and 4,520 controls, and prime encoding yields the final 141,561 rows and 122,622 controls. The documented 233 history collision pairs and destination-shared prime restorers are essential to the proof: private restorers ending in the same target with the same B=0 image would destroy reversibility. See `16-literal-source-PROOF.md:116`, `:139`, and the full `16-literal-source-independent-macro-audit.md`.

The new implementation obligation is therefore substantively closed: a fixed reversible transition table is present as 32,034,272 JSON bytes. It is not merely an existence citation, nor the old nonreversible 8,408-row table. The exported source is fully primitive, with no runtime macro, callback, hidden counter or oracle.

A second obligation is closed by the macro invariants and decreasing ranks: every clean nonhalting source computation continues forever rather than blocking in an internal macro. Together with predecessor-free START and the earlier compiler's reflection theorem, this gives periodicity/positive return exactly on halting clean inputs. If the forward CA microtime is Theta, the least period is exactly 2Theta+2. The same conclusion would be false for arbitrary guarded sources that could stop at a non-HALT control. See `16-literal-source-PROOF.md:264` and the older compiler proof's Section 10.

Consequently the fixed binary CA's five-particle positive-return problem is r.e.-complete by a computable clean-loader reduction. The report's separate sharp threshold claim additionally inherits Report 12's mass-at-most-four exact-reachability theorem through

    positive return of x iff nonnegative-time reachability of x from F(x).

This intake does not recertify Report 12's proof. Its original TeX/PDF hashes and precise deterministic conservative one-dimensional/unique-vacuum hypotheses remain an explicit separate dependency.

## Independently checked literal source and resources

The helper scans all 141,561 literal rows. It checks all references, primitive guards, updates, source-domain and target-image disjointness, predecessor-free START and exit-free HALT. Exact domain predicates depend only on zero versus positive. For images, the interval partition `{0},{1},{at least 2}` in each pre-counter captures every possible zero/positive postclass under unit updates. This is an exhaustive all-natural guard/image argument, not extrapolation from nine arbitrary test inputs. Every primitive is individually injective, so disjoint image masks prove global partial injection.

| Literal resource | Independently checked count |
| --- | ---: |
| Source controls | 122,622 |
| Primitive branches | 141,561 |
| Increments | 33,436 |
| Decrements | 32,630 |
| Zero tests | 23,429 |
| Positive tests | 52,036 |
| Identities | 30 |
| Maximum incoming/outgoing rows at a control | 2/2 |
| Moving branches p | 66,066 |
| Zero-update branches a | 75,495 |
| Exact zero/positive class cut J | 0 |

The source controls are not CA alphabet states. The compiled CA alphabet has exactly two symbols and valid encoded configurations have exactly five occupied sites. The independent recurrence check gives

    D=2m+4p=509508, S=1019018, Z=20380380,
    unsigned head modes=m+2p=254754,
    signed head-gap codes=D=509508.

For the original ordered compiler, the complete factor count is 269,291,358,255 and its explicit radius upper bound is 3,292,955,588,459,274,804. The observer word has length 1,528,527. These are finite indexed gate/radius resources, not arithmetic-operation counts for a Diophantine polynomial. The astronomical CA local truth table and gate array are not materialized. See `16-literal-source-PROOF.md:247` and `data/16-literal-source-target-ledger.json`.

The helper also independently executes 261 small TM-step macros from the saved three-counter rows, covering all 29 defined TM transitions on nine half-tape pairs and checking their exact clocks. Together with three scratch-clear checks, these visits cover 499 of 528 rows. This is deliberately supplementary finite evidence; it does not replace the all-input invariant proof or the package's claimed complete affine coverage. The full history/prime compilation-table reconstruction is an inherited authored audit, not work rerun by this intake.

## Loader boundary and the unbounded Diophantine gap

For supplied finite strings, nearest-head-first,

    L=sum left[i]*2^i, R=sum right[i]*2^i,
    A=2^L*3^R,
    initial particles={−Z−A,0,Z,S,S+1}.

The helper checks 49 small finite tape pairs and their inverse prime valuations, and reproduces the empty-tape positions

    {−20380381,0,1019018,1019019,20380380}.

No simulation or halting decision is hidden in this loader. The wider clean arithmetic interface A>0,B=0 with no 7 or 11 factor is exactly the prime-factor form advertised above after extracting powers of 2, 3 and 5; arbitrary initial 7/11 factors must not be silently admitted. A raw scalar A can certainly be treated as the input to this fixed machine. That observation gives an r.e. predicate and a computable universal encoding; it does not by itself implement a paid short polynomial relation from an arbitrary program's ordinary x to the required finite tape and prime-power input.

More decisively, the primitive Diophantine construction fixes a source-instruction horizon K as compiler syntax. Its core has

    141565*K natural witnesses,
    23435*K+1 squared residual slots,
    566225*K written residual-term slots,
    degree at most 4.

Exact clock adds one witness and one square; real-orthant selector norms add K squares. These formulas are independently recovered from the actual branch counts. See `16-literal-source-primitive-certificates-PROOF.md:158` and `:182`. The first-halt theorem has a unique complete natural witness at that fixed K, but K is not an ordinary polynomial input. Quantifying over an unbounded K does not turn this varying-arity family into a single fixed-arity polynomial.

The universal K=1 clock-plus-real-norm ledger has 141,566 witnesses and 23,438 squares and is deliberately not an emitted giant polynomial. Its empty-tape input does not halt in one source instruction; the helper checks the unique first transition directly. The small fully materialized example instead has 46 witnesses, 42 squares and 1,100 collected monomials. I independently expand all 42 residual squares, reproduce the entire quartic, verify the full supplied natural assignment, and reproduce its five primitive steps and clock 3115. This small artifact does not supply an accepting universal trace or an unbounded compiler.

The primitive proof's Section 9 has the correct return-time domain restriction. With fixed least period Π=2Θ+2, the residual `T−(u+1)(2Θ+2)` certifies positive return multiples only when u is natural, or in a mixed domain that retains u as natural. Paid selector norms do not force this new coordinate to be integral: allowing nonnegative real u would accept T=Π+1 using u=1/Π. The least-period-only residual `T−2Θ−2` adds no multiplier and preserves the paid real-orthant result. The stated obstruction for all multiples is also sound: a projection of any finite polynomial equation/inequality system with finitely many real witnesses is semialgebraic in T. A one-dimensional semialgebraic set has eventually constant membership on the natural integers, whereas multiples of fixed Π≥2 do not. Thus no fixed-arity purely-real semialgebraic replacement can certify exactly all natural return multiples. This does not exclude natural or mixed-domain witnesses, nor fixed finite horizons.

The actionable remaining obligations are therefore an unbounded fixed-arity history encoding and a fully charged ordinary-input interface when the desired input is an original program's x rather than the raw counter/tape code. A new input substitution must also account for its coefficient/degree/operation costs. No such missing component is supplied by the number of particles, finite gate factorization or bounded-horizon uniqueness.

## Comparison with current parallel work and arithmetic status

The existing [parallel-particle review](review_parallel_particle_reports.md) already covers the later two-involution/sparse-evaluator route and explicitly retains its horizon-dependent certificate boundary. Its original universal-source trace data use the startup-optimized Report 17 source SHA256

    fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3,

not Report 16's source pin. The sources have the same resource counts, but their bytes and startup histories must not be conflated. The actual Report 27 receipt already gives radius 91,711,698, agreeing with 180D+258 at J=0. This is a different full-shift rule from the ordered compiler outside admissible states. It is not a new saving discovered by this intake, nor two paid arithmetic operations merely because the rule is two involutions.

Similarly, the primitive shared-offset certificate saves 52,034*K coordinates and squares relative to the explicitly described per-positive-test-slack construction. That is a real, already documented bounded-horizon improvement, with all its remaining costs present. It does not transfer automatically to the current 85-operation universal circuit or shorten an unbounded source compiler.

No report correction is requested within this scope. The older Report 15 README's absence-of-literal-source and conditional-periodicity statements are historical statements about Report 15; Report 16 supplies their subsequent implementation/premise. The useful update is to record those obligations as closed without changing the current arithmetic frontier or claiming a universal finite-fold polynomial.

## Replay and limits

    python3 /absolute/path/review_literal_universal_reversible_source16.py \
      --repo /absolute/path/Proofs \
      --expect /absolute/path/review_literal_universal_reversible_source16.json

Replay needs the pinned Git object and the three pinned current comparison files. It performs a bounded linear scan of the stored source and small exact arithmetic checks. It never extracts or executes archive code, compiles the enormous CA, reruns the historical affine/macroscopic suites, or materializes a complete universal Pell/halting witness. The checker rejects optimized Python because assertions carry checks and compares the saved receipt with exact JSON types.
