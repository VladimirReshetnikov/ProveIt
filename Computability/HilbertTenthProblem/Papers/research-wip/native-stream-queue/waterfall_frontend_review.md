# Waterfall frontend, universality and common-column review

**PASS within the stated scope. No mathematical or source-transcription defect found.** The fixed Waterfall matrix correctly implements every defined source-machine instruction, including zero-length repetition boundaries, with strict unique-minimum semantics. The source universality handoff uses a valid finite-tape interface. The horizon-free common-column theorem is correct for its restricted positive-relative-diagonal class. Neither result supplies a fixed-arity universal polynomial or an improved universal operation count.

Archive: `Waterfall_Diophantine_Certificates.zip`, arrival `24a743255`, SHA-256 `b5d3ee90f9631695afc3c6f34f765b617eb9c631c65ab32705cf3d0e8811a9fc`. The exact original archive was left untouched. All 31 members are inventoried in [the saved receipt](waterfall_frontend_review.json); the independent checker authenticates the fixed `SHA256SUMS` and every listed member before checking the mathematics.

The complete article and all eight Python replay files were read before executing `sh run-replay.sh`. Detailed grouped-polynomial natural-zero/API review was separately assigned; I read that section and compiler for the frontend/first-halt interface and safe replay, but do not replace that separate review. No PDF rebuild or visual audit of the report's own rendered PDF is claimed. The primary paper's actual Table 16 and halting configuration were visually inspected on rendered PDF pages 17 and 19.

## Primary source and universality handoff

[Neary and Woods' primary paper](https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf) establishes the 15-state binary machine through bi-tag simulation. Definition 3.1 and Table 1 put it initially in `u1`, reading the rightmost symbol of `G=bc`; `c` is blank. Thus the report's `A,0` start and two finite binary half tapes contain the required inputs. I visually checked all 30 Table 16 cells: `(u10,b)` is undefined and `(u15,b)` writes `b`, moves right and enters `u14`. The final displayed halting configuration also reads `b`; the following sentence's `c` is a local typo. The report resolves that discrepancy correctly.

The [author-deposited metadata](https://mural.maynoothuniversity.ie/id/eprint/12416/) confirms DOI `10.3233/FI-2009-0036`, pages 123–144, and explicitly warns about incorrect PDF pagination. The report's bibliography correctly follows that metadata. Downloaded primary PDF SHA-256: `6274cb6828579c234bf9f62b8fecc64dea4bb1ae842b4e2e39b9bfc676114c1b` (179,909 bytes).

The upstream [TM table](https://raw.githubusercontent.com/Iijil1/MTGPrograms/main/Examples/UniversalTM15x2.tm.txt) and [Waterfall matrix](https://raw.githubusercontent.com/Iijil1/MTGPrograms/main/Examples/UniversalTM15x2.twm.txt) were downloaded independently; their bytes match the delivered SHA-256 values `ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae` and `52cfed3f6cba671ed7b166c126288d555ed687b74622ae5a9aaa5bee1345e46a`. I did not execute or re-audit the upstream Go compiler; the delivered compact definition and exact macrostep proof directly establish the fixed matrix's behavior.

The [Waterfall specification](https://esolangs.org/wiki/The_Waterfall_Model), whose permanent-link revision is 193038, agrees with the chosen semantics: positive initial levels, nonnegative triggers, undefined simultaneous minima, and an all-zero halt trigger. Its serialization has metadata in the first row and initial values in the first column; trigger vectors are source rows. The article correctly transposes only the actual 46-by-46 trigger submatrix. The 47th serialization coordinate is not a physical clock.

Combining the published finite input encoding with the all-input simulation proves computable-enumerability completeness for halting on pairs `(L,R)`. This is a computable reduction, not an arithmetic-cost bound for encoding arbitrary external programs. The report expressly makes that distinction at article lines 119–125.

## Exact macrostep and timing proof

Primary locations: `paper/waterfall-diophantine.tex:67`, `:108`, `:130`, `:162`, `:176`, `:192`; `replay/verify_frontend.py:65`; `replay/verify_frontend_independent.py:76` in the private extraction.

For a prescribed prefix, deadlines are exactly `a+Mp` even before legality is established. In each repeated block the selected-versus-competitor gap is affine in its iteration index. Checking both extreme iterations is sufficient only because **every letter prefix and every other clock** is checked. The delivered verifier does precisely this, including the halt-clock competitor. For the `Q`, `Y` and `2Y` loops it restricts endpoint checks to their active domains `Q>=1` or `Y>=1`; multiplying the accumulated trigger by zero correctly handles omitted blocks. The independent cone implementation also parameterizes every active iteration, splitting the `2Y` loop by parity. Neither proof assumes a finite tape bound.

My separate checker uses destination-row/source-column matrices, reconstructs the complete matrix from Appendix A, constructs symbolic firing-count vectors from scratch, and obtains the same 43,065 endpoint inequalities. Each shifted affine gap has constant at least one and nonnegative remaining coefficients. All 64 domain-tagged raw forms equal the exported forms; converting their constants by the indicated lower-bound shifts exactly reproduces Appendix B's printed table and multiplicities. All 46 final coordinates agree in each of the 58 instruction/residue cases.

The resulting count and canonical shift are `c=6+3Q+r+3Y` and `Delta=19+6Q+2r+6Y=2c+7`. The article correctly describes `Delta` as a difference between successive control-event timestamps, rather than the elapsed time through the final write trigger. This matters already at `L=R=0`: initial control at 1, last write at 10, next control at 20. The signed timing potential is independently checked against all 30 canonical controls and all 46 trigger columns; it confirms timing but is not used as a proof of event legality.

At a canonical `(J,1)` cut the halt clock is uniquely minimal and is observed before any update. Internal early halts are excluded by the strict competitor inequalities. Induction therefore makes all natural `(L,R)` runs tie-free up to any possible halt, and the timestamp after `k` source instructions and `C` nonhalting Waterfall events is `1+2C+7k`. Positive nonhalt resets and integer deadlines make event times strictly increase, so there is no hidden finite-time accumulation convention.

The grouped certificate's first-halt interface is compatible: only defined source instructions are selectable, and the terminal state and head are `(J,1)`. A claimed prefix extending beyond an earlier halt cannot select the next instruction. The detailed source-polynomial converse and public API guard audit remain assigned to the other reviewer.

## Loader and resource accounting

The two varying clock values are exactly `2+2L` and `2+2R`. The declared free-constant/copy binary arithmetic model charges two constant multiplications and two additions, hence four operations. This is a literal schedule, not an optimality theorem. Reusing those values, two further additions compute the valid file bound `2(L+R)+47`; it exceeds both varying initial levels, every other initial level, all trigger increments and metadata count 46, including `L=R=0`.

One macrostep can require exponentially many literal events in the input's binary length. Eliminating those repetitions is a substantive compression; it neither bounds witness bit length nor eliminates the number of source instructions. The external `k` still changes arity and the polynomial itself. For fixed `k`, choosing a finite instruction branch leaves only integer linear equalities and nonnegativity constraints, so the effective semilinearity argument at article lines 349–354 is correct. No fixed-dimensional representation of an arbitrary branch sequence or its input decoder is supplied.

The separately completed [forced-boundary projection](waterfall_forced_boundary_projection.md) specializes the initial A0 and terminal G0/H0/I1 instructions. Its full polynomial identity, natural-zero bijection and arithmetic ledger are separate from this frontend audit.

## Common-column theorem and literal ledgers

Primary locations: article lines 365–451 and `replay/verify_certificates.py`.

For columns `b_i*1+d_i*e_i`, removing the common offset `sum(b_i*p_i)` leaves exactly the independent streams `a_i+d_i*N` and fixed halt marker `a_h`. With `d_i>0`, only finitely many stream elements lie below the marker. A legal halt occurs exactly if no stream hits the marker and no pair intersects below it; the first obstruction really becomes a minimum tie unless an earlier tie already stops the merge. Both start offsets and the lower bound on a CRT intersection matter. Counts and physical timestamp are therefore exactly the stated ceiling and common-shift formulas.

The assumption is a positive **relative diagonal** `d_i`, not merely a positive actual self-reset `b_i+d_i`. With relative increment zero or negative, a uniquely minimal stream can stay minimal forever despite increasing physical event times. The report states this restriction and supplies correct examples. It also correctly rejects the tempting endpoint-only count criterion for arbitrary matrices: proposed future cross-increments can move a fictitious final halt boundary past an actual earlier halt.

For the residue-separated subclass, distinct residues modulo `n+1` eliminate both classes of tie. The natural remainder bound follows from `r_i+u_i=k_i-1`; the other affine row fixes the integer ceiling and the nonnegative product `p_i*s_i` gives its unique positive/negative-part decomposition. This proves a unique tuple, including time. Promoting the fixed coefficients `k_i,b_i` to inputs generally raises degree from two to four; the report acknowledges this.

The supplied three-clock circuit literally has 8 multiplications and 14 additions/subtractions; four witness shifts give 8+18 for positive witnesses. These are 22/26-operation evaluations in a decidable class, with no universal claim. The signed counterexample is valid: natural-domain nonnegativity is essential, so these products cannot silently be used for unrestricted signed witnesses.

## Replays and independent checks

All scripts were read before running:

```sh
cd /tmp/waterfall_frontend_review/waterfall-diophantine
sha256sum -c SHA256SUMS
sh run-replay.sh
python /tmp/waterfall_frontend_review.py /tmp/waterfall_frontend_review/waterfall-diophantine --output /tmp/waterfall_frontend_review.json
```

The complete eight-command author replay passes. Every original member remains byte-identical afterward; only new readable log files are added. The author records 2,116 matrix entries; 58 macros with 43,065 endpoint obligations and 64 forms; 30,015 separate symbolic guards and 32,625 cone checks; 2,842 concrete macros and 69,629 events; 1,944 common-family runs, 36,750 local natural assignments, 20,000 literal-ledger evaluations and 3,969 CRT comparisons. The seven-instruction example replays 189 prehalt events and timestamp 428. The grouped coefficient alignment, mutation and release checks also pass, within their stated finite-test scope.

The portable independent checker imports **no author modules** and writes nothing from `verify(root)`. It independently authenticates all 31 members, reconstructs 2,116 matrix entries, verifies 30 source-table cells, 43,065 strict endpoint inequalities, 58 macrostep identities and 2,668 final-coordinate identities, and checks all 64 printed affine forms. It compares actual deadline/countdown selections with a separate cell-map tape interpreter on 435 fixtures totaling 46,833 events, including zero tapes and larger quotients. It also checks 3 canonical immediate halts, 3 loader-bound cases, 30 canonical and 46 trigger potential identities, 3,000 general common-column instances (1,711 legal halts and 1,289 ties), 59,535 local natural tuples with 245 unique fibres, two nonpositive-relative-diagonal locks and an earlier-tie regression.

Finite simulations corroborate implementation; the all-value conclusion uses the exact affine identities and positivity certificate plus the written induction. The frontend helpers are research proof scripts, not a canonical hostile-input API. Their internal constructors are not claimed to reject every malformed scalar or custom matrix. No repair is needed for the reviewed mathematical or frontend claims; any separate grouped-compiler guard findings should be reported by that reviewer.
