# Natural endpoint penalties for paid three-mass certificates

Replacing two coded-state squares by nonnegative selector penalties reduces the complete quadratic circuits while retaining every witness. The two-step `INC2; DEC2` example costs **51 operations**, down from 56; the three-increment examples cost **100 native / 98 compact-clean**, down from 107 / 105. These are fixed-horizon certificates with the raw loader and all requested endpoints paid. Their degree remains exactly two.

The [source-pinned emitter/checker](three_mass_endpoint_penalties.py) and [receipt](three_mass_endpoint_penalties.json) compare with the actual [committed mass-coordinate circuits](three_mass_arithmetic.md). This is a different change from `v=e+u`: it starts with that already reviewed coordinate system, changes two finalizer summands, and retains all `2Bh` natural witnesses. It does not eliminate a selector or claim an unbounded universal arithmetic bound.

## Complete natural-zero theorem

Fix an actual source certificate with external horizon `h>=1`, finite branch set indexed by `j`, distinct numerical state codes `c(q)`, initial state `q_start`, and halt state `q_halt`. The reviewed mass-coordinate polynomial has the form

\[
F=\sum_r L_r^2+\sum_{t,j}(E_t-e_{tj})v_{tj},\qquad E_t=\sum_j e_{tj},
\]

with all `e,v` natural. It contains every one-hot square `(E_t-1)^2`, the paid initial value `N0=x+1`, value and control equations, and the requested native `y,T` or compact cleaned `T` endpoint. Its initial and terminal control residuals are

\[
C_0=\sum_j c(\operatorname{src}j)e_{0j}-c(q_{\rm start}),
\qquad
C_h=\sum_j c(\operatorname{tgt}j)e_{h-1,j}-c(q_{\rm halt}).
\]

Define the two nonnegative linear penalties

\[
K_0=\sum_{\operatorname{src}j\ne q_{\rm start}}e_{0j},
\qquad
K_h=\sum_{\operatorname{tgt}j\ne q_{\rm halt}}e_{h-1,j},
\]

and replace the complete polynomial by

\[
F_{\rm end}=F-C_0^2-C_h^2+K_0+K_h.
\]

This displayed correction is an all-value polynomial identity, not an assertion that `F_end=F` away from zero. Every remaining square and inactive product is nonnegative on the entire natural orthant, as are `K0,Kh`. Thus any new natural zero forces every remaining summand to vanish. In particular `E_t=1`; natural integrality implies exactly one branch selector is one at each step. At step zero, `K0=0` says that its branch starts at `q_start`. At the last step, `Kh=0` says its branch targets `q_halt`. Because state codes are distinct, these are exactly `C0=Ch=0` on one-hot tuples. Hence every new natural zero is an old one. The same reasoning in reverse proves the converse.

The maps on complete natural zero fibers are the identity: all ordinary input, endpoint and witness coordinates stay the same. There is no new coordinate inequality, reconstruction, hidden positive slack, or altered cleanup lift. Any uniqueness property of the original supplied-input fiber is inherited. For the compact cleaned certificate, its previously proved compact-to-full lift applies unchanged to these same zeros.

For `h=0`, the implementation changes nothing. For `B=0,h>0`, a retained one-hot square is the constant one, so both certificates have no zero. The proof also covers interior numerical initial/halt codes, several branches with the same source or target, false guards, and premature halting. It does not require that the initial code be smallest or the halt code largest.

The complete degree stays exactly two, not just at most two: the free `T` endpoint is retained with coefficient minus one in a squared affine residual and occurs nowhere else. Thus the coefficient of `T^2` is one. This holds for every supported packet, including `h=0`.

## Literal paid costs and fair comparison

The emitter uses the same affine grouping, identical-expression sharing, constant folding, dead-gate removal, and operation metric as its parent: every `+`, `-`, or `*` costs one, including multiplication by nonunit fixed coefficients. In baseline mode the entire emitted gate list and output are checked literally equal to the committed parent for both direct and factored inactive sums. The new mode removes the two endpoint squares, compiles `K0+Kh` as a paid affine form, and includes it in the final addition chain. No unaffected arithmetic is discarded or treated as a free port.

| Actual source fixture | Endpoint interface | Prior best emitted mass circuit | New best emitted circuit | Saving |
|---|---|---:|---:|---:|
| `INC2; DEC2`, `B=h=2` | Native `y,T` | 21M+35A=56 | 18M+33A=51 | 5 |
| Same source/horizon | Compact cleaned `T` | 22M+34A=56 | 19M+32A=51 | 5 |
| Three `INC2` steps, `B=h=3` | Native `y,T` | 38M+69A=107 | 33M+67A=100 | 7 |
| Same source/horizon | Compact cleaned `T` | 38M+67A=105 | 33M+65A=98 | 7 |
| Prime-three zero test, `B=2,h=1` | Native `y,T` | 11M+19A=30 | 11M+18A=29 | 1 |
| Empty halted source, `B=h=0` | Compact cleaned `T` | 2M+3A=5 | 2M+3A=5 | 0 |
| Interior initial/halt codes, `B=3,h=2` | Native `y,T` | 28M+55A=83 | 23M+53A=76 | 7 |

Each column takes the minimum over the two actually emitted inactive-sum schedules. This is a comparison of literal complete circuits, not a global SLP optimum. There is no universal saving formula depending only on `B,h`: code weights, identical square reuse, endpoint support and sharing influence the result. In the zero-test case the removed halt square duplicates the one-hot square, so the saving is only a final accumulation addition.

In the two-step example write `e_t0=a_t,e_t1=b_t,v_t0=c_t,v_t1=d_t`. The new native polynomial is explicitly

\[
\begin{aligned}
F_{\rm end}={}&(a_0+b_0-1)^2+(c_0+2d_0-x-1)^2\\
&+(a_1+b_1-1)^2+(b_1-a_0-2b_0)^2
 +(c_1+2d_1-2c_0-d_0)^2\\
&+(2c_1+d_1-y)^2\\
&+\bigl(300(c_0+d_0+c_1+d_1)+8(a_0+b_0+a_1+b_1)-T\bigr)^2\\
&+b_0c_0+a_0d_0+b_1c_1+a_1d_1+b_0+a_1.
\end{aligned}
\]

The complete 51-operation source is saved in the receipt. The compact variant keeps the already reviewed cleaned-time affine form and omits the native value endpoint exactly as its parent does. At `x=4`, the selected pairs are `a0=b1=1,c0=d1=5`, with the remaining core coordinates zero, `y=5`, and native `T=3016`; both complete polynomials vanish.

## Domain and composition boundaries

The new equivalence is **natural**, not an all-integer zero equivalence. In the complete two-step native packet, take `x=0,y=1,T=600`,

\[
(a_0,b_0,a_1,b_1)=(-2,2,-2,2),\qquad(c_0,d_0,c_1,d_1)=(0,1,0,1).
\]

The new polynomial is zero and the parent is four. The ordinary input, endpoints and mass coordinates are natural here; the negative selectors are precisely outside the theorem's domain. Both scores are verified by the literal full circuits.

Even on the nonnegative rational simplex, weighted state codes can cancel: codes `(0,1,2)`, target code `1`, and selectors `(1/2,0,1/2)` give old control residual zero but new forbidden-support penalty one. This is an exact local boundary example, not a claimed complete rational packet counterexample. The proof therefore deliberately does not promote natural selector integrality to a real-domain theorem.

There is also no automatic composition with an implicit-selector projection `e_last=1-sum(other e)`. A forbidden-last linear penalty can become negative off zero after that substitution. The nonnegativity argument above must be re-established or the penalty redesigned before composing those transformations. The separately explored selector projection has lower operation/variable counts but degree three; this route retains degree two and all `2Bh` witnesses.

## Authentication, evidence and reproduction

The parent is read from immutable commit `c5b680b90f74a792c713d5213d97a06c2b582590`, at `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_arithmetic.py`, with SHA-256 `d5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0`. It is authenticated before compilation from source bytes; no ordinary import or warm bytecode is used. Its pinned archive loader authenticates the original source/cleaned producers from `4e270aa46`, including identical vendored native source, before entering temporarily isolated module namespaces.

The receipt records:

- 80 complete old/new symbolic coefficient comparisons and literal baseline-source/ledger comparisons across 40 actual certificates and both inactive schedules;
- 1,600 signed complete-output correction identities;
- 140 one-hot endpoint cases, including nonextremal initial/halt state codes;
- 240 matched complete natural-zero evaluations and 120 source-rejected horizon/guard cases;
- 1,209 complete natural tuples with affine endpoints supplied from the actual source, including six zeros;
- the complete signed counterexample, exact local rational boundary, and four rejected non-Boolean mode arguments.

The proof gives the general natural-zero theorem; the finite census is bounded evidence. The complete coefficient expansions establish the all-value correction independently of numeric samples. No historical author suite is rerun. This is a research emitter for freshly generated authenticated certificates, retaining the parent's explicit `x,y,T` / `x,T` interface guard; it is not a new hostile-packet schema validator.

```sh
python three_mass_endpoint_penalties.py \
  --repo /path/to/Proofs \
  --expect three_mass_endpoint_penalties.json
```

`--output PATH` writes a deterministic receipt; saved receipt comparison is recursively type-sensitive. The checker uses only Python's standard library and read-only Git, without changing repository or archive files. The source input remains the paid raw `x+1` of the reviewed source machine. The external horizon, an unbounded-history representation, a fixed universal branch table, and a complete ordinary-counter input encoding remain separate obligations.

## Independent review

The separate [independent review](review_three_mass_endpoint_penalties.md) passed on source `7010ab32…`. It read the complete proof and emitter, then reconstructed all fourteen saved old/new pairs with its own coefficient algebra and counted 1,742 live paid gates. The complete corrections, ledgers, retained loader/endpoints, natural-domain proof, `h=0`/`B=0` cases and signed boundary agreed. It did not repeat historical author suites. No source or receipt change was requested.

A second [full-circuit review](review_three_mass_endpoint_penalties_full.md)
independently rebuilds 64 actual certificates and checks 128 complete old/new
pairs, including all 40 author fixtures, scaled clocks, both prime counters,
and empty nonhalted sources. All 10,702 paid gates are live, every exact degree
is two, and the full signed correction and natural-zero fixtures agree. Root
read both independent checkers/notes and replayed both receipts; the author
receipt also passed a fresh root replay.
