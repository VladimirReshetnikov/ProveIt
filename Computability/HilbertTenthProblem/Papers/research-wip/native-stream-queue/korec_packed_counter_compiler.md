# A paid universal register-machine history in one counter word

The [builder](korec_packed_counter_compiler.py) compiles a finite increment /
conditional-decrement register program into a fixed-arity integer polynomial.
Its default is an explicit 22-instruction strongly universal machine, with
ordinary positive input supplied directly in register 2 and one positive
program parameter. The default finalizer uses **453 = 138 M + 315 A**,
54 positive witnesses, and six comparisons; its propagated degree bound is
43897. This is an independent universal route, not an improvement to the
[260-operation alternative](neary_woods_universal_history_units260.md) or the
separate 75/87 frontier. The [receipt](korec_packed_counter_compiler.json)
contains the actual default schedule, counts, source digest and finite audits.

The new arithmetic component packs every register into a single digit of a
chronological counter word. Only two counter lanes of one joined AND and one
counter-transport equation are needed, regardless of the number of registers.
Instruction selection and chronological control are also paid. The witness
count and arithmetic schedule do not depend on the duration or register sizes.

## 1. Actual table and ordinary input

Korec's [*Small universal register machines* (1996)](https://www.cs.cmu.edu/~cdm/resources/Korec1996-small-universal-RM.pdf)
defines strong universality in Definition 2.3(i), with the input convention
on printed pages 267–268: register 1 contains a machine-dependent code,
register 2 contains the unchanged argument, and the other registers start at
zero. Main Theorem (a1), Figure 1 and Sections 5–6 establish the 32-instruction
machine; Section 7 contracts test/decrement pairs for Main Theorem (a2).
We use that contraction, including a decrement/increment restoration of its
remaining pure test. The source retains the full Figure 1 table and the
control-point correspondence for an executable local simulation audit.

Here `I r t` increments register `r` and goes to `t`. `D r p z` goes to `p`
and decrements when the register is positive, and otherwise goes to `z`
without changing it. States are 0 through 21, with start 0 and sole halt 22.
Registers are 0 through 7.

| State | Instruction | State | Instruction |
|---:|:---|---:|:---|
| 0 | D 1 1 2 | 11 | D 5 12 13 |
| 1 | I 7 0 | 12 | D 5 14 15 |
| 2 | I 6 3 | 13 | D 2 18 19 |
| 3 | D 5 2 4 | 14 | D 5 16 17 |
| 4 | D 6 5 3 | 15 | D 3 18 20 |
| 5 | I 5 6 | 16 | I 4 11 |
| 6 | D 7 7 8 | 17 | I 2 21 |
| 7 | I 1 4 | 18 | D 4 0 22 |
| 8 | D 6 9 0 | 19 | D 0 0 18 |
| 9 | I 6 10 | 20 | I 0 0 |
| 10 | D 4 0 11 | 21 | I 3 18 |

The original labels, in this order, are
`1,3,6,4,7,9,10,12,13,33,14,16,18,23,20,27,22,30,32,25,29,31`.
New label 33 restores register 6 after the positive branch of original test
13. Every other combined decrement follows the original test and decrement,
including test 32's positive branch through original decrement 15.
Thus contraction preserves the full configuration at each original retained
control point, reaches the same unique halt, and introduces no infinite
internal path.

There is a relevant transcription discrepancy in
[Alhazov–Verlan's reproduction, Figure 1 and its following list](https://arxiv.org/pdf/1009.2706):
the listed zero target of original label 27 is `q1`. We use `q29`, as shown
in the original Korec Figure 1 and explicitly in Korec Table 4, printed page
295. It increments register 0. This choice follows the original machine;
it is not justified by a finite test alone.

For a positive parameter $E$, put $e=E-1$. Initial registers are exactly
\[
 (0,e,x,0,0,0,0,0),\qquad x\ge1.                              \tag{1}
\]
For every recursively enumerable set $S$ of positive integers, strong
universality supplies one fixed $e$ whose machine halts on $x$ exactly when
$x\in S$. Taking the parameter $E=e+1$ proves the universal slice theorem
below. No computable transformation of the varying input is hidden here.
The dependence of $e$ on the represented set is permitted program coding;
no particular enormous code needs to be constructed to count this fixed
source. Arbitrary other $E$ values still denote actual runs of the same table.

## 2. Generic counter packing and pretyping bounds

The compiler also accepts any nonempty finite program with $m$ nonhalt states,
start 0, sole halt $m$, and $k\ge3$ registers. Its input convention is (1),
with additional zero registers if $k>8$ and the evident truncation if $k<8$.
Every destination is in $\{0,\ldots,m\}$. An increment has one edge; a
conditional decrement has a positive edge and a zero edge. Let $K$ be the
number of edges. Label each edge by its source $s_a$, target $t_a$, register
$j_a$, and kind `I`, `D`, or `Z`.

All quantified coordinates are positive. For each edge use
$E_a=\widehat E_a-1\ge0$, and define
\[
 J=\sum_a E_a,\quad W=\widehat W-1,\quad Y=\widehat Y-1,\quad
 h=E+x+\eta,\quad D=2h,\quad B=cD^k,\quad P=(B-1)J+1,          \tag{2}
\]
where $\eta>0$ and the fixed dyadic numeral
$c=2^{\operatorname{bitlength}(m+1)}>m+1$ is charged when multiplied.
The source defines the two powers and all the following polynomials using
only additions, subtractions and multiplications.

Put
\[
 \begin{split}
 R&=(h-1)\sum_{j=0}^{k-1}D^j, & M_R&=RJ,\\
 I&=\sum_{a:I}D^{j_a}E_a, & L&=\sum_{a:D}D^{j_a}E_a,\\
 Z&=\sum_{a:Z}D^{j_a}E_a, & M_Z&=(D-1)Z.
 \end{split}                                                  \tag{3}
\]
The three retained outer equations are
\[
 \begin{split}
 J+\widehat W+\gamma&=P,                                      &(4)\\
 B(W+I)+(E-1)D+xD^2&=W+L+PY,                                &(5)\\
 B\sum_a t_aE_a&=\sum_a s_aE_a+mP,                          &(6)
 \end{split}
\]
where $\gamma>0$. Equation (6) pays initial state 0 and final state $m$.
It is a chronological shift equation, not an endpoint flow constraint.
The affine input in (5) costs three multiplications, one addition, and the
separately charged subtraction $E-1$.

Before native typing, (4) rules out $J=0$: then $P=1$ while
$\widehat W+\gamma\ge2$. Thus $J\ge1$, $P\ge B$, and
$0\le W,E_a,J<P$. Since $h\ge3$, we have $D\ge6$ and $B>1$.
Moreover $R<D^k<B$, and
\[
 0\le M_R<P,\qquad
 0\le M_Z\le(D-1)D^{k-1}J<(B-1)J<P.                         \tag{7}
\]
These estimates use only positivity, (2) and (4). They require neither
canonical edge bits nor a previously typed duration.

Join the $K+2$ lanes
\[
 (E_a,J,E_a)\ (0\le a<K),\qquad (W,M_R,W),\qquad(W,M_Z,0)      \tag{8}
\]
by powers of $P$ to form three integers $H,M,A$. All coefficients are already
in $[0,P)$ by (7). Take $a$ to be the least power of two at least $K+2$ and
prescribe the native scale
\[
 Q=BP^a.                                                     \tag{9}
\]
The complete [prescribed native AND](native_binary_masked_selection63.md)
is embedded with positive ports $H+1,M+1,A+1,Q$, using its literal padded
forms $16H+12,16M+10,16A+8$ and scale $16Q$. All these ports are positive
on every positive assignment, even away from (4). At an outer zero,
$H,M,A<P^{K+2}\le P^a<Q$, so the complete inherited interface applies.

## 3. Exact chronological theorem

At every positive zero, the native theorem types $Q$ as dyadic and gives
$H\mathbin{\&}M=A$. Since $Q=BP^a$ is a positive power of two, both $B$
and $P$ are powers of two; $B=cD^k$ also makes $D$ dyadic. Write
$B=2^b,P=2^v$. The divisibility $B-1\mid P-1$ gives $b\mid v$: reduction
modulo $2^b-1$ leaves $2^{v\bmod b}-1$, whose only divisible value in that
range is zero. Hence
\[
 P=B^T,\qquad J=1+B+\cdots+B^{T-1},\qquad T\ge1.              \tag{10}
\]
There is no duration variable, upper bound, or unpaid exponent equation.

Since $P$ is dyadic and the coefficients in (8) are canonical, the joined
AND splits into the $K+2$ displayed ANDs. In particular each $E_a$ is a
subset of $J$. The equality $\sum_aE_a=J$ then implies exactly one selected
edge at every chronological row. One direct proof uses reduction modulo
$B$: the sum of the low selected bits is at most $K<B$ because
$K\le2m<cD^k=B$, so it equals 1, with no carry. Divide by $B$ and repeat.
All edge digits are therefore 0 or 1.

Write $W=\sum_{t<T}w_tB^t$. The range lane says that every $w_t$ has the
unique counter expansion
\[
 w_t=\sum_{j<k}w_{j,t}D^j,\qquad 0\le w_{j,t}<h.              \tag{11}
\]
Indeed $RJ$ repeats the binary mask with $k$ blocks of $\log_2D$ bits,
each block allowing only its lowest $\log_2D-1$ bits. It is smaller than
$B^T$ and has no overlapping time blocks. Adding the unique increment or
positive-decrement weight to (11) produces digits at most $h<D$, so neither
$W+I$ nor $W+L$ has any counter or time carry. Their time digits are below
$D^k<B$.

The initial vector $(E-1)D+xD^2$ also has canonical counter digits because
$E-1<h$ and $x<h$. Comparing the base-$B$ digits in (5) yields exactly
\[
 c_{j,0}=[j=1](E-1)+[j=2]x,\quad
 c_{j,t}=w_{j,t}+[\text{positive decrement of }j\text{ at }t],
\]
\[
 c_{j,t+1}=w_{j,t}+[\text{increment of }j\text{ at }t].        \tag{12}
\]
The coefficient beyond the last row is precisely $Y$; the equation itself
makes it the final canonical counter vector. No independent upper bound
on the free $Y\ge0$ was assumed.

A positive-decrement edge therefore has positive current counter. On a zero
edge of register $j$, the last AND lane in (8) gives $w_{j,t}=0$. There is no
simultaneous positive decrement at that row, so its current counter is zero.
Every selected edge is consequently the actual transition of its source
instruction.

All state digits in (6) lie between 0 and $m<B$. The low digit forces the
first source to be 0; successive digits force each target to be the next
source; the highest digit forces the last target to be $m$. No source edge
has label $m$, so there is no earlier halt followed by spurious extra rows.
Equations (12) and (6) thus describe an actual finite halting computation.

Conversely, given any finite halted computation, choose a dyadic $h$ larger
than every counter value in every configuration and larger than $E+x$.
Use $D=2h$, $B=cD^k$, its actual $T\ge1$, and (10). Pack its selected edges
and post-decrement counters into the variables above, and take its final
counter vector for $Y$. Set $\eta=h-E-x>0$. Since every row satisfies
$w_t<D^k$ and $c>m+1\ge2$,
\[
 \gamma=P-J-W-1\ge(B-2)J-(D^k-1)J
             =(B-D^k-1)J>0.                                \tag{13}
\]
All outer equations and AND lanes hold, and the complete native theorem
supplies positive native auxiliaries. This proves the full positive
existential equivalence for arbitrary finite duration, including $T=1$.

**Universal corollary.** With the default table, for every recursively
enumerable $S\subseteq\mathbb Z_{>0}$ there is a positive integer $E_S$ such
that the emitted polynomial has a positive zero at $(E_S,x)$ exactly when
$x\in S$. This is a fixed finite polynomial with one program parameter,
not a family whose arity grows with the running time.

## 4. Literal schedules and inherited unit forms

All arithmetic is literal: fixed-numeral multiplication costs one M, and
addition or subtraction costs one A. The builder folds neutral operations
and repeated expressions. It forms weighted state sums by grouped suffix
sums; the zero-labelled group is never emitted. It shares the common edge
packing and counter packing between $H$ and $A$. A binary recursion builds
$P^K$ and $1+P+\cdots+P^{K-1}$; every gate in that recursion is charged.
The same power gates are reused in (9) when identical. Every emitted gate
of each audited complete schedule reaches its final output.

Five literal forms are supported. The scaled and computed forms use the
[positive-scale](native_binary_positive_scale.md) and
[computed-field](native_binary_computed_fields.md) positive graph projections.
The normalized [norm-unit](native_binary_norm_units.md) and
[index/coupled-unit](native_binary_index_coupled_units.md) forms preserve the
accepted outer histories through their stated fresh auxiliary extensions
and conditional restorations. Their semantic hypotheses hold here: the
raw embedding is complete with positive ports and scale, and every removed
native field is private. Their source guards check the actual prefixed
rows and every outer consumer/export. No all-tuple identity or old/new
native-witness bijection is asserted for strong normalization or coupling.

| Form | Certificate | Comparisons | Positive witnesses | Final operations | M | A | Degree upper bound |
|:---|---:|---:|---:|---:|---:|---:|---:|
| Raw SOS | 428 | 19 | 61 | 484 | 144 | 340 | 7024 |
| Positive-scale SOS | 428 | 18 | 60 | 481 | 143 | 338 | 7024 |
| Six computed fields SOS | 428 | 12 | 54 | 463 | 137 | 326 | 15292 |
| Normalized norm units | 433 | 8 | 54 | 456 | 138 | 318 | 46195 |
| Coupled index units (default) | 436 | 6 | 54 | 453 | 138 | 315 | 43897 |

The default certificate is 132 M + 304 A. Its two free positive inputs are
$E$ and ordinary $x$; only $E$ is a program parameter. Degree bounds are
propagated through the actual DAG and are not claimed to be exact.
The default product has seven native factors with degree bounds
$7061,16466,3824,584,8820,3238,3238$, total 43231; the maximum retained
residual bound is 333, giving $43231+2\cdot333=43897$.

The [routing outcome compiler](routing_balance_outcome_compiler.md) removes
last-exit obligations only after prefix ranks are supplied. This packet
supplies a different complete universal interface: actual register history,
including zero tests and chronology. It neither makes explicit periodic
routing universal nor claims a low-cost prefix-rank graph for arbitrary
algorithmic stacks. The imported
[report's Part XIII table and priority-reaction construction](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex)
provided the lead; no reaction simulation or priority oracle is assumed by
this arithmetic compiler.

## 5. Verification and limits

The receipt records the original-table contraction audit; whole raw-source
comparisons against direct scalar packing and a separately invoked native
source; complete signed/positive projection and unit-correction identities
through each inherited rewrite; actual interpreted and packed halted
histories; and adversarial zero-branch, underflow-borrow and disconnected
control-cycle fixtures. It includes the complete default final schedule,
not only a hand operation estimate.

The finite run checks test outer rows and exact joined-AND values. They do
not materialize the enormous Pell witnesses for those runs. Existence of
those positive native extensions is the inherited mathematical theorem.
Finite simulations alone do not prove the primary machine universal; that
claim uses the verified primary table contraction and Korec's theorem.

Author receipt generation and a fresh default replay pass. The checks include
20 literal ledgers; 128 complete raw identities (64 signed); 384 inherited
full-output/correction identities (192 signed); 672 original-table control
point cases; and 288 halted histories over 49 tables, with 754 chronological
rows (344 increments, 170 positive decrements, 240 zero branches). Four of
those histories use the actual default table, program code 1 and inputs
1 through 4, each halting after 57 transitions. Seventeen forged histories
exercise zero-test, underflow and control-chronology rejection. Independent
review provenance will be appended after review.

Root independently reviewed the complete proof and source, the primary text
and Figure 1 visually, and ran a fresh default replay: PASS, with no findings.
Its separate interpreter, packer and outer-source/AND audit checked 774 halted
histories and 1,674 chronological rows across 193 programs, including the
actual U22 table and all three branch kinds. These are outer-history checks;
no full native witness tuple was materialized.

Franklin's independent full proof/source/fresh-default review also passes,
with no findings. It checked the primary strong-input convention, Main
Theorem and Section 7, inspected Figure 1 visually, and verified the disputed
branch against Table 4. Its separate enumeration tested 3,474 positive packed
assignments over 11 new small tables against legal halting chronology: the
three outer equations plus joined AND accepted exactly 18. Rejected cases
included 1,087 negative-component, 1,944 wrong-zero and 3,297 wrong-control
cases, with overlapping categories. It independently checked all 20 selected
full-source closures, operation ledgers and degree bounds, deriving the
inherited main-norm cancellation symbolically from the actual source subgraph.
No full Pell witnesses were claimed. The source, receipt and note are frozen.
