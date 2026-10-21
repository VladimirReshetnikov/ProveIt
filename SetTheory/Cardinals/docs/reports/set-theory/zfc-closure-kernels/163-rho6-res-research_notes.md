# Formalism, coding, and scheduler research notes

Date: 2026-10-21. These notes consolidate the formalism work accompanying
the K216 rho6 parameter-permutation candidate. They separate mathematical
theorems, exact finite certificates, and bounded compression experiments.
The main report is `../report.tex`.

## 1. Result and attribution

The delivered machine is a distinct 216-state variant obtained by swapping
two universally quantified parameters in the rho6 generator of the
upstream partial-selector K216 construction. The change affects two native
transition targets. The parent construction and its complete physical
verification are documented in the main report; these notes do not replace
that verification.

The public repository acquired its partial-selector K216 construction
during this research session, at commit `e6083665`. That upstream
construction supplies the actual 217-to-216 state saving. It must not be
attributed to the present parameter-permutation search. The independent
contributions here are the distinct parameter-permuted variant, its
verification, and the formalism and scheduler results below.

The initial local repository snapshot was
`d3d6b8c14e1ddff37eb1417c5448caa41cfd6da7`. The inherited native-calculus
calibration, dominated-row recovery certificate, and strong command
compiler remain explicit dependencies. No new proof-assistant
formalization of that entire calibration is claimed.

## 2. Hereditary change of pairing

### The theorem

Suppose `P0,P1 : N^2 -> N` are effective bijections, `Pi(0,0)=0`, and
`Pi(a,b) >= max(a,b)`. Define four binary constructors

\[
 J_{i,t}(a,b)=4P_i(a,b)+t\qquad(t=0,1,2,3),
\]

with tags implication, membership, universal quantification, and equality
in that order. Keep truth code 0, falsity code 1, the unrestricted native
axiom schemes, theorem-only GEN, MP, and the existing gated set-theoretic
bundle. Then there is a computable bijection `phi:N->N` fixing `0,1,2,3`
such that

\[
 \mathcal C_{P_0}\vdash n
 \quad\Longleftrightarrow\quad
 \mathcal C_{P_1}\vdash\phi(n).
\]

The calculi are therefore equiconsistent. This is a theorem about every
natural code; it does not require a separate well-formedness predicate.

### Proof

Set `phi(0)=0`. For positive `n`, decode uniquely
`n=4P0(a,b)+t` and define

\[
 \phi(n)=4P_1(\phi(a),\phi(b))+t.
\]

Both decoded arguments are strictly smaller than positive `n`: if
`P0(a,b)>0`, the factor four makes this immediate, and if the pairing is
zero its unique arguments are both zero. The recursion is thus well
founded. The constructor equation also holds at zero because its unique
recursive alias is `I(0,0)=0`. Interchanging the two pairings defines a
reverse map. Strong induction on the original input shows that the two
maps are inverses. They fix the four small constants and intertwine all
four constructors.

Every natural number is recoded, including numbers used as variable labels
and numbers used simultaneously as labels and formula codes. In
particular, the private binder `R(a,b)` in the merged equality row becomes
`R(phi(a),phi(b))`. Recoding only syntactic formula occurrences while
keeping their numerical labels fixed would not prove this theorem.

All native axiom expressions and the bundle are built from the four
constructors and the fixed constants. Their instances are transported
exactly. The bundle's two inequalities are preserved by injectivity. MP
and theorem-only generalization are preserved by the constructor
identities. Induction on finite derivations in each direction now proves
the displayed equivalence. Falsity is fixed, yielding equiconsistency.
The proof formalizes in ZFC under its displayed hypotheses on the pairing
functions. For a concrete computable pairing, those hypotheses must also
be proved in the intended base theory.

### Dyadic example

The pairing

\[
 D(a,b)=2^a(2b+1)-1
\]

has inverse

\[
 a=\nu_2(n+1),\qquad
 b=\frac{(n+1)/2^a-1}{2}.
\]

The unique odd-part decomposition proves bijectivity, while
`D(a,b)>=2^a-1>=a` and `D(a,b)>=2b>=b` prove the required bounds.

The independent finite arithmetic checker covers 100,000 inverse codes,
640 rectangular pairing cases, 512 bidirectional recoding cases, and 1,024
constructor intertwining cases. These finite computations support the
implementation of the formulas; the preceding induction proves the
all-natural statement.

## 3. The dominated fourth parameter requires its own argument

The inherited native propositional family is

\[
 L(A,B,C,U)=((C\to U)\to A)\to((A\to C)\to(B\to C)),
 \qquad U\le A.
\]

Hereditary recoding does **not** preserve this numerical side condition.
For Cantor-to-dyadic recoding, `phi(16)=20` and `phi(20)=16`. Consequently,
transporting a dominated proof by the bijection alone is invalid.

The existing Source149 full-rho8 certificate repairs the argument. Its
only term normalization is `I(0,0)=0`. At every dominated-row leaf the
fourth argument is either zero or a literal implication subterm of the
first argument. Implication dominates both its inputs for every pairing
in Section 2. Induction through an implication context therefore proves
`U<=A` after every numerical assignment, including assignments that cause
zero aliases. Every restricted leaf remains valid under the new pairing.
The certificate's forward substitutions and MP inferences are then
unchanged.

The exact certificate has 3,728 proof nodes and 5,160 shared terms:
1,260 dominated-rho8 leaves, 55 combined MP/substitution nodes, one truth
node, 410 substitution nodes, and 2,002 MP nodes. The maximum structural
depth needed to witness the dominated argument as a subterm is four.
There are leaves whose witnesses are not immediate children, so the
certificate does not justify replacing the side condition by a
zero-or-direct-child restriction.

For each fixed pairing the dominated and unrestricted calculi therefore
have equal theorem sets. The valid comparison is

\[
 \mathcal C_{P_0}^{\rm dom}=\mathcal C_{P_0}
 \ \cong\ \mathcal C_{P_1}=\mathcal C_{P_1}^{\rm dom}.
\]

The equalities are separate finite-certificate arguments. The middle
isomorphism is the hereditary recoding. The original finite native/ZFC
calibration then transfers through these three steps.

Certificate SHA-256:
`3cf18a5fe9f187b50b79d97b84535ce9bf776305728b0cdfe17285e94f028452`.
Independent forward-checker SHA-256:
`21bb2310088c8dce095b4f4c8c055012c1a068e3d7dfa7254d23e9f29d8fd9b5`.
Their original filenames are
`149-dom-theory-dominated_rho8_full_certificate.json` and
`149-dom-theory-check_classical_compact.py`.

## 4. More general constructor changes and the implementation boundary

The same hereditary proof applies to any four injective binary
constructors whose tagged images partition all natural numbers, whose positive outputs have
strictly smaller inputs, and which retain `I(0,0)=0` and `R(0,0)=1` as the
only recursive zero alias and the falsity code. Define the recoding by
decoding the old outer constructor and rebuilding the corresponding new
one on recursively recoded arguments. The inverse and derivation proofs
are identical. Only the constants actually retained by the new algebra
are automatically fixed; unlike the fixed-modulo-four case, arbitrary
prefix-tag changes need not fix codes 2 and 3.

This covers uniform reversal of either argument order separately for
membership, equality, quantification, or implication, provided every
operation using those constructors is adjusted consistently. It also
covers complete binary prefix tags. The dominated-row recovery additionally
requires the new implication constructor to dominate its inputs.

These are logical freedoms, not machine-size results. Reversing Q requires
adjusting GEN; reversing implication requires adjusting MP. Any alternative
tag system needs matching field readers and arithmetic constructors. A
source-equivalent or mathematically equiconsistent description does not
establish a binary runtime contract or a blank-tape initialization theorem.

For dyadic enumeration, if `f(n)` is the second inverse-pairing component,
then `f(n)<=floor(n/2)`. Packed proof pointers therefore drain by the same
well-founded descent as in the original enumerator. Finite word packing
is exact by pairing bijectivity. The inherited cofinal reset family

\[
 P(3,P(1,P(1,P(Y,R))))
\]

is at least `Y`, supplying a refuting candidate above any finite cutoff
whenever a native refutation exists. The compiler facts `I(t,1)>0` and
the ability to force a zero bundle gate by `U=A=C` still hold. The
strong compiler can therefore be rechecked with these algebraic
properties, yielding completeness from arbitrary finite retained tuples.

The Cantor-diagonal theorem about an arbitrary *unsafe tail* is not
automatically preserved by a change of pairing: candidate order changes.
A theorem-safe entire stack is sufficient without that theorem. In
particular, the accepted logical startup tuple

`[np,tw,ws,ac,d,h,s1,s2,pl]=[3,0,0,0,3,0,0,0,0]`

has theorem top, theorem cache, and an entirely theorem-safe zero stack
under dyadic pairing as well. The additive counter may equal three, and
cofinal completeness permits cutoff three. This is conditional on the
changed binary machine actually reaching that tuple; the old startup
trace cannot certify a new transition table.

The tested literal dyadic pair/unpair replacements were larger than the
existing Cantor macros. Their source had 214 distinct DAG roles rather
than 203. No smaller dyadic binary machine was obtained.

## 5. A three-valued obstruction to setting U=A

Replacing the fourth-parameter family by its specialization

\[
 ((C\to A)\to A)\to((A\to C)\to(B\to C))
\]

does not retain the desired strength. The repository's
`k219-fourth-parameter` already rules out a broader family containing this
case. The contribution here is a smaller, independently checked
three-element matrix, not a newly excluded class of formal systems.

Use carrier `{0,1,2}`, designated set `{2}`, truth value 2, falsity value 0,
and the following tables, with first arguments indexing rows:

\[
 I=\begin{pmatrix}1&2&2\\2&2&2\\1&1&2\end{pmatrix},\quad
 R=\begin{pmatrix}1&1&0\\1&0&0\\1&1&0\end{pmatrix},\quad
 E=\begin{pmatrix}0&0&0\\0&0&0\\0&0&0\end{pmatrix},\quad
 Q=\begin{pmatrix}1&1&2\\1&1&2\\1&1&2\end{pmatrix}.
\]

An independent symbolic-AST evaluator exhausts every assignment to the
seven other native rows, the specialized eighth row, and the entire
ungated set-theoretic bundle. All yield 2. It also checks MP and GEN on
all nine argument pairs. MP preserves designation because the last row
of I is designated only in its final column. GEN preserves designation
because the last column of Q is constantly 2.

For every numerical code define `v(0)=2`, and evaluate each positive code
recursively by its unique outer constructor. Its two arguments are
smaller, giving a bounded, arithmetic definition of this valuation. The
exceptional identity `I(0,0)=0` is respected because the matrix gives
`I(2,2)=2`. Falsity code `1=R(0,0)` gets value `R(2,2)=0`. Thus every
constructor identity holds on every raw code, including junk codes.
Induction on a finite native derivation proves that all its theorems have
value 2, whereas falsity has value 0. This consistency proof formalizes
in elementary arithmetic and hence in ZFC.

If ZFC is consistent, this specialized calculus cannot have a
ZFC-provable consistency equivalence with ZFC: the arithmetic consistency
proof and that equivalence would give a ZFC proof of its own consistency.
This argument does not exclude an unrelated three-parameter axiom, a new
bundle, or a different proof system.

## 6. Finite protected stack credit at an arbitrary cutoff

This strengthens the arithmetic scheduling lemma underlying upstream
`k217-protected-tail-seed/proof.md`. The full proof is in
`protected_credit.md`; the precise quantifiers are important.

Let `W(n)` be the complete finite command word generated by candidate n.
For Cantor unpairing write `(tag,y)=unpair(n)` and let f be its second
projection. The first command is MP, DROP, or NIP for tags 0, 1, or 2, and
AX for every larger tag. The remaining proof pointer is `f(y)` in the
first three cases and `f(f(f(y)))` in the AX case. A positive remaining
pointer r continues with `W(r-1)`; a zero pointer ends the word.

Give commands conservative stack balances MP=0, DROP=1, NIP=-1, AX=10.
Let b(n) be the total balance of W(n) and m(n) its minimum prefix balance,
including the empty prefix. The successful-MP dummy push, if retained,
can only improve this lower bound.

For each cutoff `N>=0`, choose s with
`s(s+1)/2 <= N < (s+1)(s+2)/2`, put

\[
 E(N)=\max\left(6,\frac{(s+1)(s+2)}2\right),
\]

and let d(N) be minus the minimum prefix balance of the finite
concatenation `W(N)...W(E(N)-1)`. The empty prefix makes d(N) nonnegative.

**Quantified seed theorem.** For every N, every arbitrary tail S, every
finite list L of native theorem codes with `length(L)>=d(N)`, every
theorem current formula, every theorem cache, and every additive counter,
start the abstract machine at a complete command root with cutoff N,
proof pointer zero, and stack `pushL(L,S)`. Then no NIP reads S. Every
formula that can reach the falsity detector is a native theorem.
Consequently any halt supplies a finite native refutation. If the proof
pointer is initially p>0, let (b,m) summarize `W(p-1)`; the sufficient
credit is instead

\[
 \max(0,-m,d(N)-b).
\]

The formula is exact for the conservative schedule. It need not be
minimal for an actual run in which successful MP creates extra safe
entries.

### Why the finite horizon suffices

Every whole Cantor diagonal of index at least three has nonnegative
relative balance at every command prefix, starting from zero. To see
this, put `g(0)=0`, `g(r)=b(r-1)` for positive r. Nonnegative prefix sums
are preserved by pullback along f, since f enumerates the finite rows
`[0]`, `[0,1]`, `[0,1,2]`, and so on. Iterate this observation three times
for the AX suffixes. In diagonal s, the first s-2 words are AX words.
The first k complete such words have balance at least 10k. Within the
AX word at position y, the suffix loses at most `f^3(y)<=y`; after its
first command the relative balance is at least `9y+10`. The final NIP,
DROP, and MP words retain respective lower bounds `9s-19`, `8s-17`, and
`7s-17`, all positive for s>=3. The global prefix premises required in
this argument concern earlier candidate indices, so induction is
well founded. The six candidates before diagonal three can be checked
directly.

The interval defining d(N) covers the tail of the current diagonal and,
for early N, the exceptional diagonal two. All later whole diagonals
need no extra credit. Therefore d(N) is the credit for the entire
infinite conservative schedule, not merely a guessed finite horizon.

Track an explicit list of theorem entries above the fixed S. Its length
is at least the initial credit plus the conservative balance. Before a
NIP it is at least one, because the balance after that NIP is
nonnegative. Every popped item is therefore a theorem, and the arbitrary
tail is never inspected. AX, DROP, and MP preserve theoremhood. The
pairing alias `P(0,0)=0` is harmless: a conceptual prefix zero can still
be tracked because `unpair(P(x,z))=(x,z)` holds exactly. For a nonzero
initial pointer, reserve enough for its word and enough remaining
credit for the future cutoff, giving the displayed maximum.

### Full calibration and useful cutoffs

If the run does not halt earlier, every active word drains and every
candidate above the finite cutoff is eventually processed. The inherited
strong compiler constructs a refuting command block from a native
refutation independently of the retained stack tail and working tuple;
its cofinal padding places such a block above every finite cutoff. Hence
a refutation implies a halt from every seed in the theorem. Combining
this with soundness proves halt iff native refutation, then the inherited
native/ZFC calibration proves the desired consistency equivalence.
Binary runtime simulation and startup remain separate obligations.

No theorem prefix is needed at cutoffs 0, 1, 4, 5, 6, 8, 9, 10, 11, or
at any triangular cutoff `s(s+1)/2` with s>=3. Cutoffs 2, 3, 7, 12, and
18 need one conservative theorem entry. In particular, cutoff 3 does
not permit an arbitrary unsafe tail with an empty protected prefix: its
first command is NIP. The delivered candidate has an entirely safe zero
stack, so this caveat does not affect its calibration.

The independent finite checker compares 10,000 explicit command words
against its balance recurrence and checks 2,000 complete diagonals,
covering candidate indices below 2,001,000. This is supporting evidence
for the all-natural argument, not a replacement for it or a binary
machine proof.

## 7. Compression experiments and their limits

The baseline source has 4,751 primitive leaves and 203 distinct DAG
roles. The following are exact results within the stated source families;
none is a general lower bound on state count.

* All 5,040 permutations of the seven independent row blocks were tested
  with unchanged spans preserved and moved closed forests reassociated
  to the right. The baseline order uniquely attained 203 roles. The
  census was 203:1, 205:1, 206:13, 207:123, 208:4,902.
* Three dictionary-reparsing runs made 3,176, 4,605, and 4,537 trials.
  They produced 53 distinct source hashes with 203 roles, of which 52
  retained maximum zero run at most six. None reached 202. Saved hits
  passed independent primitive-word and both complete CFG-resolver
  checks. This certifies the tested closed-source constructions, not a
  cheap physical decoder allocation.
* Uniform argument reversal gave 208 roles for membership, 209 for
  equality, and 205 for both. Repeating all 279,936 independent row
  parameter permutations for those three variants lowered the first
  two to 207 and 208 respectively, and left the third at 205.
* All ten complete four-leaf least-significant-bit binary prefix-tag
  layouts retaining `I(0,0)=0` and `R(0,0)=1` were priced with the tested
  literal arithmetic macros. The baseline attained 203 roles; the best
  alternative attained 215. Alternative arithmetic implementations or
  source parenthesizations are not excluded.
* Uniform Q reversal and combined Q/R/E reversal were also explored by
  closed-grammar heuristics. No source below the 203-role baseline was
  found. These were bounded heuristic searches, not exhaustive results
  over all equivalent programs.

The seven source-row spans, using half-open primitive ordinals, are
G `[493,902)`, rho6 `[902,1185)`, rho5 `[1185,1481)`, rho4
`[1481,1780)`, rho3 `[1780,2076)`, rho2 `[2076,2426)`, and rho1
`[2426,2657)`. The bundle occupies `[2657,4570)`. Reassociation can cross
these interfaces while remaining inside the larger closed region
`[173,4592)`; artificially imposing a root on only `[493,4570)` loses
useful sharing. This is one concrete reason source-description searches
must include larger closed contexts.

## 8. Artifact manifest and reproducibility

Portable mathematical material in this packet (paths relative to the archive root):

| File | Role |
|---|---|
| `research/research_notes.md` | This consolidated report and exact scope. |
| `research/pairing_change.md` | Detailed pairing theorem and implementation obligations. |
| `code/theory/check_dyadic_pairing.py` | Standalone finite arithmetic support checker. |
| `evidence/dyadic_pairing_check.json` | Its recorded passing result. |
| `evidence/pairing_certificate_check.json` | Existing full-rho8 certificate recheck and structural census. |
| `research/diagonal_matrix_obstruction.md` | Raw-code soundness proof for the three-valued matrix. |
| `code/theory/check_diagonal_matrix.py` | Standalone exhaustive AST-based matrix checker. |
| `evidence/diagonal_matrix_check.json` | Its recorded passing result. |
| `research/protected_credit.md` | All-natural finite-horizon scheduler proof. |
| `code/theory/protected_credit.py` | Standalone finite scheduler-support checker and credit calculator. |
| `evidence/protected_credit_result.json` | Its recorded passing result. |

The three independent Python checkers use only the standard library.
Run them with Python 3. The matrix checker writes its JSON next to the
script; the scheduler checker prints JSON for optional redirection.
The existing Source149 certificate and its checker are included under
`code/theory/`; `code/theory/check_pairing.py` reruns that structural check.

Search scripts `permute_rows.py`, `grammar_search.py`,
`dictionary_search.py`, `orientation_terms.py`, `prefix_tags.py`, and
`check_dictionary_sources.py` are research scripts. Their present imports
refer to the session's parent helper module and repository snapshot;
they require path adaptation before being advertised as portable
standalone reproduction tools. The recorded JSON results and exact
candidate source files remain useful evidence. The model-search C++
program and external theorem-prover checkout are not required to verify
any mathematical result above.

## 9. Main-report review

Sections 7–9 of the main report and its set-theoretic bundle appendix were
reviewed against these mathematical notes and independent checker ASTs.
The pairing theorem, domination repair, finite-matrix valuation,
protected-credit formula, cutoff-3 caveat, and the displayed Req/Clos
definitions and bundle agree. No mathematical correction was required.
The report correctly attributes the inherited broader fourth-parameter
obstruction and the public partial-selector state saving. Its source-DAG
counts are explicitly separated from binary state counts.
