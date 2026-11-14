# Mathematical audit and correctness of the cached-head composition

## Scope and result

This note concerns the ordinary mathematical proof that the new literal
194-state cached-head machine, `PA194C`, satisfies

\[
\mathrm{PA}\vdash
  \operatorname{Nonhalt}(\mathrm{PA194C},\mathrm{blank})
  \leftrightarrow\operatorname{Con}(\mathrm{PA}).
\]

It is not a claim of a newly compiled end-to-end Lean or Rocq theorem.
The internal arithmetic statement is justified by primitive-recursive
proof and trace transformations with PA-provable correctness. The source
calibration is inherited from the supplied PA195/PA194 reports; the new
machine-specific preservation is proved from explicit source identity,
positive symbolic runtime contracts, and exact whole-tape initialization.

The corpus revision is
`b88235336c63a247852fe8ec7f931d51f953632d`. The relevant source packets are:

1. [PA194 packet](https://github.com/VladimirReshetnikov/ProveIt/blob/b88235336c63a247852fe8ec7f931d51f953632d/docs/incoming/pa194_conpa_2026-11-13.zip), especially `report/calibration.tex`, `report/reference/original_pa195_calibration.tex`, `report/reference/diagonal_calculus.tex`, and `report/reference/separate_head_calculus.tex`.
2. [PA195S/PA195C packet](https://github.com/VladimirReshetnikov/ProveIt/blob/b88235336c63a247852fe8ec7f931d51f953632d/docs/incoming/PA195_ConPA_research_2026-11-14.zip), especially `independent_verification/composite_command_audit.tex`, `construction195/build_check.py`, and `construction195/preservation.tex`.
3. [Imported PA196 proof statements](https://github.com/VladimirReshetnikov/ProveIt/blob/b88235336c63a247852fe8ec7f931d51f953632d/Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/docs/result.md), [reverse membership proof](https://github.com/VladimirReshetnikov/ProveIt/blob/b88235336c63a247852fe8ec7f931d51f953632d/Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Logic/Reverse.lean), [neighborhood interface](https://github.com/VladimirReshetnikov/ProveIt/blob/b88235336c63a247852fe8ec7f931d51f953632d/Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Logic/Neighborhood.lean), and [internal consistency direction](https://github.com/VladimirReshetnikov/ProveIt/blob/b88235336c63a247852fe8ec7f931d51f953632d/Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Arithmetic/Transport/InternalConsistency.lean).

## What was checked directly

The cached controller is not an arbitrary row mutation. Its six native
rows and two source-DAG replacements are precisely those in the supplied
195C builder. Applying them to the supplied 195S grammar reconstructs the
195C native table with SHA-256
`8f34d9e5cc2e64ecc49bbc8581dc29b2ac0a84ad9187c4dd8b7597588ef22ea3`.
This binds the intended semantics to the actual parent table.

The new grammar and the parent 195C grammar have identical *resolved*
register-instruction maps, not merely equal lists of AX macro names:
3,649 primitive sites and 4,749 branch outcomes. The 190-token AX word,
each register operand, and each resolved successor agree. This guards
against the structured-jump problem: reassociation alone can change an
ancestor-relative jump even when the flattened word is unchanged.

The new final table has 194 working controls and 388 rows. Its seven
simultaneous folds pass all 28 exact two-cell cases in the final table.
All 23 incoming rows establish the distinguishing history bit. An
independent examination of the original fold traces shows that none of
the six cached-controller edits is used during a fold detour, and no new
target enters an exceptional folded control. Thus the fold proof remains
valid under the cached-controller modification.

The construction checker actually completed all 4,749 arbitrary-register
source contracts for the child: 1,507,397 symbolic steps, maximum 506 per
contract. It also completed the corresponding parent contracts. The
entire blank tape reaches the exact prescribed seed after 57,922 steps.
The seed uses source site 25, native dispatch control 84, head -2,
logical registers `(2,0,0,0,0,0,0,0,0)`, and 26 spare blocks of value one.
The current child dense table SHA-256 is
`d759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b`.
These values are taken from the successful new construction receipt;
later changes must regenerate that receipt and its hashes.

The second implementation subsequently passed all 4,749 source outcomes
using literal symbolic tape lists, with no arithmetic-box oracle. It
rederived four generic list-operation lemmas from the actual table,
used 1,096,302 symbolic steps (maximum 403), and certified a minimum
positive-duration constant of three. Its complete blank-start check
independently obtained 57,922 steps. It also checked that the new graph
is distinct from both supplied 194-state graphs under arbitrary control
renaming and under a global tape reflection. This is supporting
executable evidence for the mathematical interfaces, not a replacement
for the arithmetic proof explanation below.

## Exact command protocol

Let `p` be Cantor pairing, `[a;w]=p(a,w)`, and use the total projections
`hd(0)=tl(0)=0`. In particular `[0;0]=0`; a zero push need not enlarge the
canonical stack. Let `I(a,b)=4p(a,b)` and `U(a,B)=4p(B,a)+2`.
The command store is `(t,w,d,h)`.

The cached-head Shift is

\[
S(t,w,d,h)=
\begin{cases}
\mathsf{halt},&h=1,\\
(h,\operatorname{tl}(w),d,\operatorname{hd}(w)),&h\ne1.
\end{cases}
\]

For `y=d+x`, the new MP command is

\[
\mathsf{MP}_x(t,w,d,h)=
\begin{cases}
(0,w,0,y),&I(t,y)=h,\\
(0,w,y,0),&I(t,y)\ne h.
\end{cases}
\]

Neither MP branch pushes. The original PA194 protocol instead tests
`t+h=1` in Shift and returns a successful MP result in the top while
pushing a zero. Hence the new composition changes an operational
interface, not just the names of controls or a tape reflection.

The separate-head AX command pushes ten entries, including the saved top,
and clears `d,h`. Listed from stack top to bottom, its nine generated
entries are

\[
\Gamma(c),L_6,L_5,L_4,L_3,L_2,L_1,
\rho_8(d+x,c,h+y,d),U(d,h).
\]

Here `Gamma(B)=I(B,U(B,B))`; `L1,...,L6` are the unchanged six heads.
The new visible top is the guarded old gate `G`, or zero when its guard
fails. Each generated entry and the gate is different from code one:
all but `U(d,h)` have residue zero modulo four, while `U(d,h)` has residue
two. This numerical fact, not an appeal to consistency, makes the stack
selectors below total where claimed.

## Completeness of the cached protocol

For a general AX stack length `n`, define

\[
\begin{aligned}
\mathsf{Push}_n&=\mathsf{AX}_{0,0,0};S^{n-1};\mathsf{MP}_0,\\
\mathsf{Pop}_n&=\mathsf{AX}_{0,0,0};S^{n+1},\\
\mathsf{Discard}_n&=\mathsf{MP}_1;\mathsf{AX}_{1,0,0};S^n;\mathsf{MP}_0.
\end{aligned}
\]

In this construction `n=10`. Direct use of the two total pairing
projection identities proves

\[
\begin{aligned}
\mathsf{Push}_n(t,w,d,h)&=(0,[t;w],0,0),\\
\mathsf{Pop}_n(t,[a;w],d,h)&=
 \begin{cases}\mathsf{halt},&t=1,\\(t,w,0,a),&t\ne1,\end{cases}\\
\mathsf{Discard}_n(t,w,0,0)&=(0,w,0,0).
\end{aligned}
\]

No stack-length assumption is involved, so these formulas include the
zero-stack alias. In Push, the last MP must fail because it compares an
implication code with a universal code. Pop detects precisely the saved
top at its final Shift; it is deliberately not total when that top is one.
Discard uses two forced MP failures, justified by `I(t,1)>0` and
`I(U(1,0),0)>0`.

Let `Offset_0` be empty and `Offset_i=MP_i` for `i>0`. The generalization
word is

\[
\mathsf{Gen}_{i,n}=\mathsf{Push}_n;\mathsf{Offset}_i;S;
\mathsf{AX}_{i,0,0};S^n.
\]

It sends `(a,w,0,0)` to `(U(i,a),w,0,0)` even when `a=1`. The intervening
Shift reads the cleared cache; AX clears the newly retrieved cache before
any later Shift test.

For the ordinary head in stack position `j`, `1<=j<=n-3`, a selector is

\[
\mathsf{Discard}_n;\mathsf{AX}_{A,D,H};S^{j+1};
\mathsf{Pop}_n^{n-1-j}.
\]

It returns that head and the unchanged underlying stack, with both
offset and cache zero. The diagonal head is `j=1` for `n=10`.
The restricted propositional head for `u<=a` is selected by
`Discard_n;Offset_u;AX_(b,a-u,c);S^(n-1);Pop_n`.
The gate is selected by `Discard_n;AX_(c,b,a);Pop_n^n`.
All preserved heads in these Pop uses are different from one.

The MP proof compiler must install a dummy zero. Put

\[
\mathsf{MPSuffix}_b=S;S;\mathsf{MP}_b;S.
\]

On `(0,[a,I(a,b),0;w],0,0)` it halts if `a=1` or `b=1`; otherwise it
returns `(b,w,0,0)`. The final Shift consumes the dummy zero. Omitting
that zero would consume an item of the arbitrary underlying stack and
invalidate the induction hypothesis.

Compile an MP proof with minor proof `p0:a` and major proof `p1:I(a,b)` as

\[
W_p=\mathsf{Discard}_n;\mathsf{Push}_n;
 W_{p_1};\mathsf{Push}_n;
 W_{p_0};\mathsf{Push}_n;\mathsf{MPSuffix}_b.
\]

An induction on proof trees proves that `W_p`, from any `(t,w,0,0)`,
either halts or returns `(concl(p),w,0,0)`. Axiom cases use the selectors;
generalization uses the word above. Early halting only helps completeness.
If the conclusion is one, then

\[
\mathsf{AX}_{0,0,0};W_p;\mathsf{Pop}_{10}
\]

halts from **every incoming store**, since the initial AX clears the
offset and cache and the final Pop detects the proved top. This universal
incoming-store property is what allows reuse of the exhaustive scheduler
without assuming that earlier command words restore an empty store.

## Soundness and source-level binding

Maintain native derivations of `t`, `h`, and every live canonical stack
entry; `d` need not be a theorem. Code zero has a fixed derivation, for
example the all-zero dominated propositional instance. AX generates only
axioms, zero, generalizations, or the saved theorem. Successful MP derives
`d+x` from the two existing proofs, and Shift only moves existing theorem
codes. A halting Shift exposes a proof of one. Alternatively carry PA
proofs of the arithmetic translations from the outset. This argument
does not depend on the old Shift condition or the old MP push.

The changed primitive source tails have direct all-natural loop proofs.
For `N=3649`, the successful MP tail starts at `E=N-15=3634` and transfers
`D=y,H=0` to `D=0,H=y`. Its decrement/increment/jump loop takes `3y+1`
instructions to exit, then one return instruction. The new Shift starts
at `S0=N-11=3638`. Under the inherited scratch condition `X=0`, it clears
`T`, copies `H` into `T,X`, and restores `H` from `X`. It reaches
`T=H=h,X=0` in `2t+7h+3` instructions, then sets `X=1` and enters the
unchanged comparison/decoding code. Thus the advertised cache-only guard
is exactly the primitive source behavior. The common command-boundary
condition is important: this is not a contract for arbitrary scratch X.

The C source reuses the unchanged scheduler, arithmetic macros, and AX
emitter. Only three exits and the MP/Shift tails change. The supplied
independent command audit proves these finite bindings, and the new
construction checks complete source-map identity against the exact 195C
parent. There is therefore no need to infer source semantics from a
finite blank execution.

## PA calibration of the numerical calculus

The two syntactic translations in the supplied PA194 report are ordinary
mathematical constructions and are logically distinct from the upstream
formal PA196 theorem, which exports only nonhalting implying consistency.
The following substantive points were reviewed.

* Every label in formula code B is below B; code zero is a separate truth
  case. Consequently `Gamma(B): B -> forall x_B B` is sound and has a
  uniform first-order proof supplier after arithmetic translation.
* The retained gate gives membership vacuity and pointed separation.
  For reverse membership rewriting let
  `C=E(a,b)->(chi(b)->chi(a))`, `phi=not C`, and `c=code(phi)`.
  Pointed separation at `(a,a,c)`, direct rewriting, and the unchanged
  `negativeSpecialization` lemma give `phi -> (S -> not P)`. Diagonal
  `Gamma(phi)` pays for generalization at c under phi, giving `phi->Q`;
  the gate gives `not Q`, hence C. This avoids using equality vacuity to
  prove equality vacuity indirectly. Coincident-label cases are handled
  separately as in the existing reverse membership proof.
* Choose `z0=code(E(a,b))` to obtain neighborhood equality at a fresh
  binder using Gamma. Transport the binder to any `z!=a,b` by the
  equality witness and membership-only vacuity. This recovers exactly
  the rewriting, neighborhood, and witness interfaces of the existing
  PA-refutation compiler.
* In the inspected PA196 files, direct primitive `equalityVacuity` uses
  are the reverse-rewriting and neighborhood modules, plus their
  arithmetic-certificate counterparts. Later source modules use the
  derived neighborhood equality interface. The displayed replacement
  therefore addresses the relevant dependency.
* For the converse translate membership to `Bit(x_a,x_b)`, equality to
  equality, and quantification to the corresponding PA quantifier. PA
  proves `Bit(s,z)->z<s`, hence refutes the translation of code one.
  A fixed PA induction template uniformly proves finite bit
  comprehension for each input formula theta. The proof generator
  substitutes theta into syntax; it never evaluates theta or invokes a
  uniform arithmetic truth predicate.
* The gate proof must distinguish label equality a=b. When a!=b, use
  matrix `(Bit(x_a,z) or z=x_b) and T(c)[z/x_b]`; when a=b, use
  `(z=x_b) and T(c)[z/x_b]`. In the latter case the first antecedent
  inside the quantified gate is `Bit(z,z)`, so is false. Treating x_a
  as a fixed parameter in that case would be an error; the supplied
  proof explicitly avoids it.
* The truth alias `I(0,0)=0`, all-zero stack alias, capture-avoiding
  substitution, and proofs of both visible formula registers are
  explicitly handled. These are needed for uniform correctness over
  nonstandard proof codes, not just individual standard instances.

Proof compilation, finite bit-comprehension proof supply, canonical-stack
annotations, and command-word compilation are primitive recursive.
Their correctness uses induction on syntax, finite lists, proof trees,
and loop counters available in PA. Consequently the source computation
has a halting trace iff PA has a refutation, provably in PA. No
reflection axiom, semantic PA soundness assumption inside PA, or
replacement of PA consistency by iPRA consistency is used.

## Internal finite-trace transfer to the new literal table

Let R be the common 3,649-site register program of 195C and 194C, with
the fixed seed. Let H_R and H_M be their coded finite-halting predicates.
The exact symbolic contracts assert that each nonhalting source step
has a finite **positive-length** physical execution to the exact next
frame, and a source halt has an execution to the terminal control.
Each certificate uses literal rows, affine constant-bit scans, and
unary-register list operations. Their witness traces are produced by
primitive recursion on finite lengths, and PA proves the corresponding
scan/update lemmas. This explains why these are PA-uniform statements;
finite sampled register tests alone would not suffice.

A halting source trace gives a physical halt by prepending the fixed
startup and concatenating the exact simulation segments. Conversely,
suppose the physical machine first halts at time T. If the first T+1
source steps did not halt, their positive segments, preceded by startup,
would make a nonhalting physical trace longer than T. Determinism gives
a contradiction. Thus a source halt occurs within that bounded source
iteration. All constructions and the determinism comparison are
primitive recursive and PA proves them by induction. Hence

\[
\mathrm{PA}\vdash H_{194C}\leftrightarrow H_R
\leftrightarrow H_{195C}
\leftrightarrow\exists p\operatorname{Prf}_{PA}(p,\ulcorner0=1\urcorner).
\]

Negating yields the stated nonhalting/consistency equivalence.
This is the same finite-trace transport method used for the principal
PA194 reduction, applied to the cached source. It proves both directions
without extracting arbitrary intermediate tape frames or assuming
actual nonhalting.

## Useful limits and research directions

The ZFC work contributes a compiler lesson: source DAG size and available
physical helper paths must be optimized together. A logically shorter
program need not yield fewer TM controls. The current 194C construction
is a composition of existing independently understood ingredients; its
novelty is their verified combination at 194 states. The cached source
protocol itself was already present at 195 states.

The concise-iPRA work contributes techniques for deriving checker
interfaces from smaller axiom sets, but no equivalence `Con(iPRA) =
Con(PA)` is licensed. Any replacement calculus must come with explicit
PA-verifiable refutation translations in both directions. For this
construction the original numerical PA calibration is retained.

Potential further reductions include jointly optimizing the new cached
controller with the AX DAG, finding a 66-reader/seven-fold or
67-reader/eight-fold allocation, or replacing a whole shared helper
interface rather than independently merging pairs. Every proposed change
must also preserve startup and the exact successor map; successful
finite runs and failed bounded searches do not establish a global
lower bound.
