# Removing the success-only zero push from modus ponens

## Exact source change

Start with class-A U208's 3,909-primitive counter source. Delete the closed
subtree at address `001101110`, comprising ordinals `[3847,3866)`.
It is the inherited `PUSH0` macro: with cleared scratch registers,

\[
(T,W)\longmapsto(0,P(T,W)).
\]

Its next sibling, at `001101111`, is the seven-primitive `PAR4` macro.
Collapse their parent to this sibling. The output is `source.sites.json`:
3,890 primitives, 197 source DAG nodes, maximum address depth 42, maximum
zero run 6. Every retained primitive and control edge agrees with the old
source after mapping the deleted interval to its successor and translating
later ordinals down by 19. The exact source address at protected bootstrap
ordinal 136 is unchanged.

This removes a source-level stack operation. It does not yet establish a
sub-208 literal TM; the binary allocator and whole primitive simulation must
be checked separately.

## Why the old current is zero here

The successful-MP path has just destructively checked the old cache against
`I(t,z)`. Immediately before that comparison, ordinals `[3834,3837)` transfer
the current T into scratch X, clearing T. The comparison at `[3837,3847)`
never increments T. Its successful exit is ordinal 3847 and has emptied the
two compared counters. Therefore T=0 and both scratch registers are zero
at this point, independently of the natural values compared.

An independent finite inductive certificate is provided by
`prove_source_zero.py` and `source_zero_certificate.json`. Its domains are
products of `{0}`, positive naturals, and all naturals at each source ordinal.
It checks the initial source state (N positive, all other registers zero)
and all 5,080 applicable abstract control edges. It also checks that the
calibrated ordinal 136 bootstrap store (1,0,13,0,0,1,0,0,1) belongs to
the invariant, so the actual startup continuation is covered directly. The certificate has 3,907
reachable ordinal domains and proves T=0 at ordinal 3847; ordinals 3848 and
3849, the positive body of the redundant initial T-to-X transfer, are excluded.
This is an induction on arbitrary execution length, not a bounded run.

Consequently the old removed `PUSH0` contributes only the stack cell 0.
After deletion, `PAR4` still installs the target z in T and preserves the
counter z, since T and the scratch registers are zero.

## New exact abstract command

Write the retained tuple as `(t,w,d,h)`. Put `z=d+x`. Change only MP success:

\[
\operatorname{MP}'(x)(t,w,d,h)=
\begin{cases}
(z,w,z,0),&I(t,z)=h,\\
(0,w,z,0),&I(t,z)\ne h.
\end{cases}
\]

The old success value was `(z,P(0,w),z,0)`. The final U208 source has
**three** commands: direct transfer S, MP, and AX. Its selector fields are
S:[0], MP(x):[1,x], and AX(c;x,y):[c+2,y,x]. The earlier four-command
NIP/DROP presentation is not used in this proof.

The direct transfer has the exact contract

\[
S(t,[x;v],d,h)=
\begin{cases}
\mathsf{halt},&h=1,\\
(h,v,d,x),&h\ne1.
\end{cases}
\]

AX, S, pairing, field parsing, and candidate enumeration are unchanged.
The soundness invariant says t, h, and all explicit protected stack entries
are numerical-calculus theorems. On success the tested cached implication
and current premise justify z by modus ponens. Keeping w preserves the
invariant; failure is unchanged. S remains the only possible halt and
still extracts a proof of target code 1.

## Corrected three-command proof compiler

This section uses the final source's three-command compiler in the retained
U213 `proofs/compiler.tex`, rather than the historical four-command compiler.
Let `M=I(A,Y)`. All compiler blocks except the modus-ponens node remain
unchanged. Put

\[
D=\operatorname{AX}(0;0,0),\qquad
H=D;S^{11},\qquad
\operatorname{PUSH}=D;S^9;\operatorname{MP}'(0),
\]
\[
\operatorname{DISCARD}=\operatorname{MP}'(1);
\operatorname{AX}(1;0,0);S^{10};\operatorname{MP}'(0).
\]

The MP uses inside PUSH and DISCARD are forced failures. In PUSH its cache
is a quantified formula of residue 2 modulo 4, while the compared implication
has residue 0. In DISCARD the first comparison is I(t,1)>0 against zero; the
last is I(Q_1(0),0)>0 against zero. Thus these retained contracts continue to
hold for arbitrary incoming t,w:

* PUSH, from zero d,h, never halts and returns `(0,[t;w],0,0)`.
* DISCARD, from zero d,h, never halts and returns `(0,w,0,0)`.
* H, from arbitrary d,h, halts if the original top is 1, or otherwise
  returns `(t,tail(w),0,head(w))`. The first ten transfers test only zero
  and the nine generated nonfalsity entries; the eleventh tests t.

Replace the ordinary MP-node compiler by

\[
\operatorname{DISCARD};\operatorname{PUSH};
 B_M;\operatorname{PUSH};B_A;\operatorname{PUSH};
 S;S;\operatorname{MP}'(Y);H.
\]

Its no-early-halt calculation is:

| Point | Current | Stack | Counter | Cache |
|---|---|---|---|---|
| After DISCARD; PUSH | 0 | [0;w] | 0 | 0 |
| After B_M; PUSH | 0 | [M;0;w] | 0 | 0 |
| After B_A; PUSH | 0 | [A;M;0;w] | 0 | 0 |
| After S;S | A | [0;w] | 0 | M |
| After MP′(Y) | Y | [0;w] | Y | 0 |
| After H | Y | w | 0 | 0 |

H removes exactly the reserved zero, preserving the desired theorem and
clearing the additive counter. If Y=1, its last transfer halts. Any earlier
halt during a recursively compiled premise or transfer also satisfies the
strong Build contract. This reserves a disposable zero explicitly, exactly
as the retained compiler does for its cache-return MP alternative.

Every other proof rule retains its existing block. Its MP uses are the
forced-failure uses just checked, or J(u)=MP′(u) for positive u with current
and cache zero. J(0) remains empty, since the raw alias I(0,0)=0 would make
MP′(0) succeed. Induction on finite numerical proofs therefore proves

\[
(t,w,0,0)\xrightarrow{B_X}\mathsf{halt}
\quad\hbox{or}\quad(X,w,0,0)
\]

for every theorem X and arbitrary natural t,w. The terminal B_1;H halts.
The unchanged prefix AX(0;1,z) clears d,h and yields the same cofinal family
of successful candidate indices. Every unsuccessful candidate still drains:
all commands terminate by their inherited natural-counter inductions, and
command pointer descent is unchanged.

## Protected blank startup

The actual initialization lands at source ordinal 136 inside the AX suffix,
well before the modified MP region. Both that literal source address and the
remaining startup suffix are unchanged. Hence the same nine explicit theorem
heads lie above opaque tail 4, with candidate 1 and residual pointer zero.
The retained conservative credit weights are S=-1, MP=0, AX=+10. The old
successful MP actually added one cell; the new MP preserves the stack, still
satisfying weight 0. Every other command is unchanged. Thus the existing
prefix-debt bound 2 and permanent protected margin 7 apply without alteration.
No unsafe head of tail 4 becomes exposed. The proof uses explicit ghost list
lengths, so it remains valid despite the Cantor alias P(0,0)=0.

## Scope

This is a complete ordinary source/command-level simplification. It preserves
the numerical proof calculus and Theory U. The PA-level endpoint can be
transported once a newly allocated binary table is proved to implement this
source and its blank initialization. No new full PA, Lean, Rocq, or MM0
certificate is supplied here, and no state-count improvement is inferred
merely from the smaller primitive count.
