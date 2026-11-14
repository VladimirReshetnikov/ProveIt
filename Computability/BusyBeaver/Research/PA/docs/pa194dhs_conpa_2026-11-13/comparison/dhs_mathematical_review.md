# Independent mathematical review of the Gamma(D) hybrid

## Scope and verdict

I read the original PA195 calibration, the separate-head calibration,
the PA194D Gamma(D) appendix, and both current HS/NS command proofs.
I also inspected the upstream Lean constructions in
`PA196/Logic/{Reverse,Neighborhood,Vacuity}.lean` and searched their
arithmetic certificate copies for uses of equality vacuity.

I found no mathematical defect in the new command-level transfer from
Gamma(A) HS/NS to Gamma(D) HS. The combined source needs a fresh zero
invariant because successful no-push MP retains the offset instead of
clearing it. The construction has supplied that fresh invariant; reuse
of the old PA194D closure without recomputation would not have sufficed.
This review does not assert an end-to-end proof-assistant theorem or a
fresh formalization of the inherited PA-refutation compiler.

## New command transfer

Let `p(a,b)=((a+b)(a+b+1))/2+b`, `[a;w]=p(a,w)`,
`I(a,b)=4p(a,b)` and `U(i,a)=4p(a,i)+2`. The hybrid's store is
`(t,w,d,h)`. Its Shift halts exactly at `h=1`; otherwise it gives
`(h,tl(w),d,hd(w))`. For `b=d+x`, successful MP gives `(b,w,b,0)`
when `I(t,b)=h`; failed MP gives `(0,w,b,0)`.

AX has top equal to the unchanged guarded separation gate and stack
`[q1,...,q9,t;w]`, clearing `d,h`. The sole logical-emitter change is
`q1=Gamma(D)` instead of `Gamma(A)`, where `D=old_d+x`,
`Gamma(B)=I(B,U(B,B))`. The other emitted heads retain their complete
formula trees and parameter correlations. Thus every calculus axiom
family remains available: choose the free offset parameter to make
`D=B`. Conversely every new diagonal output is an instance of the
same diagonal family. No replacement of the underlying proof theory
or a new consistency-strength argument is needed.

The first eight generated entries and the gate have residue zero mod4,
and `q9=U(old_d,old_h)` has residue two. They cannot be code one.
Consequently:

- `AX;S^9` gives `(q8,[t;w],0,q9)` for every incoming store.
- `AX;S^10` gives `(q9,w,0,t)` for every incoming store.
- `Push=AX(0,0,0);S^9;MP0` gives `(0,[t;w],0,0)` because
  its last comparison is between residues zero and two.
- `Discard=MP0`, when `d=0`, gives `(0,w,0,0)` in both MP branches.
- `Pop=AX(0,0,0);S^11` halts exactly when the old top is one,
  otherwise sends `(t,[a;w],d,h)` to `(t,w,0,a)`.

The numerical aliases `p(0,0)=0` and `I(0,0)=0` do not invalidate these
calculations: both Cantor projections satisfy their constructor equations
also at zero. No stack-length injectivity is assumed.

The changed diagonal selector from an arbitrary `(t,w,0,0)` is exactly

`MP0 ; AX^D(0,B,0) ; S^2 ; Pop^8`.

It returns `(Gamma(B),w,0,0)`. The last Pop consumes the saved zero and
clears the cache. Since the selected head is not one, this selector is
total. Selectors for the six other heads, the dominated propositional
head, and the guarded gate are unchanged. Generalization uses

`Push ; MP_i ; S ; AX^D(i,0,0) ; S^10`.

Its intermediate Shift tests a zero cache and loads the arbitrary premise
formula into the cache; AX consumes that formula before it can be tested
again. Thus the calculation remains valid even for premise code one.

For modus ponens, reserve a zero before compiling the major and minor
premises. The resulting suffix begins at
`(0,[a,I(a,b),0;w],0,0)`. The first Shift loads `a`; the second either
halts at `a=1` or presents the exact MP pair. MP returns
`(b,[0;w],b,0)`. Pop either halts at `b=1` or gives `(b,w,0,0)`.
The reserve is essential: without it Pop would consume the caller's tail.

Induction on a numerical derivation proves the halt-or-return compiler
invariant for arbitrary caller top and tail. Given a derivation of one,
`AX^D(0,0,0); compiled-proof; Pop` halts from every four-component store.
The first AX clears offset and cache; the final Pop tests the proved top.
This is the appropriate interface for the scheduler, which retains stores
between candidate words rather than resetting them.

## Scheduler and PA internalization

The HS/NS proof supplies explicit positive continuation encoding. For a
continuation `z`, the raw AX code is `p(A+2,p(y,p(x,z)))`: the field order
is **y then x**. A positive continuation first subtracts one, and its
residual is at most that raw code, hence strictly smaller than the incoming
positive continuation. Every candidate therefore finishes or halts.

Prefixing the all-store halting word by `AX(k,0,0)` gives the unbounded
fresh-candidate codes `p(k+2,p(0,p(0,z)))`. The scheduler's initial counter
two loses no refutation. A bounded iteration through a sufficiently large
candidate constructs a finite halt or detects an earlier halt. These are
primitive-recursive syntax/trace constructions with PA-provable
correctness; no reset or external standard-model exhaustiveness is assumed.

For soundness, annotate top, cache and each canonical stack entry with
derivations or translated PA proofs. AX adds axioms and a generalization
of the old cache. Successful MP performs actual inference; failed MP gives
truth. Shift transports annotations and a halt exposes an annotated one.
The offset requires no theorem annotation. The canonical finite Cantor
tail strictly decreases when nonzero; popping zero supplies the fixed
truth proof, so the annotation invariant also handles collapsed zero tails.

## Inherited calibration checks

The replacement of equality vacuity by diagonal vacuity is the delicate
logical part. The supplied reverse-membership argument takes
`C=E(a,b) -> (chi(b) -> chi(a))`, `phi=not C`, and separator
`c=code(phi)`. Code freshness makes this label absent from phi and satisfies
the gate guards. The available `Gamma(phi)` supplies precisely the vacuity
needed to generalize under phi. The negative specialization lemma uses
only direct membership rewriting, an equality witness and membership
vacuity. The removed primitive equality-vacuity schema is not smuggled
back into that step. Cases where the fixed membership label equals `a`
reduce through the separately handled diagonal membership case.

For neighborhood equality, the first binder is `code(E(a,b))`; diagonal
vacuity provides the needed equality antecedent there. Existing witnesses,
bidirectional membership rewriting, and membership-only vacuity transport
the binder to an arbitrary allowed label. In the upstream code, direct
equality-vacuity uses affecting the PA refutation transport occur in
Reverse and Neighborhood (and their arithmetic certificate copies), which
are exactly the interfaces replaced by these arguments.

The opposite interpretation uses finite binary membership. Uniform finite
comprehension is proved by an induction proof template with the input
formula substituted syntactically, not by a truth predicate for arbitrary
PA formulas. The proof supplier never evaluates the formula. The gate's
`a=b` label collision has its own singleton matrix because both occurrences
are bound together. Translation handles code zero by a proof of a
constructor equivalence instead of asserting false syntactic injectivity.
I found no reflection principle, appeal to PA's truth, or unmentioned
consistency assumption in these steps.

The new machine's theorem may therefore cite this ordinary syntactic
calibration as an explicit inherited mathematical dependency. It must not
be presented as a newly elaborated kernel theorem or as completing the
separate iPRA endpoint.

## Seed specialization and physical connection

The ordinary Gamma(D) hybrid source must be distinguished from the two
known-zero-specialized jumps in the literal source. The fresh construction
receipt reports a common closed positivity relation of 263,236 pairs,
with changed sites 26 and 3553. At 26, bit6 (scratch X) is zero in every
listed mask; at 3553, bit4 (D) is zero. The relation is recomputed for the
new source and its successors agree with those of the ordinary source.
Finite closure plus induction yields exact source-run equality from the
clean seed, which is enough for the theorem. It does not claim arbitrary
store equality of the specialized source.

The construction receipt binds the candidate to 194 working states,
3,650 source sites, 4,752 primitive outcomes, 40 simultaneous fold cases,
and a complete 58,014-step blank startup. The separate literal replay is
now complete: its PASS receipt reports all 4,752 outcomes, two agreeing
control-flow resolvers, four literal list lemmas, 1,096,025 symbolic steps,
a maximum of 385 symbolic steps for one outcome, and a minimum duration
constant of three. The independent blank simulation agrees on the entire
tape and zero exterior. Positive exact
source-to-tape segments plus startup give both finite-halting directions:
a supposed physical halt at time T cannot coexist with T+1 completed
nonhalting source steps, since their positive segments extend the same
deterministic run beyond T.

The novel table was independently compared with all 34 supplied frontier
graphs using exact canonical tuples under every spanning root, reflection
and symbol interchange. There were no matches. Its dense SHA-256 is
`2c5385ddcb928af834c1b959058d5fdc9e01b1d2be3ee9cf7c50557e45bfb48e`.

## Final proof and script review

Read the final `proof_dhs.tex`, construction `build.py`, the free-term
command checker, and the independent physical verifier. No substantive
defect was found. The command equations explicitly require the inherited
command boundary with scratch X zero; they do not quantify over arbitrary
dirty physical scratch. The semantic distinction can be illustrated with
the satisfiable numerical input `(t,w,d,h)=(0,0,0,20)`: MP2 produces
`(2,0,2,0)` and a following zero-parameter Gamma-D generator emits
Gamma(2)=5712, whereas the Gamma-A hybrid emits Gamma(0)=20. This example
does not rely on carrying a proof of contradiction.

The final statement correctly retains its proof boundary: an ordinary
mathematical argument formalizable in PA, with executable finite and
universal symbolic certificates, relying on the explicitly supplied
logical calibration. The exact native-table SHA-256 is
`2775e4a43f13c7713a41ccade6963bdf612ff9d2dbd6e5239122f588f1abc8d6`.
