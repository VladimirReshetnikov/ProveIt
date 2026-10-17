# Independent proof review: the monotone DROP barrier

## Verdict

The proposed abstract safe-start theorem is valid for the exact published
`Enum254` enumerator, with the hypotheses below. It does not require the
initial numerical theorem stack to contain only theorems. The proof exploits
the order in which the enumerator visits complete candidate command lists,
not merely the stack behavior of an arbitrary individual command program.

This review is an ordinary mathematical proof in ZFC. It is not a claim that
the new theorem has already been checked in Lean, or that the entire new
binary-machine simulation chain has been independently verified.

The reviewed definitions are in the pinned upstream
`ZF/m254/coq/logic/Enum254.v` and ProveIt's
`BusyBeaver/ZFC/Enum254.lean`. The existing arbitrary-state completeness
theorem is `EnumSafeStart254.complete_from`.

## Exact theorem

Write a six-register command-boundary state in the order

\[
 (\mathit{pl},\mathit{np},\mathit{tw},\mathit{ws},d,h).
\]

For every three natural numbers t,w,h,

\[
 \operatorname{HaltsFrom}(0,0,t,w,0,h)
       \quad\longleftrightarrow\quad C_{254}(1).
\]

Thus the proof-list pointer, next-candidate counter, and additive parameter
must start at zero, while all three formula-bearing registers may be
arbitrary. In particular w may encode falsity or nonderivable formulas.

The theorem is about a legal abstract command boundary. It does not permit
uninterpreted physical tape garbage, a malformed register encoding, an
arbitrary program counter, or a nonzero initial candidate number without
additional arguments.

## 1. Candidate syntax and its order

Use the actual Cantor pairing

\[
 P(a,b)=b+\frac{(a+b)(a+b+1)}2.
\]

It is a bijection from pairs of natural numbers to natural numbers and is
strictly increasing in each argument separately. The actual packing is

\[
\begin{aligned}
 \operatorname{pack}(\mathrm{MP}(x),r)&=P(0,P(x,r)),\\
 \operatorname{pack}(\mathrm{DROP}(x),r)&=P(1,P(x,r)),\\
 \operatorname{pack}(\mathrm{NIP}(x),r)&=P(2,P(x,r)),\\
 \operatorname{pack}(\mathrm{AX}(c,x,y,u),r)
   &=P(c+3,P(x,P(y,P(u,r)))).
\end{aligned}
\]

The last command has rest pointer r=0. A command followed by a nonempty
suffix L has rest pointer r=code(L)+1. These are exactly `pack` and `encL` in
the Lean source. The enumerator reads a new candidate n when pl=0, increments
np, and otherwise reads pl-1. It executes every command in one candidate
before advancing to the next unless it has already halted.

Every natural number n uniquely decodes to a nonempty finite command list.
After decoding the command fields, a nonzero remaining rest pointer r leads
to the next code r-1<n, since every pairing coordinate is at most the paired
number. Thus decoding terminates. The inverse pairing identities then show
that re-encoding the decoded list returns n. There are no discarded or
invalid candidate numbers.

For every nonempty list L with a distinguished NIP occurrence at position i,
let L' replace only that occurrence by DROP with the same x field. NIP and
DROP have the same arity, so all command fields and the complete suffix
remain aligned. At the changed command,

\[
 P(1,P(x,r))<P(2,P(x,r)).
\]

Every enclosing list context is strictly increasing in its suffix code:
adding one and composing the displayed Cantor packings preserves strict
order. Therefore code(L')<code(L), even when the changed occurrence lies
deep inside a candidate.

## 2. The marked-occurrence injection

Map the marked NIP occurrence (L,i) to the marked DROP occurrence (L',i).
This map is injective: from the output, replace that marked DROP by NIP,
leaving all other commands unchanged, to recover the unique input.

Keeping the occurrence mark is essential. Distinct NIP occurrences can map
to different DROP occurrences in the same earlier candidate, which is
exactly what the counting proof needs. It does not require the map from
unmarked candidate numbers to be injective.

Consider any finite execution prefix that has reached an occurrence in
candidate n. Every lower-numbered candidate has already executed completely;
otherwise candidate n could not have been reached. Hence the image of every
NIP occurrence in that prefix lies among DROP occurrences already executed.
The image of a NIP about to execute also lies in an already completed lower
candidate. Thus, writing D for the number of completed DROP commands and N
for the number of completed nonhalting NIP commands, immediately before any
NIP command one has

\[
 D\geq N+1.
\]

At every other prefix D>=N. These statements do not assume that the
enumerator never halts. For a reached prefix, any hypothetical earlier halt
is already excluded by the fact that the prefix was reached.

## 3. Candidate zero removes dirty formula registers

Candidate 0 decodes to the one-command list MP(0). With initial d=0, its
success branch produces tw=0, h=0, d=0 and pushes a 0. Its failure branch
also produces tw=0, h=0, d=0, leaving the stack unchanged. This conclusion
does not depend on the initial tw or h, or on which comparison succeeds.
The command cannot halt. The next candidate is 1 and pl is again 0.

Consequently, after candidate 0 both active formula registers contain the
truth code 0. The stack is a finite safe prefix, of length zero or one,
followed by the original arbitrary numerical stack w.

## 4. The protected-prefix invariant

Track an explicit finite list S of theorem codes above the original tail w,
so that the physical numerical stack equals fold-P(S,w). The representation
need not determine the length of S uniquely. In particular P(0,0)=0 causes
no problem: the inverse identity unP(P(a,b))=(a,b) applies whenever S is
nonempty.

After candidate 0, maintain:

1. tw and h are derivable in C254;
2. every entry of S is derivable in C254;
3. stack = fold-P(S,w);
4. |S| >= D-N.

Here D and N count completed DROP and nonhalting NIP commands in the global
execution from candidate 0. The possible truth pushed by the first MP only
improves the final inequality.

The ordinary MP, DROP, and AX soundness arguments preserve the first three
items. A successful MP derives its new top formula by modus ponens and
pushes truth; a failed MP returns truth. DROP pushes the old top formula and
copies the theorem-valued cache into the new top. AX pushes ten theorem
codes, including generalization of the old theorem-valued cache, and chooses
either an axiom bundle or truth as the new top. All additive parameter values
are permitted in these existing C254 rules.

A nonhalting NIP is the sole operation removing a stack entry. Immediately
before it, the marked-occurrence argument gives D-N>=1. Item 4 therefore
makes S nonempty. NIP reads a theorem from S and removes that entry; it never
reads an entry of the original arbitrary tail w. Both |S| and D-N decrease
by one. A halting NIP tests h=1 before any pop, and the invariant already
gives C254(h), so a halt proves C254(1).

This establishes the forward implication without assuming consistency of
C254. The argument applies to every finite execution until a halt. Neither
the potential presence of falsity in w nor the growth of the actual numerical
register values invalidates it.

## 5. Completeness from the same dirty start

The existing theorem `EnumSafeStart254.complete_from` states

\[
 C_{254}(1)\;\Longrightarrow\;\operatorname{HaltsFrom}(s)
\]

for every six-register state s, including states that fail the old complete
stack invariant. Its proof compiles a C254 derivation into a command program,
prepends an AX reset block, and pads the candidate code beyond the current
np counter. Every such later candidate is reached unless the run has already
halted. The compiled program works over arbitrary previous top and stack
values and forces a pair of NIPs after putting falsity into the cache.

Applying that theorem to s=(0,0,t,w,0,h) gives the reverse implication. Equally,
one can apply it after candidate 0 at np=1. No soundness premise about the
dirty initial stack is used in this direction.

## 6. What the binary-machine application still must check

The new abstract theorem removes the requirement `Good ws` at the first
root reached by the candidate 252-state binary machine. It also removes any
need to evaluate its enormous initial TW and WS registers or prove their
contents derivable. It requires only exact zeros in pl, np, and d, plus the
correct command-boundary interpretation.

To obtain a binary-machine theorem, the finite prefix certificate must still
establish a legal runtime frame and the subsequent simulation must apply to
the entire actual tape: register markers, head, dispatcher state, gap, and
all spare cells or other retained data. The DROP argument protects the
logical WS tail only. It does not itself prove that arbitrary physical
spare data is harmless or that a finite collection of macro tests establishes
all future binary steps.

Once those independent simulation obligations and the inherited C254/ZFC
consistency calibration are established, the displayed abstract equivalence
supplies exactly the missing soundness link from the observed dirty root.

## 7. Physical spare blocks: source-level resolution

The fetched canonical `Box.v` and `Sim.v` do admit nonzero spare register
blocks. In `Box.v`, all four `box_*` lemmas quantify an arbitrary list `vs`
of natural-number block values, subject to `length vs >= 9` and (for
decrement) the selected register's zero/nonzero test. The scan and shift
lemmas quantify the remaining block values without a zero restriction.
Increment preserves the complete later block list; positive decrement
preserves that list and appends a zero block.

Correspondingly, `Sim.Inv` includes an existential `ext : list nat` with no
`Forall (=0)` hypothesis. Its updates preserve ext, except that positive
decrement replaces it by `ext ++ [0]`. Thus retained nonzero spare blocks
are permitted when the complete tape has precisely this register-file form
with blank tape beyond it. This is a source-level proof fact, not a guess
that the machine will never scan the tail.

The existing `Sim` invariant is written for the fixed initial assignment R0;
the dirty-root application must parameterize that initial assignment by the
observed R. The induction and its `no_stray` call already treat the assignment
as data, so the required adaptation does not change the register-excursion
argument. The fetched `Site.v` uses D0=40. Applying it to the observed gap 37
still requires the candidate-specific site checks for exact gaps 37, 38, 39
and the affine family 40+n, as well as the modified table's register-excursion
proof. Those are distinct from the abstract DROP theorem.

## 8. Independent executable syntax controls

`check_drop_barrier.py` independently implements the displayed Cantor pairing,
its integer-square-root inverse, and the exact command field counts. It does
not import a register simulator or any binary-table macro interpreter.

For candidate numbers 0 through 99,999, every decoded list re-encodes to the
same number. The lists contain 124,708 commands: 23,049 MP, 1,971 DROP,
675 NIP, and 99,013 AX commands. All 675 marked NIP images are injective,
strictly earlier, and already present among executed marked DROPs. Every
command prefix has at least as many DROPs as NIPs, and the smallest
pre-NIP margin is one.

Three additional constructed mixed-arity examples check deeper positions
that do not occur in that modest numerical interval. They include a NIP at
position four in a 13,759-bit candidate code, nested behind two AX commands.
The check confirms the exact suffix alignment, strict decrease, and recovery
of the original candidate by changing the marked DROP back to NIP.

As a useful structural control, candidates 33 and 134 have marked NIPs whose
images both lie in candidate 26, at different marked positions. This shows
why the correct proof uses an injection between occurrences, rather than a
false injectivity claim about unmarked candidate codes.

The complete parameters, short counts, and nested examples are in
`drop_barrier_check.json`. Its input specification SHA-256 is
`7053323250fea46707e4aa0a0e62d32d6a599bd6bfd5f5b662da0bcd234162c8`.
The default check takes about 0.21 seconds in the review environment.
These finite controls catch coding and orientation mistakes; the structural
proof above supplies the unrestricted theorem.
