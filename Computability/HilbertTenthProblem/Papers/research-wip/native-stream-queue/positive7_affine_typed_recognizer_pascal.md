# An affine-edge unary recognizer with one global nonnegativity condition

This note replaces the closed unary recognizer's repeated counter-type atoms
by one global `omega_1(N)` condition and gives a literal machine whose 46
running branches are integer affine lattices. The resulting accepted unary
set is exactly the previously fixed universal set U. Each bare affine branch
has a direct finite subgroup-word list inside the same fixed nine-generator,
twenty-relator group A. No numeric size of a complete benign presentation,
universal relator list, matrix alphabet or Diophantine circuit is claimed.

Root proposed global omega_1 typing and the direct affine-base route. Pascal
derived the shorter partial loader and checked the literal table, branch
counts and both acceptance directions. Aristotle independently supplied the
general affine-orbit/retraction argument and the separate common-ambient
construction. The persistent presentation theorem and its counts are not
part of this note.

## 1. Fixed conventions and inherited input set

Use the finite-support integer functions and Higman primitive conventions of
the frozen `positive7_higman_unary_recognizer_root.md`, Sections 1--2. In
particular sigma shifts right, rho reflects indices rather than signs,
and omega_d imposes its input relation on every aligned d-block. Write

    Left = rho pi rho;  Right_j = sigma^j pi sigma^-j;
    Block_d(E) = Right_(d-1) Left E intersect Box_d.

The two liberations extract the displayed coordinates from a single witness;
they do not require its other coordinates initially to vanish. The imported
finite expressions Eq, S, C_j and N define equality, successor, the singleton
j, and the nonnegative integers respectively. Only C_0 through C_31 are
needed. Every affine relation displayed below also has a finite H expression:
use the fixed tag singletons, Eq, S and zero singletons in the parent's exact
window-cylinder macros. The direct group recipe in Section 4 is a different,
shorter way to represent these particular relations; it does not change the
definitions of the Higman primitives.

Retain the literal eight-register U21 machine K and its enumeration

    S_e = {x>=1 : K started at 0 on (0,e,x,0,...,0) halts},
    U = {2^e(2x+1) : e>=0 and x in S_e}.                 (1)

The source is `korec_packed_counter_units.md`, Section 1, including its
strong-universality input convention. This note independently checks the
table transformations below; it imports that source's universality theorem
and does not re-audit Korec's complete proof.

## 2. The complete increment/decrement machine

An instruction I j t increments R_j and goes to t. A full D j t z decrements
R_j when positive and goes to t; when zero it preserves the counters and
goes to z. D+ j t has only the positive decrement edge and no zero edge.
It is a partial instruction, not a halting instruction. State 21 is the only
halt; state 22 is the start. The exact nonhalting table is:

| State | Instruction | State | Instruction |
|---:|:---|---:|:---|
|0|D 1 1 2|16|I 2 20|
|1|I 7 0|17|D 4 0 21|
|2|I 6 3|18|D 0 0 17|
|3|D 5 2 4|19|I 0 0|
|4|D 6 5 3|20|I 3 17|
|5|I 5 6|22|D 0 23 25|
|6|D 7 7 8|23|D 0 24 28|
|7|I 1 4|24|I 2 22|
|8|D 6 29 0|25|I 1 26|
|9|D 4 0 10|26|D 2 27 22|
|10|D 5 11 12|27|I 0 26|
|11|D 5 13 14|28|D+ 2 30|
|12|D 2 17 18|29|I 6 9|
|13|D 5 15 16|30|I 2 0|
|14|D 3 17 19|||
|15|I 4 10|||

There are 13 increment instructions, 16 full decrements and one partial
positive decrement. Thus Run has exactly

    13 increment + 17 positive-decrement + 16 zero branches = 46. (2)

For clarity the increment states are
1,2,5,7,15,16,19,20,24,25,27,29,30; the full-decrement states are
0,3,4,6,8,9,10,11,12,13,14,17,18,22,23,26; the partial state is 28.
These lists and the table specify every branch and target, without an
instruction evaluator or a search. Live tags q+1 range from 1 to 31.

The old K test at state 8 is replaced by decrement 8 followed, on its
positive branch, by restore 29. On zero it still goes directly to 0.
At the next old checkpoint this preserves every register and target. The
loader's positive-input test is similarly decrement 28 then restore 30;
its zero branch is absent. No K instruction targets a loader state.

Start with (R0,...,R7)=(n,0,...,0). At a visit to 22 with positive R0=N,
R1=e and R2=0, states 22--24 consume pairs of units and accumulate their
number in R2. If N is even, state 22 finishes with (0,e,N/2,0,...), state
25 increments e, and states 26--27 transfer the quotient to R0. The next
visit to 22 has (N/2,e+1,0,...), with a strictly smaller positive dividend.
Both inner loops terminate by decrementing their source counter.

If N is odd, state 23 detects that the last unpaired unit was already
removed. State 28 then sees (0,e,(N-1)/2,0,...). For a positive quotient,
28--30 restore it and enter K at state 0 on precisely (0,e,x,0,...).
For quotient zero the machine is stuck at nonhalting state 28. Thus every
n>0 either is a power of two and gets stuck, or enters K with the unique
parameters in (1), and thereafter has exactly K's halting behavior.

For n=0 the machine follows 22 -> 25 -> 26 -> 22 indefinitely. It increments
only R1 once per cycle; R0 and R2 stay zero. It never enters K or reaches
state 21. Therefore the new partial machine M_aff satisfies, including n=0,

    M_aff halts on n>=0 if and only if n belongs to U.    (3)

The reverse direction follows the same finite division and restoration
steps for n=2^e(2x+1) with x>=1, followed by the given finite K run. This is
accepted-set equivalence with the former loader; the changed machines do
not have literally identical full history sets.

## 3. Explicit affine branches and one global type condition

A live configuration is c=(q+1,R0,...,R7). In an 18-window the current
configuration occupies sites 0,...,8 and the next occupies 9,...,17.
Let delta_i denote the unit vector at site i, set

    h(q,t)=(q+1)delta_0+(t+1)delta_9,
    v_i=delta_i+delta_(i+9),  i=1,...,8.

The bare affine branch lists are the following sets; every span is over Z:

    I j t at q:
      h(q,t)+delta_(j+10)+span(v_1,...,v_8);
    positive D j t at q:
      h(q,t)+delta_(j+1)+span(v_1,...,v_8);
    zero D j z at q:
      h(q,z)+span(v_i : i!=j+1).                         (4)

For positive D the active span parameter is the next counter, so its current
counter is one larger. This includes the sole edge at state 28. Let Run_bare
be the union of the 46 relations (4), and set

    Clear_bare = 22delta_0+span(delta_1,...,delta_8);
    Restart = span(delta_9,...,delta_17);
    R_bare = Run_bare union Clear_bare union Restart;
    H_bare = omega_18(R_bare) intersect sigma^-9 omega_18(R_bare);
    Hist_aff = H_bare intersect omega_1(N).              (5)

Clear_bare has next block zero and current tag 22, the unique halt's tag.
Restart has current block zero and arbitrary next block. The all-zero
18-block belongs to R_bare, and zero belongs to the one-supported N. Both
omega inputs therefore satisfy the corrected benign-wrapper prerequisites.
`omega_1(N)` means exactly that every scalar entry of the finitely supported
history is nonnegative; there is no duration-dependent conjunction.

Here is the precise typing equality, separate from (3). Fix this branch
table, or any finite I/D table with positive live tags. Define R_typed by
adding N to both endpoint counters in every Run branch and to every current
counter in Clear; leave Restart unchanged. Then

    omega_18(R_typed) intersect sigma^-9 omega_18(R_typed)
      = H_bare intersect omega_1(N).                    (6)

For the forward inclusion every nine-block is the current endpoint of an
edge, by the two alignments. A Run/Clear source has nonnegative counters
and a positive fixed tag; a Restart source is wholly zero. Hence all scalar
entries lie in N. For the reverse inclusion the global condition types both
endpoints of every edge, restoring every deleted N atom. In particular an
edge with current=next+1 has a positive current counter. This proves (6)
for entire finite histories, even histories with several restart episodes.
It does not assert equality of the bare and typed local edge relations.

Take Reach_aff=Block_9(Hist_aff). A nonzero initial block with a live tag
must follow actual machine edges until it reaches the first future zero
block, which exists by finite support. The edge into that zero block cannot
be Run (positive target tag) or Restart (zero source). It must be Clear,
so the episode reaches state 21. A stuck state 28 cannot simply disappear:
it has neither an applicable Run edge nor a Clear/Restart exit.

Conversely a finite accepting run, followed by a zero block and padded with
zeros on both sides, satisfies (5). Restart admits its initial entry, and
all machine configurations have nonnegative scalar coordinates.

The initial relation can now be the affine line

    Init_aff=23delta_0+span(delta_1) in the nine-window.

Intersect it with Reach_aff, existentially forget sites other than 1 using
the parent's Keep macro, and shift by sigma^-1. Hist_aff itself imposes
n>=0; (3) rejects its remaining extra value n=0. The resulting unary set
is exactly E_U. No Pos atom or test branch is needed in this construction.

## 4. Fixed-A lists for every affine branch

Use the primary notation b_i=c^(-i)bc^i, a_f=a^(product_i b_i^f(i)), and
d_i=e^(-i)de^i. The products are in increasing index order. The fixed group
A and its nine generators/twenty relators are equation (5.10) of
[Mikaelian v8](https://arxiv.org/pdf/2507.04347v8), Sections 5.2--5.3.
Its embedding of F3=<a,b,c> and Lemma 5.12 are imported group-theoretic
premises. That lemma explicitly states both signed shifts

    a_f^(d_i)=a_(f+delta_i),  a_f^(d_i^-1)=a_(f-delta_i). (7)

For fixed finite-support integer vectors f0,v_1,...,v_k, put

    w_j=product_i d_i^(v_j(i)),
    L(f0;v_1,...,v_k)=(a_f0,w_1,...,w_k).               (8)

Then, writing Lambda=f0+span_Z(v_1,...,v_k),

    F3 intersect <L(f0;v_1,...,v_k)> = <a_f:f in Lambda>. (9)

Indeed (7), applied repeatedly with either sign, shows that conjugation by
any word in the w_j translates the subscript by its exponent-vector sum.
Every lattice point is reached, including negative coefficients. Collect a
word in <L> into a product of conjugates of a_f0 and its inverse, followed
by a residual word w in <d,e>. Its conjugates all belong to the right side
of (9). The presentation of A admits a retraction onto the free group on
d,e: send its other seven names to identity; all twenty relators vanish.
The inclusion of the pure d,e group splits that map. If the collected word
belongs to F3, its residual w has trivial retraction and is therefore the
identity. This proves the reverse inclusion without a word-problem test.

Apply (8) literally to each of (4), Clear_bare, Restart and Init_aff. An I
or positive-D branch has nine listed words; a zero branch has eight; Clear
has nine, Restart ten and Init two. These are finite subgroup-list lengths,
not new ambient group relators. The 46 Run lists contain 398 word occurrences
in total; adding Clear and Restart gives 417 across 48 alternatives. This
is only a check of the displayed list recipe, not a count of their subsequent
union, omega, extraction or final presentation construction.

The same lemma directly gives Eq with list (a,d_0 d_1), S with
(a^(b^c),d_0 d_1), tau S with (a^b,d_0 d_1), and the signed opposite-pair
set with (a,d_0 d_1^-1). Their older finite H expressions remain valid.
No commutativity of d_0,d_1 inside A is used.

## 5. One affine pattern and one unary cylinder

Root further observed that the final commutator pattern itself is the affine
line P=f0+Z*v in the ten-window, where

    f0=(0,0,1,0,1,0,-1,0,-1,0),
    v =(0,-1,0,1,0,-1,0,1,0,0).

It has the direct two-word list (8) in the same fixed A. Define the full
unary cylinder

    C_U = sigma^3 (Left pi E_U).

For a one-supported E_U, pi first frees all positive sites and Left then
frees all negative sites. They preserve its site 0 and one underlying
E_U witness. Thus C_U is exactly the finitely supported functions whose
site 3 belongs to U. Both directions use only finite-support patching.
The coefficient of v at site 3 is one, so

    P intersect C_U
      = {(0,-n,1,n,1,-n,-1,n,-1,0):n in U}=X_U.          (10)

This uses pi, rho, pi, rho in application order, the fixed shift by three,
and one intersection after E_U. At the group-compiler level it uses the
tracked fixed A to represent P; it needs no separate signed opposite-pair
or omega_4 construction. The shift has a cost unless a separately proved
persistent shift mechanism is supplied. Equation (10) does not count it as
a free general Higman primitive. The frozen conditional pattern expression
remains valid, and its explicit even-a/odd-b convention is unchanged.

## 6. Retained boundaries and remaining compilation

**Remark 1 (a bare decrement is not a typed local transition).** The signed
pair current=0,next=-1 lies in a positive-D affine branch. It is excluded
only when the global omega_1(N) condition is restored. Thus deleting local
type atoms preserves (6), not the unguarded edge relation. Every use of
machine semantics above follows that global typing step.

**Remark 2 (partial termination is not acceptance).** Deleting the old
rejecting loop is justified by the accepting-path history semantics, not by
calling an instructionless configuration a halt. Powers of two reach state
28 with R2=0 and are rejected. Adding a zero edge from that state to K would
admit the wrong ordinary-input interface x=0, whether or not a particular
body computation at x=0 happens to halt.

**Remark 3 (signed translations do not make the stable letters commute).**
Equation (7) makes their actions on a_f commute. The pure d,e subgroup is
free, and d_0,d_1 do not commute in that subgroup. Replacing the residual
word in the proof of (9) by its abelianized exponent data would be unjustified.
The retraction and split inclusion, rather than such a replacement, prove (9).

**Remark 4 (retained preliminary count correction).** Root's tentative
message suggested sixteen positive-D branches. There are seventeen: the
sixteen full decrements each contribute one and the partial instruction at
28 contributes the extra one. The correct partition is (2), totaling 46.

**Question 1 (the actual common-ambient compilation).** Combine these fixed-A
lists with the independently proved union/intersection, persistent-marker,
omega and extraction recipes, retaining all named embedding and subgroup
words. This note supplies their recognizer semantics, not a completed
presentation or a numeric universal operation bound. The separate persistent
presentation theorem should be bound only after its own review and freeze.

Evidence is inert text/primary-source reading and handwritten reasoning only.
No scientific code, instruction-table evaluator, supplied/frozen helper,
stored source array, symbolic computation, degree propagation or build was
run. The receipt records the exact read spans.

Root read the complete 300-line mathematical draft and independently passed
the literal table/counts, both loader directions, global typing equality,
delimiter argument, affine-base retraction and pattern cylinder. His only
requested edit corrected the Section 1 cross-reference from Section 5 to
Section 4; no mathematical change was requested. The final edits are that
reference and this provenance/status. This proof and its byte/read-span
receipt are frozen after that full challenge. The separately forthcoming
persistent presentation/count theorem is not implicitly certified here.
