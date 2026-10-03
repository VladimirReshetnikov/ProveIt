# Deleting the width bound cannot be repaired by label constraints alone

The [63-operation source](native_dualrail_fifo63.md) explicitly pays for
6x+beta=W. Deleting its one addition, comparison and positive beta leaves
a literal62-operation source. A fixed controller on the four rail labels
cannot recover that bound on any of its properly initialized runs. The
same obstruction applies to a regular block filter on those labels.

This note also gives an effective decision procedure for the native
branch at each fixed width, including width1. It does not characterize
all solutions of the weakened source, prove variable-width decidability,
or rule out a different compiler for an overflowing arithmetic model.

## 1. Exact source invariance under decreasing the width

Keep the joint bound, packing and all retained Pell equations, and delete
only the equation I+beta=W and its defining addition from63, where I=6x.
The residual source costs62=33M+29A, with14 equations and25 positive
existential coordinates besides x. Its unchanged transport and geometry are

    D=6x+WA, q=WL, A+D+alpha=q.                         (1)

The [checker](input_bridge_width_descent.py) audits this exact deletion
and all remaining polynomial residuals, including the auxiliary-norm
correction. No exact native-typing theorem for the weakened source is
assumed in the count.

Suppose there is a positive solution with genuine native words, W=3^m,
m>=2, and A>=1. Take any smaller power W'=3^m' with1<=m'<m. Set

    x'=x+(W-W')A/6, W'=3^m', L'=(W/W')L.               (2)

Keep every other supplied coordinate unchanged. The difference W-W'
is divisible by6, so x' is a positive integer and L' is a positive
integer. Substitution preserves every polynomial in the weakened source:
6x'+W'A=6x+WA and W'L'=WL, while the fields, q, r, joint bound and all
Pell coordinates are untouched. This is also verified symbolically for
every residual, not just for the two displayed equations.

Moreover W>=3W' and A>=1 imply

    6x'=6x+(W-W')A>W'.                                 (3)

Thus every such solution yields a positive solution violating the deleted
bound. In particular any properly initialized run has W>6x>=6, hence
m>=2, and its first append rail guarantees A>=1. Taking W'=3 always
produces an overflowing solution.

The transformation keeps the entire four-label word, its length, every
fixed carry path and its endpoints unchanged. Consequently it preserves
any additional condition depending only on those words, q and fixed
program data, including arbitrary label languages and regular block-code
filters. It does not preserve additional conditions involving W or x;
such conditions would be extra compiler or arithmetic obligations.

This proves a precise obstruction: a label-only controller that admits
any proper bounded run cannot make all witnesses satisfy I<W after that
equation is deleted. It does not prove that the overflowing model itself
is nonuniversal.

## 2. Positive witnesses and the separate width1 issue

An explicit instance has q=27, fields(F0,F1,F2,F3)=(14,13,25,16),
A=1,D=15,r=333518 and alpha=11. At x=1,W=9,L=3 it is the proper
three-step run from6 to zero with append trits(1,0,0) and read trits
(0,2,1). The source63 converse supplies every positive Pell coordinate.
After deletion, (2) gives x'=2,W'=3,L'=9, with the same fields, r and
Pell coordinates. Its initial value is12>3. Both queue trajectories
become5 after the first step, then1, then0; the label words coincide.
This exhibits the full positive extension without materializing the
enormous auxiliary kernel tuple.

Deleting the width bound also allows W=1. There is a separate native
example with q=27,x=1,W=1,L=27 and fields(14,13,17,16). It has A=1,
D=7, alpha=19 and even native packing. The exact four-field converse
again supplies the retained positive kernel. But its first scalar read
is1, whereas I=6 is0 modulo3. Thus even after assuming native typing,
the weakened source does not always describe the usual FIFO recurrence
with read=N modulo3. The factor W/3 would not be integral here.

## 3. Exact native arithmetic dynamics at every fixed width

For W=3^m with m>=0, native scalar words D,A and initial I=6x, the
equation D=I+WA has an exact uniform interpretation. Starting N0=I,
choose the next scalar append a and read d in{0,1,2} subject to

    N+Wa-d divisible by3, N_next=(N+Wa-d)/3.            (4)

Because d is one of0,1,2, it is necessarily the remainder of the
nonnegative integer N+Wa. Hence N_next>=0. The prefix residual identity
shows that (1) holds exactly when the resulting t-step path ends at0.
For W>=3 this reduces to read=N modulo3 and
N_next=floor(N/3)+(W/3)a. For W=1 it instead has
d=(N+a) modulo3. These are distinct interpretations of the same
arithmetic transport, not a free standard-FIFO inference.

For a fixed x and W, all these numerical states lie in the finite range

    0<=N<=max(6x,W),

because floor((N+2W)/3)<=max(N,W). Couple this state to the fixed
affine carry controller

    3k_next=k+h+sum_i ci*label_i.

Its carry is confined to[-B,B], where
B=max(abs(cs),ceil((abs(h)+sum abs(ci))/2)). Add a carry e in{0,1}
for adding the represented scalar words A and D:

    e0=0, e_next=floor((e+a+d)/3).

At the end e=0 is equivalent to A+D<3^t. Finally retain a finite age
counter capped at max(1,m). On the first edge require append rail0=1;
accept only after age reaches its cap, N=0, k=cf and e=0.

This finite graph decides existence of a native word for the specified
x,W and fixed controller. The age condition enforces positive length
and q=3^t divisible by W. Every accepted path gives positive native
fields Fi=H+Bi, with F0's units digit2. Transport with even I and odd W
gives sum Fi even, hence even packing. The central-binomial carry mask
and the complete four-field converse then supply all positive retained
Pell coordinates. Conversely every native solution gives exactly such
a path. Arbitrary additional fixed finite-state label filters can be
included by a finite product of state graphs.

This is a uniform effective procedure from the fixed coefficients,
endpoints, numerical input and fixed width: the state ranges and all
edges are explicit, and ordinary graph reachability terminates. No
eventual-periodicity cutoff, unbounded search or external automata
theorem is needed. No claim is made here that a variable-width solution
must have one of finitely many widths; that would require another proof.

## 4. Evidence and scope

The checker audits the literal62 deletion and proves (2)'s symbolic
invariance of every source polynomial. It checks both positive native
examples, their parity and binomial valuations. For fixed widths1,3,9,
several small controllers and inputs, it compares direct whole-word
arithmetic against the local finite graph on all four-label words
through length3. It separately runs the terminating reachability
procedure and compares its short witnesses with that enumeration.

The [receipt](input_bridge_width_descent.json) records these focused
checks. The universal assertions above are mathematical proofs; the
large positive kernel extension remains parametric. Independent full
proof/source/default review PASS (pell_kernel), with no findings. The established complete universal bound remains76.
