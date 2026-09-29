# Native ternary controller encoding: bounded findings

This is a research note, not a compiler or a universal operation bound.
The six/eight-operation queue-stream component requires the finite controller
to certify four synchronized trit streams on exactly the same base-three
time positions. A larger fixed cell radix cannot be substituted without
an explicit digit conversion.

## A sound but expensive baseline

Let T_e be Boolean base-three selector streams for the edges of a fixed
finite-state transducer. Assume that exactly one edge is selected at every
time position; this is an unpaid typing obligation here. The four read and
append streams are linear sums sum_e digit(e) T_e. Their digit coefficients
are in {0,1,2}, so under one-hot selection no carry occurs.

Encode states in k ternary digits. For each state-digit position a, let
O_a=sum_e code(source(e))_a T_e and
I_a=sum_e code(target(e))_a T_e. For a fixed starting state s and final
accepting state f, enforce

    O_a + q code(f)_a = code(s)_a + 3 I_a.

Both sides describe ordinary bounded trit words, with disjoint endpoint
positions. Their equality forces the initial state, every adjacent state
match, and the final state. The true zero queue is reached in the accepting
control, so fixing that endpoint does not restrict completeness.

This gives an exact finite compiler once one-hot typing is paid, but the
linear forms cost operations proportional to the transition table. For a
single digit form containing n1 coefficient-one edges and n2 coefficient-two
edges, grouping equal coefficients costs n1+n2-1 additions when nonempty,
plus one multiplication if n2>0. Every computed form and the state-flow
instructions must be charged. No small total count has been obtained.

Choosing accepting-control code0 and initial-control code1 simplifies the
endpoint schedule: O_0=1+3I_0 and O_a=3I_a for a>0. Once O_a,I_a are
bounded by q and their trit meanings established, these relations force
the top trit of every I_a to vanish, hence the terminal state is0. This
costs only k multiplications and one addition after forming the planes;
the potentially expensive edge selection and linear forms remain.

## Two shortcuts that do not work by themselves

1. Boolean T_e and sum_e T_e=(q-1)/2 do not enforce one-hot selection.
   For q=9, four selector streams each equal1 sum to4, the ternary word11.
   All four edges occur at time zero and none at time one. The issue is an
   ordinary carry between native time digits.

2. A scalar state code larger than one trit does not permit coefficientwise
   state-flow extraction. With state codes0,1,2,3, select edge3->1 at time0
   and edge0->2 at time1. Then O=3, I=1+3*2=7, q=9, and
   O+q*2=3I+0, although the first selected source is not the initial state0
   and the two edges do not join. The selected edges can have valid distinct
   input/output labels in one fixed deterministic transition table; this is
   a false controller path, not an asserted full queue counterexample.

More generally, no fixed integer scalar codes for S>3 states yield an
injective encoding of *all* length-t state words at native ternary positions
for every t. After translating the least code to zero, let C be the largest
code. There are S^t words but at most C(3^t-1)/2+1 possible encoded integers.
Eventually the former is larger. Free arbitrarily large numerals only
increase the length at which collisions are forced. For k integer-valued
coordinate codes, the same argument gives at most O(3^(kt)) images, so
S>3^k forces collisions.

This is only an obstruction to an injective native fixed-linear coding of
arbitrary state words. It is not a lower bound for a particular controller's
valid paths, a controller compiler with nonlinear masks or extra witnesses,
or a universal Diophantine certificate. Restricting the language, proving
additional structure, or using paid digit planes may avoid these examples.

The raw bound x<L in the queue initialization is also retained. None of
these controller observations makes input carrying harmless.
