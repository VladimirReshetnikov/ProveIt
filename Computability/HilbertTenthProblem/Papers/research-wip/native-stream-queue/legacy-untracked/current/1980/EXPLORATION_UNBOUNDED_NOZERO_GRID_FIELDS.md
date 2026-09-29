# An unbounded nozero alias in the lower fields of 102

Removing the positive supplied variable Z and its equation Z+D=H from
the undoubled102 construction leaves a substantive proof obligation.
The remaining counter equations and the first eight Boolean mask chunks
do **not** imply D<H, or even D<q. The following family has D=q+H and
formal Z=H-D=-q. Its counter values satisfy the actual numerical time
equation, but one supplied track is not Boolean.

This is a lower-subsystem obstruction. It does not satisfy or refute
the complete program route. No full smaller schedule, program typing,
packed Pell extension, or impossibility for the complete construction
is claimed. In particular it does not refute the separately proved
doubled101 construction, which retains positive Z.

## Construction and exact counter equations

Choose any even m>=4 and set

    R=3^m, k=(R-3)/6=(3^(m-1)-1)/2, x=(k+1)/2.

Here k is odd and x is a positive integer. Start three ordinary counters
at (2x,0,0). Use one six-step bank pair with signs +++---, followed by
x copies of the six-step sequence -++---. Each latter pair subtracts
two from counter zero and preserves the other two counters. Thus the
height is u=6(x+1), all counters remain nonnegative, and the endpoint is
(0,0,0). The largest source value is k+2<R/3.

Let q=R^u, W=R^3, H=(q-1)/(R-1), and J=(q-1)/2. Let Kplus,Kminus
be the ordinary row-head words recording these signs. At every source
row except the first, split its ordinary ternary digits between two
Boolean tracks in the usual way: a digit two contributes one to each
track and a digit one contributes one to either track. Each such local
track value is at most k, because the source value is below R/3.
At the first row instead put

    A0_initial=k+1, A1_initial=0.

The sum of the tracks is unchanged, so the exact numerical identity is

    W(A0+A1+Kplus-Kminus)=A0+A1-2x.

Both global supplied tracks are positive; the later positive source
values allow both tracks to occur. The checker gives an explicit
alternating split. However, the first row of A0 has unit trit two,
so A0 itself is not a Boolean word. The input slack R-2x is positive.

Now put

    D=q+H, t=k(q+H), Z=-q.

Then 6t=(R-3)D and formal Z+D=H hold exactly. All retained supplied
counter coordinates are positive. In particular the failure is not
caused by admitting a negative supplied D or t.

## Exact signed normalization

The first eight conceptual base-q coefficients are

    Kplus,Kminus,-q,q+H,t-A0,A0,t-A1,A1.

Their normalized coefficients are exactly

    Kplus,Kminus,0,H-1,
    kH-A0+1,A0+k,kH-A1,A1+k.                              (1)

The successive outgoing signed carries are

    0,0,-1,1,k,0,k,0.

Consequently there is no outgoing carry into the program fields.
This is an exact polynomial identity, independently checked symbolically
in the companion script.

Every coefficient in (1) is Boolean and lies below q. For the two low
guard chunks, k is the Boolean word of m-1 ones. Away from the initial
row, subtraction from k is therefore digitwise complementation without
borrow. The initial row of kH-A0+1 is zero, and that of kH-A1 is k.
For the two high chunks, the initial rows are respectively

    (k+1)+k=2k+1=R/3,    0+k=k,

both Boolean and below R. All later rows retain their original Boolean
track values. The words H-1, Kplus and Kminus are Boolean as well.
The first Kplus trit is one, as in the original unit-mask interface.

Thus the lower masks conceal both a nozero word exceeding q and a
non-Boolean track while the numerical counter time equation remains
exact. Any successful elimination of positive Z must use additional
program constraints or a different packing argument; the former
pretyping bound D<H cannot simply be reused.

## Reproducible finite evidence and boundary

`../verification/explore_unbounded_nozero_grid_fields.py` checks the
general signed polynomial identity and materializes the complete lower
counter words for m=4,6,8. These have respective inputs 7,61,547 and
heights 48,372,3288. Each case checks nine displayed lower residuals,
all eight normalized Boolean chunks, positive retained coordinates,
the malformed initial track, and the full outgoing carry sequence.

These modest radices are not claimed to exceed a particular compiled
ROM's fixed constants. The general argument permits arbitrarily large
even m, including any fixed grid-alignment requirement, but the routing
equation is deliberately absent throughout. The receipt preserves this
boundary instead of calling the family a full counterexample to102.
