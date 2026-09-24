# Shared transport for the two-coordinate universal queue

This is a conditional arithmetic skeleton for
`EXPLORATION_FINITE_STATE_RAW_QUEUE.md`. The two coordinate transports and
the length transport cost fourteen operations directly. Paying one common
radix factor R=3B allows all three equations to be divided by three and
reduces that cost to **twelve operations, 4M+8A**. The reduction is exact
on the stated source equations. It does not yet realize the rule-selection
products, field bounds, Boolean masks or finite controller.

## 1. One common finite queue history

Let a queue run have t>=1 steps and end with the empty queue. Its initial
coordinates are x,L0 and its initial length marker is Winit=3L0. For each
source step j let n0_j,n1_j be its two coordinate values, w_j its length
marker, d0_j,d1_j the removed symbol coordinates, and u0_j,u1_j the values
of the appended word. Let a_j be the number of appended symbols, 0<=a_j<=3.
All of these quantities have their exact meanings in this section.

Use a common time radix R and q=R^t. Form the packed words

    X=sum n0_j R^j,  Y=sum n1_j R^j,  Z=sum w_j R^j,
    D=sum d0_j R^j,  E=sum d1_j R^j,
    U=sum u0_j*w_j R^j, V=sum u1_j*w_j R^j,
    T=sum 3^a_j*w_j R^j.

The final coordinates are zero and the final length marker is one.
Multiplying the scalar recurrences by R^(j+1) and summing gives

    R(X-D+U)=3(X-x),
    R(Y-E+V)=3(Y-L0),
    R*T=3(Z-Winit+q).                                   (1)

These equations telescope through the same packed X,Y,Z. The two content
equations each cost five operations, and the length equation costs four,
for **14=6M+8A**. Winit is already computed by the raw input interface;
its computation is not part of this transport subtotal.

## 2. A common paid factor saves two multiplications

Supply positive B and add the paid equality R=3B. Replace (1) by

    B(X-D+U)=X-x,
    B(Y-E+V)=Y-L0,
    B*T=Z-Winit+q.                                     (2)

The radix equality costs one multiplication. Each coordinate equation
now costs one multiplication and three additions/subtractions, and the
length equation costs one multiplication and two additions/subtractions.
Thus the complete subtotal is **12=4M+8A**.

This is an exact source transformation. If F0,F1,FL are the three residuals
of (1), and G0,G1,GL those of (2), then

    F0-3G0=(R-3B)(X-D+U),
    F1-3G1=(R-3B)(Y-E+V),
    FL-3GL=(R-3B)T.

On R=3B either system implies the other over the integers. For a genuine
power-three time radix R>=3, B=R/3 is a unique positive witness. No other
witness changes. Signed intermediate differences are allowed. If B is
already supplied with its meaning established, the incremental transport
cost is eleven; the stated twelve-operation count pays its relation.

If row geometry already uses R=C*A with fixed C divisible by three,
computing B=(C/3)A is still one additional multiplication. Merely deriving
divisibility after a power-decoding proof does not make that arithmetic
free. Conversely, using B as the primitive radix variable and computing
R=3B pays exactly the same one multiplication counted here.

## 3. Where the remaining multiplication problem occurs

U,V,T are *weighted sums*, not arbitrary fresh witnesses and not products
of the corresponding packed histories. For example, for two rows with
append-coordinate values (1,0) and length markers (3,9), the required
weighted word is 3. The product of their two packed words is instead
3+9R. There is no carry issue to cure: the wrong cross-time term is already
visible with arbitrarily large R.

The seven-symbol queue's rule families suggest useful specializations:

* Loading a raw trit appends its fixed two-bit code; the first step also
  marks its first bit. The final loading delimiter appends blank and #.
  All these output lengths are two.
* An ordinary scan step appends the held predecessor, or appends nothing
  at the beginning of the scan. A left-boundary extension emits one fixed
  marked blank. The held symbol is part of finite control.
* A normal scan delimiter appends two symbols; a right-boundary delimiter
  appends three. Accepting drain steps append nothing.

For an interval known to append one symbol on every step, the length is
constant. Its length word would be Wstart*H, costing one product once its
own row-head repunit H is available. This is a conditional phase fact,
not a free replacement in (2): a complete computation has unboundedly
many scans, exceptional delimiter steps and a final drain. Separating
them needs a common ordering and verified phase transitions.

For a general packed run, one can introduce selected length words for
append lengths zero, one, two and three, but proving that they select
exactly the controller's rows is an additional mask or projection problem.
Likewise, the two append-coordinate sums must reflect the same held symbol
and the same length word. The twelve-operation transport does not enforce
any of these facts by itself. A complete cost is therefore still open.

## 4. Evidence

`../verification/explore_raw_queue_transport.py` expands both schedules
against independent residuals and verifies the three displayed source
corrections. It then imports the actual finite queue compiler, collects
complete accepting runs, constructs all eight packed words from the same
dequeue sequence, and checks both schedules and positive radix witnesses.
The weighted-product counterexample is tested separately. The receipt
counts these as transport examples, not a new complete arithmetic verifier.

Author and independent root/affine_optimization complete proof/source audits
and fresh checker runs PASS with no findings (72 runs, 2,316 steps). The
three files are frozen for publication; this review status does not extend
the conditional transport scope.
