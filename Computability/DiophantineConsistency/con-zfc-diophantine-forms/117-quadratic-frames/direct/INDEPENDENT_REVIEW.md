# Independent review of the 63-predicate signed-radius construction

## Scope and conclusion

I independently reviewed the new arithmetic reduction against ProveIt commit
`84e16e43092614bae262ca59651cb9d77e31a255`. The reduction replaces one
shared-frame equality and deletes twelve of the former seventy-five sign
predicates. Its ordinary integer-zero-existence proof is valid with the
order of arguments described below. The source theorem is inherited from
the existing direct C222 construction; this review does not claim a new
proof-assistant theorem or an internal object-ZFC proof term.

The independent program `independent_source_check.py` imports no producer,
optimizer, prior checker, or proof compiler. Its normal and optimized runs
both pass. They authenticate seven complete source/certificate files, check
every changed and unchanged body row, check the sixty-three remaining
predicate rows, and bind all 109 nongate constraints in the private Pell
completion. All 1,029 original gate definitions, including the 474 private
gates, are checked as unique monic triangular definitions over the integers.
The separate projection checker is responsible for the complete projected
polynomial and inverse certificates.

The substantive new idea is using squares of initially signed power outputs
in the common bound. That gives the required absolute-value bound without
assuming their signs. The power certificates then recover their signs before
the quotient signs are inferred. This avoids the old dependency cycle.

## 1. Early premises are sufficient

The twelve removed raw scalar predicates are

```
575,584,592,600,609,618,627,636,104,6,106,825.
```

The first eight are range quotients. Coordinates 104, 6 and 106 are power
outputs. Coordinate 825 is the second factorial's shifted-index slack.
The first factorial lower bound `f=x87>=2`, the original remainder/slack
predicates, the positive common ordinate predicate, and the paired-index
product predicate remain.

The first recovered sign is the already known 75-parent consequence

```
x93 = f*x94 + (f-1)*x95 + f >= 2.
```

The new recovery of x104 uses an exact eleven-row source identity:

```
f*(x104+1) = f*x59 + x131 + 3.
```

The right side is strictly positive because x59,x131 are retained
nonnegative coordinates, and f>=2. Therefore x104+1>0; integrality yields
x104>=0. No power meaning or downstream sign is used here. The identity is
checked from the complete original rows 88,104,105,106,110,111,112,114,115,
116,117, with their explicit polynomial multipliers.

Filtering the existing prefix proof after these two recoveries gives
exactly 604 of the 643 nonnegative prefix coordinates. The unproved set has
39 entries: the earlier 32 range-quotient/output descendants, and

```
6,106,124,125,130,132,133.
```

Of the 43 distinct power arguments, precisely ten have unproved sign:

```
573,583,591,599,607,617,625,635,6,106.
```

These are precisely the coordinates squared in the new frame. Every
requested base and exponent is already natural, and all fifteen seed
indices are strictly positive by their actual constructor rows. The only
additional postponed special lower bound is the one on coordinate 130.
The independent checker verifies this entire dependency boundary.

## 2. Signed output recovery has the right sign hypotheses

The new bound has the exact identity

```
W = 2 + sum(other distinct arguments) + sum(ten selected outputs squared).
```

Consequently every actual base and exponent is less than W, and every
selected signed output m satisfies |m|<W. The unchanged initial modulus
row supplies A>=2. The bootstrap norm at base W+1 then supplies A>W^W.
This bootstrap uses the actual integer W and no intended power value.

For each of the eight range-output calls, the original retained ordinate
slack gives Y>=k>=1. The signed comparison-base theorem therefore gives
|X|=chi_k(A) and Y=psi_k(A). This positive-Y conclusion is essential.
With T=2An-n^2-1, the negative-X branch forces

```
T divides m*n^k+1.
```

Here n>=2. The dividend cannot vanish for any integer m; its absolute
value is strictly less than T by the new frame bound. Thus X is positive.
The positive branch forces T to divide m-n^k, again with absolute value
strictly below T, and hence m=n^k>0.

It would be invalid to allow Y to be signed in this argument: simultaneously
negating X and Y permits the false output -n^k. The eight retained positive-Y
slacks were checked individually and none is deleted.

Each range row has the form

```
m=(M*e)*q+r,  e=r+s+1,
```

where M=x129>=3 and r,s remain nonnegative. M is the canonical CRT modulus,
not the binomial radix b=x530. Hence 0<=r<e<=M*e. The now-positive m
excludes q<=-1. All eight missing quotient signs follow at the original
body tuple. No modular cancellation or coprimality assumption is used.

## 3. The two further signed outputs can be delayed

The first factorial argument only uses the K/shifted-K calls 1,5,6 and the
local ceiling/digit data. None of its hypotheses uses the signs of the
seven additional deferred prefix coordinates. Its large/small Pell-index
dichotomy, f>=2, and the literal digit equations restore both K slacks.
The first factorial fixed-point lemma then yields f=K!, which is even.

The paired t/k122 argument must change its supporting call for the t seed.
The former proof used call 0, whose output 6 no longer has an early sign.
The new proof uses call 2 instead:

```
(base,exponent,output,X,Y)=(103,4,104,670,671).
```

Its output 104 was recovered algebraically before the prefix proof, and
its base is at least 5. The other supporting call is call 9, with
(base,exponent,output)=(531,122,560). It is not call 7, which belongs to the
second factorial's shifted seed. All these literal identities are checked.

Evenness of f, the actual main norm, and call 2's congruence give x104 odd
without yet interpreting that power. Thus t and k122=t+x104+2 have opposite
parity. The even-index argument makes the corresponding ordinate slack
strictly positive, using call 2 or call 9 as appropriate. The retained
product predicate then makes the other slack nonnegative. Both seed pairs
can therefore be oriented using calls with already nonnegative outputs.

Once the t pair is oriented, signed-output uniqueness recovers the actual
values of call 0 and call 3, namely x6=(t+1)^t>0 and x106=f^t>0. The
remaining prefix products 124,125 are now nonnegative. The literal rows

```
x125 = M + x126*x130,  x126=M+x131+1>M>0
```

exclude x130<=-1, restoring its postponed sign and the final prefix wires.
All 643 prefix signs are then available. The checker binds every one of
these local source identities; the unbounded Pell reasoning is ordinary
mathematics, not inferred from numerical examples.

## 4. Deleting the shifted second-factorial slack is sound

After the t pair is exact, put f1=x107, d1=f1*t^2, C1=x111 and b=x530.
The exact t-index calls give

```
x113=(d1+1)^t,  x547=b^t.
```

The ceiling and remainder rows give

```
f1*C1=x113+x115,  C1=x114+x115+1>=1.
```

Thus f1>=1. The common V predicate already excludes a zero ordinate at the
shifted index k=t+d1. If its absolute ordinate is at least two, Pell growth
puts it above k, the signed index theorem applies, and the positive
supporting call 7 orients it. Its deleted slack is then positive.

The remaining case is absolute ordinate one. The same small-ordinate
argument used in the first factorial forces the exact small pair X=A,Y=1
and the output x546=b+1. The actual choose1 equations are

```
x546=b^t*(C1+b*x548)+x549,
b^t=x549+x550+1.
```

If t>=2, the right side is at least b^t>b+1, a contradiction. If t=1,
Euclidean division by b forces C1=1, whence the ceiling equation reads
f1=f1+1+x115, another contradiction. The boundary case t=1 is therefore
covered, rather than silently using a strict inequality valid only for
t>=2. This establishes the missing coordinate 825's sign.

## 5. A fresh Pell completion is necessary and sufficient

After all sign and power recovery, the new tuple still satisfies the new
frame equality, not the old linear one. Appending guard witnesses alone
would not produce an old source zero. The proof correctly uses a fresh
private completion while preserving the entire natural semantic prefix.

For any prescribed integer W dominating the finite true power data, choose

```
A=chi_W(W+1),  Z=psi_W(W+1)/W.
```

The latter is integral by the recurrence modulo W. Choose the main indexed
pairs at A. A finite unit period modulo four times the product of their
squared ordinates supplies U odd and V a positive multiple of that product.
Then gcd(U,4V)=1, so the Chinese remainder theorem supplies a large positive
comparison base B with B=A modulo U and B=1 modulo 4V. Its canonical indexed
pairs give the comparison and progression quotients. The ordinary oriented
power recurrence gives the remaining power quotients. Every defining gate
can be evaluated in order.

The finite audit proves that these target norms, congruences, products,
moduli and frame identity exhaust all 109 private nongate rows. Each
certificate isolates exactly one nongate with coefficient +1 or -1, with
only actual defining gates in its remainder. It also verifies the sole
derived t+1 pair. Thus no hidden private condition is left outside the
completion argument.

Both the old linear radius and the new quadratic radius dominate the same
finite nonnegative semantic data. Reconstructing the private frame in
either direction gives existence equivalence. This is not a pointwise
polynomial identity and not a bijection between the original Pell tuples.
It is exactly the kind of existence transformation needed for preserving
the consistency-calibrated zero problem.

## 6. Verification boundary

The supplied source checks pass in normal and optimized Python and reject
three representative changes: a missing output square in the frame,
a changed final guard, and removal of the strict-modulus premise. These
checks establish the finite literal interface. They do not prove the
unbounded Pell classification or the logical calibration by testing.

The proof combines the new ordinary arithmetic arguments above with the
repository's existing ordinary C222/refutation calibration. It makes no
assumption that ZFC is consistent and does not claim that an actual root
has been found. Global simplicity optimality is not asserted.
