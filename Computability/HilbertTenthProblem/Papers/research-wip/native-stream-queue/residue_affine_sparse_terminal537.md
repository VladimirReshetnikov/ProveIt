# Deriving the terminal digit bound gives sparse universality in537 operations

> The [coded-control successor](residue_affine_sparse_control_codes.md)
> gives505 operations with the same67 witnesses, seven comparisons and
> degree bound5091. Paid selector sharing changes only the state codes;
> after typing, its supplied positive zeros agree with this537 construction.

The [literal source](residue_affine_sparse_terminal537.py) improves the
[538-operation sparse compiler](residue_affine_sparse_scale538.md) to
**537=193M+344A**, with **67 positive witnesses**, **seven comparisons**
and degree **at most5091**. Its certificate has517 operations. The
[receipt](residue_affine_sparse_terminal537.json) contains the complete
polynomial schedule and deterministic exact checks.

Remove the final payload F from the height expression. Once the native
AND has typed the local rows, exact payload transport already forces
F below the radix. Thus paying for F in the height is unnecessary.
The fixed U21, valid program recipe E=3^e and ordinary positive input x
retain their full universal representation. This improves the independent
prime-payload route, above the separate established75/87 bounds.

The forward map from positive parent zeros preserves positivity. Its
integer affine inverse can have a nonpositive height slack. Accordingly,
the theorem concerns the represented input relation; it does not assert
a positive-zero bijection on all supplied coordinates.

## 1. Literal rewrite and exact integer identity

Replace only the height definition

    h_old=E+x+F+eta_old

by

    h=E+x+eta,       eta>0.                              (1)

The radix B=C_B*h, positive computed scale
P=V+YI_hat+YD_hat+beta, repunit unit N_P=P−(B−1)J,
range mask (h−1)J and every other row remain as in538. In particular,
both exact transport comparisons and the paid loader count remain.
All fixed multiplications retain their literal costs.

The source checks the complete canonical538 packet, its private height
chain and its exports. It deletes the private E+x+F addition and makes
the final height row add eta directly to E+x. No old rewrite helper is
reapplied to the altered graph. Metadata records its parent; the actual
emitted source, comparisons and degree audit remain authoritative.

For arbitrary integer assignments the affine maps

    eta=eta_old+F,       eta_old=eta−F                    (2)

make every surviving source register identical. The comparisons, native
unit factors, product finalizer and same-cost SOS finalizer therefore
agree exactly under (2). The forward map is positive on every positive
assignment. The inverse need not be positive, including at typed outer
histories. We prove soundness directly below rather than treating (2)
as a positive witness restoration.

## 2. Power and sign recovery before any terminal bound

Now h>=3 unconditionally, E,x<h, and F is only a positive witness.
The inherited dyadic constant satisfies

    C_B>=max(4,edge_count+1,state_count+2,3*pmax+1).

Since pmax>=2, C_B>=8 and B>=24 before equations. In particular

    B−1>2(pmax−2),       B−1>2(h−1).                     (3)

These are precisely the height-dependent strict estimates used in
[538 Sections2–3](residue_affine_sparse_scale538.md).
For completeness, at a product zero every ordinary residual vanishes
and each unit is ±1. The computed P is at least3; the weak repunit
P=(B−1)J+e, e=±1, forces J>=1. The nonnegative definition of V
and the positive action hats give

    J<=U<=V<P, W<P, each Z_p<P, YI<P, YD<P.

The exact remainder comparison and (3) give R,S<P, while the range
mask is also below P. Each class mask is at most P+1. Therefore the
packed words satisfy

    0<=H,Z<P^L,       0<=M<2P^L<Q=B*P^a,

where a is the least power of two at least L. This bound allows carries
inside M; no selector or radix typing has yet been assumed. All padded
native ports are legitimate positive ports.

The unchanged local native proof in538 recovers its exponent with the
individual units and both ratio slacks, before assuming the native product
sign or its complete AND theorem. In the coupled form it reconstructs
the fixed-minus kernel at r'=r+epsilon−1>=4367, proves
X=2^(2r'+1), and hence makes q0=16Q, B and P dyadic. In the uncoupled
form the literal index comparisons give the same argument at r'=r.
None of these steps uses F<h or the transport comparison.

For B=2^v, P=2^s the negative repunit sign would imply
2^s=-1 modulo2^v−1. Reducing s modulo v contradicts
0<2^t+1<2^v−1 for 0<=t<v and v>=3. Thus N_P=1,
P=B^T and J=1+B+...+B^(T−1), T>=1. The old native unit product
is now1, so its full theorem gives H AND M=Z. This restores all the
local typing assumptions, without invoking a positive old height slack.

Also h=B/C_B is an integer power of two; at these zeros h>=3 improves
to h>=4. Consequently the parent's later typed estimates with h>=4
remain available. This observation is not used to justify the earlier
pretyping bounds (3).

## 3. Typed rows, terminal bound and complete chronology

Use the local typing proof in
[the factored compiler Sections2–3](residue_affine_sparse_factored.md).
All joined coefficients now fit below P, so the native AND separates
into its prescribed lanes. Edge selectors are bitwise subsets of J;
their sum J and edge_count<B give exactly one selected edge per row.
The range lanes put each w,rho,sigma in [0,h−1]. Thus U has digits
w+1<=h, the prime lanes select them, and V has digits
(p−1)(w+1)<B. The action lanes then select the appropriate V digits.
The two sides of the remainder comparison are carry-free, with digits
at most2h−2 and pmax−2, respectively. Hence each row has the exact
remainder condition of its selected I,D,T or Z branch.

The computed current and following payloads C,N consequently have T
digits in [1,pmax*h], all below B. In particular

    0<C<P,       0<N<P,       0<E<B.                    (4)

This step uses only the selected local graphs, not chronological adjacency
or a terminal bound. Exact payload transport, still literally paid, says

    B*N+E=C+P*F.                                       (5)

Using (4), positivity of F and integer bounds gives

    0<P*F=B*N+E−C
          <=B(P−1)+(B−1)−C<BP.

Therefore **0<F<B**. Now both endpoints and every internal digit are
canonical base-B digits. Comparing digits in (5) gives initial payload E,
each following payload equal to the next current payload, and final
payload F. The unchanged control transport likewise gives initial loader
state0, every true target/source adjacency, and halt state m+1.

The loader is a nonempty contiguous prefix, with no return from the body.
Its last output is E*2^ell<B: it is itself a typed following digit, whether
or not a later row is used to express it as a current digit. Hence
1<=ell<B−1. The surviving input term in (1) gives1<=x<h<B−1.
The exact loader count reduced modulo B−1 now forces ell=x.
Thus the decoded run has precisely the requested ordinary input, and
all later rows follow the actual deterministic prime-payload program.

The current factory requires a nonempty body table; it does not emit an
initially halted body. The terminal-digit inequality itself also works
when a loader output is terminal, but no empty-table source support is
claimed. In particular this distinction has no effect on the fixed U21
universal slice.

Conversely, every positive538 zero maps by eta=eta_old+F to a positive
new zero with all surviving registers unchanged. The parent's complete
extension of every finite accepted U21 run therefore supplies completeness.
Soundness above and this positive map establish exactly the same represented
ordinary-input relation, for valid universal recipes and the other supported
positive program parameters.

## 4. Arithmetic and validation

| Form | Certificate | Comparisons | Witnesses | Polynomial | Degree bound |
|---|---:|---:|---:|---:|---:|
|Normalized norm units|514=184M+330A|9|67|540=193M+347A|5345|
|Coupled index units|517=186M+331A|7|67|537=193M+344A|5091|

Both finalizers lose exactly one addition. Height remains degree1, so
every surviving register's propagated degree and the complete product
and SOS degree dictionaries are unchanged. The coupled factor bounds
remain816,1900,442,65,1018,375,375,2; their sum4993 and maximum
ordinary residual bound49 give5091. The same-cost SOS bound is9986.
These remain upper bounds, not claims of exact polynomial degree.

The checker evaluates complete affine identities with a separate parent
interpreter, including signed assignments and explicitly nonpositive
inverse slacks. It checks both native forms, both finalizers, both packing
recipes, complete closure, unchanged degree dictionaries, malformed caller
rejection, weak-repunit bounds at the new minimum h=3, and exact terminal
transport at extreme digits. Actual outer runs choose h from E+x and
local quotient/remainder bounds alone. Many have F>=h; wrong ordinary
inputs still fail the paid count while preserving the other outer rows.
These finite fixtures do not materialize full native Pell witnesses.

```sh
python3 residue_affine_sparse_terminal537.py
```

The author writer and fresh replay pass. Twelve contexts cover six tables
and both native forms, including no exceptional prime class and a new
prime23. There are1152 complete affine output identities on576 assignments
(288 signed),197 nonpositive inverse slacks on positive assignments, and
576 positive forward maps. Another576 complete shared/unshared outputs
include144 signed assignments. Separate checks cover1680 weak-repunit
bounds,336 at h=3,560 exact terminal/chronology cases and six rejected
callers. Across22 tables,192 halted outer histories contain925 chronological
rows;127 have F>=h and155 have nonpositive inverse height slacks. There
are174 wrong-input count rejections. For example, one supported body
increment at prime5 has payloads1,2,10 with h=4, B=64 and old slack−8.

Native and Franklin independently reviewed the complete source, proof and
dependencies and passed fresh replays without findings. Both checked the
h>=3 pretyping estimates, power recovery before repunit sign and AND,
local payload bounds before chronology, and the scope of the affine map.
Native's separate executor checks512 complete register/factor/residual/output
identities, including256 signed checks and128 positive assignments with
nonpositive inverse gaps, across16 contexts. Its32 independently propagated
degree/opcode ledgers agree. It separately simulates and packs180 outer
histories with657 rows,123 with F>=h and137 with nonpositive parent gaps.
Franklin checks640 complete affine identities on320 assignments (160 signed),
40 independently expanded degree/opcode/closure ledgers and144 complete
shared/unshared output/interface identities on72 assignments (36 signed).
Its separate simulator and packer check36 halted histories with129 rows,
24 with F>h and31 with nonpositive inverse gaps. Both reviewers resolve
all five local links. These checks retain the stated outer-history scope.
