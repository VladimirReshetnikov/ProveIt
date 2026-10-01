# A positive-scale coordinate lowers the toggle polynomial to155 operations

The complete [chronological toggle-tape component](langton_ant_packed_toggle_tape.md)
has a **155=65M+90A** polynomial successor with **27 positive witnesses**
and **17 comparisons**. The certificate still costs **105=48M+57A**.
Its total degree remains **at most124**. The two positive parameters
are the same initial and final tape words plus1.

The [source](langton_ant_packed_toggle_positive_scale.py) and
[receipt](langton_ant_packed_toggle_positive_scale.json) apply the new
[guarded native positive-scale rewrite](native_binary_positive_scale.md)
to the literal `native__` AND64 instance. No parent source or receipt
is changed. There is an explicit positive-zero coordinate bijection
with the158-operation parent, preserving every supplied outer history.

This remains a toggle component with independent head choices. Its
existential endpoint projection is all pairs of nonnegative tape words.
Planar ant turns/motion, the periodic-background input map and acceptance
are still absent. Neither this saving nor the component changes a
universal operation bound or the separate75/87 frontier.

## 1. The actual domain and two reused gates

The parent defines, on its strictly positive supplied domain,

    D=initial_tape_hat+final_tape_hat+height_slack>=3,
    B=4D, J>=1, P=(B-1)J+1,
    Scale=B*P^4, q=16Scale>=16.                     (1)

The native index r is an unchanged positive supplied coordinate. Before
any equation, q and r are independent of the native coordinates w and
bound_beta. The three packed native words are nonnegative, so their
folded ports16A+12,16M+10,16Z+8 remain legitimate positive native inputs.
This is the already proved complete parent AND embedding, not merely
a syntactic resemblance to its kernel.

In that core the two gates and comparison are

    X=q*w,
    bound=r+beta,
    bound=X.                                      (2)

The source's literal names are native__wn2, native__bs_X_bound,
native__w and native__bound_beta. The helper checks the complete raw
kernel rows and comparisons, the private w/beta/bound consumers, and
transitive independence of q,r. It permits the parent's already proved
folded input ports.

Omit w. Keep the old spelling bound_beta for a new positive coordinate b
and reuse the same two arithmetic gates as

    bound=r+b,
    X=q*bound.                                    (3)

Remove only the comparison in(2). A topological sort puts bound before
X. The repurposed bound register is private, so none of the outer
interfaces changes. The source charges every multiplication and addition
in(3); nothing is replaced by a free arithmetic definition.

## 2. Positive forward lift and exact signed polynomial identity

Given any new positive tuple, set

    w_old=r+b,
    beta_old=q*(r+b)-r=(q-1)r+q*b.                 (4)

Both old coordinates are positive by(1) and r,b>0. All other parameters
and witnesses remain unchanged. The old X is the new X, while the old
bound is exactly X, so the removed residual vanishes. Every other native
or outer source register agrees, except for the intentionally repurposed
bound register itself. Thus the complete old positive predicate follows
from every new zero.

The same substitution is a polynomial identity over arbitrary integer
coordinates. If Phi denotes(4), and F_old,F_new are the literal SOS
polynomials, then

    F_new(v)=F_old(Phi(v)).                         (5)

This identity does not need positivity, dyadic typing or any zero-set
assumption. Its positive interpretation does need the proved q,r domain.
The source checker tests the identity for the full emitted polynomials,
not only the changed native comparison.

## 3. The inverse is positive at every old zero

At every positive parent zero the complete raw native theorem gives

    X=2^(2r+1), q=2^popcount(r).                    (6)

These are inherited conclusions of the full AND kernel, with its true
positive port embedding, retained ratios and strong equation. The generic
helper cannot infer them for an arbitrary modified caller solely from
q>=1. Here all their premises are supplied by the unchanged parent.

Since r>=1 and popcount(r)<=r, equation(6) yields

    w_old=X/q=2^(2r+1-popcount(r))
         >=2^(r+1)>r.                              (7)

Therefore

    b=w_old-r>0                                    (8)

is a valid new supplied coordinate. Substituting(8) in(3) preserves X,
all norm factors and all remaining comparison residuals. The complete
new polynomial vanishes. Equations(4),(8) are inverses on the positive
zero sets: the old bound comparison fixes beta_old=q*w_old-r, and r,q
are unchanged.

This converse applies to every old positive zero, not only a canonical
choice of auxiliary Pell indices. Given a genuine finite toggle history,
first take the parent's full positive native extension and then apply(8).
All supplied outer histories, head positions and endpoint parameters are
preserved. In particular both setting and erasing a bit are retained,
including repeated heads and duration1.

## 4. Literal counts and unchanged degree bound

Both versions contain105 certificate gates, with48M+57A. The rewrite
omits one positive witness and one comparison. The old eighteen-residual
SOS used18 squares and35 residual/accumulation additions; the new
seventeen-residual SOS uses17 squares and33 additions. Consequently

| Version | Certificate | Comparisons | Witnesses | Polynomial | Degree bound |
|---|---:|---:|---:|---|---:|
| Parent |105=48M+57A|18|28|158=66M+92A|124|
| Positive scale |105=48M+57A|17|27|155=65M+90A|124|

In this unprojected native core r and b each have formal degree1.
Replacing w by r+b therefore leaves X's propagated degree unchanged.
All downstream degree bounds agree. In particular the native q has
bound9, X bound10, and the maximum retained residual bound is62.
The SOS bound is2*62=124. No equality holding only at zeros is used
in this degree calculation, and no exact-degree claim is made.

## 5. Verification and retained limitations

```sh
python3 langton_ant_packed_toggle_positive_scale.py
```

The receipt checks512 complete source/output identities under(4),256
signed; all512 coordinate round trips; and256 strictly positive forward
lifts. Every unchanged source register is compared, and all retained
residuals also agree with an independently assembled canonical AND64
invocation using the parent's actual scalar ports.

It also checks192 exact scalar instances of(6)--(8). These test the
inverse inequality and coordinate formulas; they are not asserted to
satisfy every native equation. There are288 genuine outer toggle histories
through duration12, including24 duration-one histories and rows which
erase previously set bits. The packed AND, every outer comparison and
all positive-coordinate conditions hold on these fixtures. Their native
auxiliaries are placeholders; the full positive extension follows from
the parent converse and Section3, rather than a numerical materialization
of enormous Pell witnesses.

The coordinate rewrite changes no tape, geometry or action constraint.
Thus the parent's endpoint obstruction remains exact: toggle the support
of a XOR b to reach any b from any a, using two flips when a=b. Turning
those free head choices into a planar ant path and imposing its fixed
periodic hardware, ordinary input and simulated acceptance require
additional paid work. The155 figure is a complete component polynomial,
not a complete universal recognizer.

Author writer and fresh default replay passed. Independent root and native
reviewers each completed full proof/source/fresh-default review with no
findings. Each also used its own literal executor and manual coordinate
lift for128 complete register/output identities,64 signed and64 positive,
using the actual outer scale q=16B*P^4. Source and receipt are unchanged
after these reviews.
