# A positive scale coordinate gives prescribed AND64/108

The complete prescribed AND from [masked selection63](native_binary_masked_selection63.md)
admits a **64=33M+31A** certificate with **15 comparisons and21 positive
auxiliaries**. Its ordinary sum-of-squares polynomial costs
**108=48M+60A**, with total degree **at most28**. The old certificate has
the same64 arithmetic gates but16 comparisons and22 auxiliaries, giving
111 SOS operations. Every fixed-numeral multiplication remains charged.

The [source](native_binary_positive_scale.py) and
[receipt](native_binary_positive_scale.json) supply a guarded prefixed
rewrite. The change is a bijection between full positive zero sets after
the explicit coordinate transformation below. It does not merely retain
canonical witnesses or the existential projection. This is a local
complete AND component; no new universal bound is claimed.

## 1. Source and complete domain

The four positive relation parameters remain P,Hhat,Mhat,Zhat. The exact
projection remains

    P=2^ell, ell>=0,
    0<=Hhat-1,Mhat-1<P,
    Zhat-1=(Hhat-1) AND (Mhat-1).                       (1)

The prescribed source computes q=16P, so q>=16 before any comparison.
Its positive auxiliaries include r,w,beta, with literal beta name
`bound_beta`. The old source has

    X=w*q, bound=r+beta, comparison bound=X.            (2)

The supplied r remains a positive auxiliary and retains its comparison
to the packed truth index. Replace(2) by

    bound=r+b, X=bound*q,                              (3)

where b is positive and keeps the literal spelling `bound_beta`. Omit
w and the comparison in(2). The two arithmetic gates are reused. A stable
topological sort puts the bound gate before the multiplication defining X.

All remaining native equations, both input ports, the checksum, oddness,
strong auxiliary equation and ratio slacks remain in place. In particular
this is not the unresolved removal of a native bound: equation(3) enforces
X>r on the complete positive supplied domain.

## 2. Full positive-zero bijection

For any new positive supplied tuple, define the old coordinates by

    w_old=r+b,
    beta_old=q*(r+b)-r=(q-1)r+q*b.                      (4)

Since r,b>0 and q>=16, both are positive. The old X equals the new X,
and the old bound equals X. Every old comparison is therefore restored,
with all other coordinates fixed. Only the meaning and value of the
bound register itself change; it has no other consumers or external port.

At every positive zero of the old source, the complete
[binary-selector theorem](native_controller_binary_selector56.md)
gives

    X=2^(2r+1), q=2^popcount(r).                       (5)

These are conclusions for every old zero, not solely for a specially
chosen extension. Since popcount(r)<=r for positive integer r,

    w_old=X/q=2^(2r+1-popcount(r))
         >=2^(r+1)>r.                                (6)

Consequently b=w_old-r is strictly positive. It restores(3), leaves every
other register and comparison unchanged, and is inverse to(4): the old
bound comparison gives beta_old=q*w_old-r. Thus the complete positive
zero sets are in bijection. The positive converse for every tuple in(1)
is inherited from the full native theorem, including P=1 and zero
unpadded words.

The same algebraic substitution is an exact identity on arbitrary signed
integer assignments, without any zero assumption:

    SOS_new(values)=SOS_old(Phi(values)).              (7)

Here Phi is(4). The deleted residual is identically zero under Phi, and
every retained residual agrees individually. The inverse coordinate
formula is integral everywhere but is asserted positive only at old
positive zeros. No division or exponentiation in this proof is an
uncounted runtime gate.

## 3. Reusable helper and guarded scope

`rewrite(old,prefix='')` accepts a packet with `source`, `comparisons`,
`parameters` and `auxiliaries`. It returns updated cost/domain metadata
and records the parent, prefix, removed comparison and six named scale
registers. `build()` supplies the standalone prescribed-AND packet;
`lift_to_parent` and `project_from_parent` implement(4) and its inverse.

The rewrite checks every unchanged raw-kernel row and required native
comparison against the frozen prescribed source. It requires r,w,beta
as supplied auxiliary coordinates. It checks that w is consumed only by
X, beta only by bound, and bound by no source gate and exactly its one
comparison. None is exposed through a declared `public_registers` port.
It checks transitive independence of q and r from both changed
coordinates, all gate definitions and the final acyclic schedule.

For a prefixed host, the first seven input-padding rows may already have
been substituted by its paid outer source, as in the Wang and toggle
components. The helper preserves these rows. Its algebraic identity and
consumer guards are unconditional, but applying the positive theorem
requires the host's established pretyping q>=1 domain and its complete
inherited native semantics. The helper does not infer arbitrary computed
input-port positivity from register names. The intended hosts already
prove q>=16 and the nonnegativity of their unpadded words on every positive
supplied assignment. Supplied positive r makes their forward map immediate.
The old native theorem gives(5) at their zeros, so the same inverse applies.

## 4. Costs, degree and evidence

The certificate retains64 gates, with33 multiplications and31 additions
or subtractions. Fifteen residual squares and their sum add15M+29A,
giving108=48M+60A. There are21 positive auxiliaries and four unchanged
positive relation parameters. The raw supplied r has degree1, as does b;
replacing w by r+b does not raise the formal degree of X. Literal degree
propagation through every gate gives SOS degree at most28, with no use
of zero equations. No exact-degree or optimality claim is needed.

The receipt records512 complete residual/output identities,256 signed,
512 coordinate round trips and256 positive forward lifts. It separately
checks512 exact scalar instances of(5)–(6), and rejects guarded source
mutations involving private consumers, missing comparisons, altered
native rows and coordinate dependencies. Scalar inverse checks are not
full positive Pell witnesses; the inherited complete theorem proves the
arbitrary positive extension. No parent source or receipt is modified.

```sh
python3 native_binary_positive_scale.py
```

Author writer and fresh default replay pass. Root independently completed
full proof/source/fresh-default review with no findings, and a separate
literal executor checked128 complete output/common-register identities,
64 signed, using a manually derived forward coordinate map; all64
positive cases lifted positively. The review includes the explicit
host-embedding contract for the prefixed helper.

Gibbs also completed full proof/source/fresh-default review without
findings. An independent literal executor and manual coordinate lift
checked256 whole-source/output identities across standalone, renamed
standalone, toggle and motion contexts:128 signed and128 positive lifts,
with manual round trips. Those checks do not call the implementation's
lift or audit functions. All four local links resolve; the source,
receipt and proof note are frozen after review.
