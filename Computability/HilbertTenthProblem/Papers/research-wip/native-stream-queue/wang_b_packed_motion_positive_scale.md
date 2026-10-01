# Positive native scale: Wang motion188/241

Applying the [positive native-scale helper](native_binary_positive_scale.md)
to [packed Wang motion](wang_b_packed_motion.md) gives an
**188=81M+107A** certificate with **18 comparisons and34 positive
auxiliaries**. Its SOS polynomial costs **241=99M+142A**, with total
degree **at most316**. The four positive endpoint parameters remain
unchanged. The old244-operation polynomial has one more comparison and
one more auxiliary; both packets have the same188 paid certificate gates.

The [source](wang_b_packed_motion_positive_scale.py) and
[receipt](wang_b_packed_motion_positive_scale.json) preserve every outer
packing, read/mark relation and nearest-neighbor head transition. No
finite instruction controller or ordinary-TM input map is supplied.
The endpoint relation remains decidable as described below; these are
complete history-component counts, not a universal-polynomial claim.

## 1. Exact coordinate transformation

Let q be `native__q`, r the supplied positive `native__r`, and X the
native register `native__wn2`. The old positive coordinates w,beta enter
only

    X=w*q, bound=r+beta, comparison bound=X.

The successor keeps positive b in the old `native__bound_beta` slot,
removes `native__w`, and computes

    bound=r+b, X=bound*q.

The same two gates are used and the comparison is deleted. The generic
helper audits all unchanged raw-core rows and comparisons, unique
consumers, external exports, transitive coordinate independence and the
new acyclic ordering. The motion wrapper additionally checks that all
outer source rows, the three outer comparisons and all interfaces are
identical to the parent.

On arbitrary positive supplied coordinates, the parent's action-hat
decomposition gives J>=0, D>=5, B=8D>0 and P=(B-1)J+1>=1. Thus its
prescribed native scale S=B*P^12 is positive, and q=16S>=16, before any
comparison or native typing. All three unpadded joined words are
nonnegative before typing. These facts meet the helper's explicit domain
contract; positivity is not inferred merely from a symbolic register.

The positive forward map fixes every outer and other native coordinate
and restores

    w_old=r+b,
    beta_old=q*(r+b)-r=(q-1)r+q*b>0.                  (1)

At every positive parent zero, the complete native theorem gives
X=2^(2r+1), q=2^popcount(r). Hence w_old>=2^(r+1)>r and
b=w_old-r>0. This is the inverse to(1). Consequently the full positive
zero sets are in bijection, not merely their endpoint projections.
Every accepted physical history retains a strictly positive native
extension through the parent's complete converse and this inverse.

Under(1), every retained comparison residual agrees on all signed
integer assignments and the deleted residual is zero. Therefore the
complete new SOS polynomial equals the old SOS evaluated at(1), without
using any source equation. There is no claim of equality on unchanged
supplied coordinates with two different meanings for beta.

## 2. Preserved chronological semantics and scope

All semantic details are the parent's proved ones: arbitrary positive
duration, dyadic cell geometry, nonzero one-hot head in every row,
chronological reads and marks, and four exclusive row choices:
mark/stay, read/stay, left without marking, or right without marking.
The initial and final tape hats and head values are still explicit
parameters. The head transport still rejects a left move from head1.
The global height/slack inequalities and every canonical lane remain.
No instruction-state sequence, read-dependent branching program or
unpaid Boolean selector assumption is added or removed.

In particular, after existentially choosing all intermediate rows, the
endpoint relation is still exactly

    T_initial AND T_final=T_initial,
    H_initial and H_final are positive powers of two.

Any missing marked cells can be visited and marked before moving to the
specified final head; a stay makes a zero-change path nonempty. This
endpoint projection is decidable and does not establish a universal
recognizer. A finite translated physical tape prefix still requires its
initial/input encoding and any instruction-control interface to be paid
separately.

## 3. Literal ledger and replay

The188 certificate operations remain81M+107A. Removing one comparison
changes19 residual squares to18; their sum costs18M+35A, giving
241=99M+142A. The positive auxiliary count falls35 to34. No proof-only
exponentiation, division or coordinate conversion is an emitted gate.

Because r and b are still supplied degree1 coordinates, their sum has
formal degree1, as did w. The complete literal degree propagation gives
at most316, including all four endpoint parameters and every witness.
No zero equation is used to reduce degree, and no exact-degree or
optimality claim is made.

The source checks384 full old/new residual and SOS identities under(1),
192 signed, plus384 coordinate round trips and192 positive forward lifts.
It freshly packs192 physical outer histories through duration12 and
checks all three outer equations, exact joined AND, native scale bounds
and positive coordinate lifts. Their total steps and left moves are
recorded in the receipt. The inherited invalid-shape checks retain
left-at1, forged jump, simultaneous mark/move and free-mask carry cases.
The wrapper's unchanged outer source/ports make their interpretation
unchanged. These finite outer fixtures use native placeholders, not
full numerical Pell zeros; complete extension comes from the proof.

```sh
python3 wang_b_packed_motion_positive_scale.py
```

Author writer and fresh default replay pass. Root independently completed
full proof/source/fresh-default review with no findings. A separate
literal executor checked128 complete output/common-register identities,
64 signed, using the manual forward map; all64 positive cases lifted
positively. The unchanged outer-source and interface audit preserves
all parent motion proofs and their stated scope.

Gibbs additionally completed full proof/source/fresh-default review with
no findings. The motion context was included in the256 independently
executed whole-source/output identities across four helper contexts,
128 signed overall, with manually computed positive lifts and round
trips. These counts describe the shared four-context audit, not256
additional motion-only cases. All four local links resolve.
