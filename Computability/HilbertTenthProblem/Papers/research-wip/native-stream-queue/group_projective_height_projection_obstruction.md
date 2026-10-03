# Directly supplying the height admits false ordinary inputs

Deleting the input-dependent height constructor is unsound in the current
projective matrix architecture. A concrete fixed one-macro table has an empty
accepted language on positive ordinary inputs, but the proposed direct-height
source admits input **511**, and infinitely many further positive inputs.
The full positive native extension is proved below; the finite fixtures check
the actual outer source and prescribed AND, without materializing the huge
Pell witnesses.

The [helper](group_projective_height_projection_obstruction.py) and
[receipt](group_projective_height_projection_obstruction.json) save an explicit
complete 464-operation parent and its rejected 463-operation child. The child
deletes exactly one addition. These deliberately simple schedules are not
arithmetic optima. This is a counterexample to the proposed general rewrite,
not to the valid parent, the established universal bounds, or a particular
243-operation specialization of the separate ten-letter example.

## 1. The precise complete candidate

Keep the ordinary input and boundary convention of the
[shifted projective compiler](group_projective_shifted_boundary.md):

    u = 24*x+13, D = u+height_slack, C0 = D−1, B = 16D.

The signed initial vector is `(1,u,1,u)` and the target is `(0,1,0,1)`.
All supplied inputs and witnesses are positive integers. The proposed child
replaces supplied `height_slack` by supplied `D` and deletes only the paid
definition `D=u+height_slack`. Every other gate and all six comparisons remain.

As a map on unrestricted integer coordinates this is exact: substitute
`height_slack=D−u` in the old source. The helper verifies the old slack has
only this one consumer and that deleting this single row gives the literal
whole child. Induction through the remaining rows proves the full polynomial
identity, not just agreement on tested values. The issue is precisely the
positivity of the restored slack.

Both saved sources use a single private 32-edge hub cycle, injectively packed
in m=32 lanes, with no idle selector. The ordinary compiler constants remain
alpha=24 and beta=12, so the established margin `alpha+beta+1=37>=32` holds.
The parent therefore retains its existing positive-input soundness theorem.
Both sources include the actual product scale `q=32B*P^72`, the smaller tail
quotient, all seven unit factors, and the complete finalizer

    F = eight_units * (1 + sum of the five outer residual squares) − 1.

The source reconstruction reads the pinned complete m=8 label-aligned
template. It replaces the graph-dependent checksum, general chronological
flow, physical selectors and controller packing, extends the paid powers and
repunit to m=32, and updates the joined scale and range scale. All native and
history gates outside these interfaces remain literal. The product-scale and
tail-quotient rewires are the already proved ones. No historical Python helper
is imported or executed, and no stale template ledger is reported as current.

The complete parent costs **464=192M+272A** and its child **463=192M+271A**.
Their comparison prefixes cost447/446; the common six-comparison finalizer
costs17=6M+11A. Both use58 positive witnesses and one ordinary input. All paid
gates and supplied coordinates are live. Propagated degree upper bounds are
5055 for both; this note makes no exact-degree or optimality assertion.

## 2. A fixed macro with no positive accepted input

Use the following physical word, with the original eight signed shear labels:

    W = (3,2,3, 1 repeated13 times,
         7,6,7, 5 repeated13 times).

It has32 letters and begins with a lower shear in the first block, whose
source is the even coordinate. In either 2-by-2 block, the first three letters
give `S=[[0,−1],[1,0]]`, followed by thirteen positive upper shears. Thus the
macro matrix is `diag(M,M)`, where

    M = [[13,−1],[1,0]].

The chronological convention multiplies each next shear on the left. It gives
`M*(1,13)^T=(0,1)^T`. This reference input has x=0 and is outside the declared
ordinary input domain; it is used only to construct finite outer data.

To prove the entire positive-input language is empty, put

    f0=0, f1=1, f(n+1)=13*f(n)−f(n−1).

Matrix multiplication shows `M^(−n)*e2=(f_n,f_(n+1))` for all n>=0. For n>=1
the sequence is positive and strictly increasing after f1, so f_n=1 only at
n=1. Therefore a word W^n can send `(1,u)` to e2 only when n=1 and u=13.
The empty word cannot do so. Since `u=24x+13>13` for every positive x, there
are no accepted positive inputs for this fixed macro table.

## 3. A carry that the retained outer equations do not detect

Let D be any power of two with D>=32; set B=16D, duration t=32,
P=B^32 and J=(P−1)/(B−1). Follow the genuine finite trajectory of W from
`(1,13,1,13)` to `(0,1,0,1)`. With origin C0=D−1, all reference shifted
coordinates are strictly between0 and2D. Their signed values lie between
−13 and14. Let H_i be the packed pre-step histories, E_e the one-hot edge
words, and Z_i the selected source words.

Construct the candidate data by

    H'_1=H_1−24, H'_3=H_3−24,
    H'_0=H_0, H'_2=H_2,
    u'=13+24(B−1), x'=B−1.

Keep every edge word and selected source word unchanged. Subtracting24 only
changes the time-zero digit of each odd history: `D+12` becomes `D−12>0`.
Every later digit stays unchanged. At time zero the first physical letter is
a lower shear and reads the even history, so neither changed odd digit is
selected. At every other time there is no changed digit. Hence all selected
source products remain exact, despite the changed histories.

The actual odd history comparison has the form

    B*(H_i+delta_i) = H_i+C0*P−D+(P+1)−u.

Its delta depends on the unchanged selected source words, selectors and C0.
Changing H_i by−24 reduces the left side by24B. The right side changes by
`−24−24(B−1)=−24B`. Both odd comparisons therefore remain exact. The two
even comparisons and chronological controller flow are unchanged.

The native scalar joint unit is

    sum H_i + sum Zhat_j + global_slack − P.

Raise the reference positive global slack by48. Then this unit remains
exactly1. The reference slack is positive for every such D: at each cell,
the history and selected-source digit sum is bounded by `5*(2D−1)`, giving

    global_slack >= (6D+4)*J−6 > 0.

All supplied outer coordinates of the candidate are strictly positive.
The restored old height slack is

    D−u' = D−13−24(16D−1) = 11−383D < 0.

Thus the exact signed coordinate identity cannot supply an old positive
witness tuple.

## 4. The complete native extension exists

This is more than a formal transport alias. The modified history digits
remain in `(0,2D)`, all Boolean edge words and their checksum are genuine,
and every selected source word remains the corresponding exact product.
Their scalar range and output bounds are preserved; the modified joint slack
restores the original bound exactly.

At the actual paid scales, all lower history, selector, controller and range
regions therefore satisfy their prescribed AND relations. The radix B and P
are dyadic. The product-scale top region uses B AND2=0. Consequently the full
literal words satisfy

    H AND M = Z, 0<=H,M,Z<Q, Q=2B*P^72, q=16Q.

The [product-scale proof](group_projective_product_radix_scale.md) and
[tail-quotient proof](group_projective_tail_quotient_shift.md) supply the
positive native converse for these prescribed words. This component converse
requires the positive word fields and AND relation, not the ordinary input
being a genuine matrix query. It supplies strictly positive native roots,
ratio slacks and auxiliary coordinates making all six native unit factors1.
The gap/root, computed-field and tail-quotient coordinate maps remain
positive by their component proofs. In particular the tail embedding from
the larger quotient adds the positive difference between the full packed
quotient and its tail.

The joint scalar factor is already1 and all five outer residuals vanish, so
the complete child output is zero. This argument invokes neither a positive
parent zero at x=0 nor a full compiler theorem at the false x'. It applies
only the native component converse to the verified prescribed words.

For D=32, this gives a full existential positive child zero at x'=511 even
though the actual accepted positive-input language is empty. Letting D range
over powers of two gives infinitely many false ordinary inputs. Any repair
must restore an input range obligation or supply a different proof excluding
this carry; the single defining addition cannot simply be dropped.

## 5. Executable evidence and limits

The helper authenticates eleven source/proof dependencies. It records the
two full sources and recounts every paid operation, finalizer and live port.
Twelve integer/rational evaluations supplement the literal signed-coordinate
identity, including four rational cases.

Three exact outer fixtures at D=32,64,128 check all five actual outer
comparisons, the joint unit, the real paid checksum and packing registers,
and the complete prescribed AND at its actual native scale. They produce
false inputs511,1023,2047. Large word hashes and bit lengths are saved instead
of huge decimal expansions. The native coordinates in these executable
fixtures are explicitly placeholders, and the helper confirms that the
resulting full numerical output is nonzero. The claimed full positive zeros
come from the native extension proof above, not from those placeholders.

Run from any working directory with standard-library Python:

```sh
python3 group_projective_height_projection_obstruction.py \
  --root /path/to/native-stream-queue \
  --expect group_projective_height_projection_obstruction.json
```

This is a bounded source-pinned research artifact. It claims no maintained
general compiler API and no lower bound for other ways of handling input
height. All valid frozen predecessors remain unchanged.
