# Four evolving registers for the fixed matrix-word substrate

A word of arbitrary length in the fixed `SL2(Z) x SL2(Z)` subgroup
alphabet can be checked by following **four signed integer registers**,
two per block. Eight evolving matrix entries are unnecessary. The
special top-right entry `1` of the existing input curve makes this exact
without an extra bound comparing the input to the word length.

This packet proves the uniform mathematical reduction, gives its
**10=4M+6A** ordinary-input boundary circuit, and gives a conditional
**43=15M+28A** packed trace interface. The latter has four comparisons;
its digit typing, synchronized selection, regular controller and linked
power geometry remain unpaid. It is not a complete universal
Diophantine certificate or an improvement to the complete arithmetic
frontier.

## 1. A fixed elementary alphabet, with its controller retained

Let `Gamma` be any fixed finite symmetric subset of
`SL2(Z) x SL2(Z)`. The application is the one fixed subgroup alphabet
from the [group substrate](group_commutator_universal_substrate.md).
Use nine physical letters: identity, and the eight unit signed shears
that update exactly one of four coordinates by plus or minus its mate:

    v_0 <- v_0 +/- v_1,       v_1 <- v_1 +/- v_0,
    v_2 <- v_2 +/- v_3,       v_3 <- v_3 +/- v_2.          (1)

Each physical letter is a pair of determinant-one matrices. For a
physical word `s_0,...,s_(t-1)`, use action order

    P_0=I,       P_(j+1)=s_j P_j.                        (2)

Thus the final product is `s_(t-1)...s_0`. This orientation is part of
the convention; it does not assume that the matrices commute.

Every integer determinant-one `2 x 2` matrix is a finite product of
the four unit shears. Here is a self-contained effective proof. Left
multiplication performs signed row additions. If the first column is
`(a,c)` with `c != 0`, choose the Euclidean quotient of `a` by `c`,
subtract that multiple of row two, and rotate the rows by

    J=[[0,1],[-1,0]]=E_+(1) E_-(-1) E_+(1).

The new lower first-column entry has strictly smaller absolute value
than `c`. Eventually the first column is `(1,0)` or `(-1,0)`, since
`gcd(a,c)=1`. Multiplication by `J^2=-I` fixes the latter sign. The
remaining matrix is an upper shear. Remove it, reverse and invert the
recorded operations, and expand each fixed integer shear coefficient
into unit operations. This terminates and gives a literal physical word.
For a pair, factor its two blocks separately and concatenate; the two
block actions commute.

Choose such a fixed code word `code(gamma)` for every member of `Gamma`.
Keep the regular language

    R_Gamma = ( identity | code(gamma_1) | ... | code(gamma_m) )*.       (3)

It is recognized by a finite controller: start/end at one hub, with a
separate finite path spelling each code and an identity loop at the
hub. Multiple paths with the same labels are harmless. A physical word
in (3) evaluates to a product of members of `Gamma`, in reverse macro
order under (2); conversely every product in the subgroup has such a
word. Identity padding at the hub permits any larger physical length.
In particular `t>=2` costs no expressive power.

**The controller must be enforced.** Allowing arbitrary physical shear
words generally enlarges the subgroup to the whole ambient product.
The finite controller in (3) has been constructed mathematically, not
encoded arithmetically for free. Fixed code lengths may be large, but
are program-independent when `Gamma` is the fixed universal alphabet.

## 2. Native geometry identifies a whole matrix from one vector

For a product of `j>=1` physical letters, every entry of either block
has absolute value at most `2^(j-1)`. To prove this, follow a column.
Its initial `l1` norm is one, and a unit signed shear increases that
norm by at most a factor of two. Just before the last step its norm is
at most `2^(j-1)`. The updated entry is bounded by that previous norm;
each unchanged entry is too. Identity letters and operations in the
other block preserve the same bound.

Let

    t>=2,        q=2^t,        e_q=(q,1),
    L_r=[[1+r,1],[-r^2,1-r]].                            (4)

For any product block `P` of a length-`t` physical word,

    P e_q = L_r e_q       if and only if       P=L_r.     (5)

This holds for every integer `r`; the intended input has `r>0`.
For soundness, equality of the first components says

    q(P_11-1-r)+(P_12-1)=0.

But `|P_12-1| <= q/2+1 < q`, so divisibility by `q` forces
`P_12=1` and `P_11=1+r`. Put `a=1+r`. Determinant one now gives
`P_21=a P_22-1`. Thus the difference between the second row of `P`
and that of `L_r` is `(a delta,delta)` for an integer `delta`.
Equality of the second action components gives `delta(aq+1)=0`.
The integer `aq+1` is nonzero because `q>=4`; hence `delta=0`.
The converse is immediate.

Apply (5) separately to the two blocks. The paired matrix word equals
`diag(L_r,L_r)` exactly when the four-register machine (1), started at
`(q,1,q,1)`, ends at the two copies of `L_r e_q`. This proves an
arbitrary-length reduction; its number of evolving registers is
independent of `t` and of the fixed subgroup alphabet.

The dyadic relation is essential to this argument. If the product-height
bound is omitted, the nonidentity determinant-one matrix

    I + [[-q,q^2],[-1,q]]

fixes `(q,1)`. Right multiplying `L_r` by it gives a different matrix
with exactly the same tested vector. The checker records an explicit
example. Nor is (5) asserted for arbitrary targets: the fixed
upper-right entry `1` is what removes the input-height comparison.

## 3. Strictly positive state coordinates and the input boundary

Set `D=q^2`. At time `j>=1`, the preceding entry bound gives

    |v_i(j)| <= 2^(j-1)(q+1)
             <= q(q+1)/2 < q^2.                        (6)

The initial coordinates `q,1` satisfy the same strict final bound.
Therefore every shifted state

    X_i(j)=D+v_i(j)

is a strictly positive integer less than `2D`, including the terminal
state. Equation (1) becomes the affine update

    X_i' = X_i +/- (X_(i xor 1)-D),                    (7)

with the other three coordinates unchanged.

The [preferred ordinary-input loader](group_unipotent_input_loaders.md)
has `r=alpha*x+beta`, where `x>0` is the ordinary numerical input and
`alpha,beta` are fixed positive program numerals. In the universal
program family they are `12*2^(p+1)` and `12*2^p`. Each of these is
one fixed numeral; no varying-input exponentiation is being charged
as a numeral.

The exact shared initial and terminal values are computed as follows:

    input_product=alpha*x;  r=input_product+beta;
    D=q*q;
    c0=D+q;                d0=D+1;
    rq=r*q;                z=rq+1;
    U=c0+z;
    rz=r*z;                V=d0-rz.                    (8)

This is **10=4M+6A**, including the multiplication by the fixed program
numeral `alpha`. Both blocks start at `(c0,d0)` and finish at `(U,V)`.
Indeed, before shifting their final coordinates are

    q+(rq+1),             1-r(rq+1).

The registers in (8) have total degree at most three in the supplied
`x,q`. There are no additional supplied witnesses in this boundary
circuit. An arbitrary off-solution assignment can make computed `V`
negative; the exact trace and (6) force `0<V<2D` on every accepted
solution. No positivity of that computed register is assumed in advance.

## 4. A uniform packed interface with eight selected source fields

This section isolates the remaining history compiler's interface. In
addition to `q=2^t`, put

    B=4D,        P=B^t.                                 (9)

The shared length `t` in these two powers is an obligation of the
interface. The current native word kernels do not automatically prove
it for these variable-width state fields.

Supply four positive packed histories

    H_i = sum_(j=0)^(t-1) X_i(j) B^j,
    0<X_i(j)<2D.                                        (10)

For each coordinate `i`, let `s_i+(j),s_i-(j)` indicate its two signed
physical shear letters. At each time at most one of the eight selector
bits is one; all zero means the identity letter. The common selected
physical word must belong to (3). Define selector and selected-source
fields

    S_i+ = sum_j s_i+(j) B^j,
    S_i- = sum_j s_i-(j) B^j,
    Z_i+ = sum_j s_i+(j) X_(i xor 1)(j) B^j,
    Z_i- = sum_j s_i-(j) X_(i xor 1)(j) B^j.             (11)

These are digitwise selected fields. Ordinary multiplication of a
selector word and a history word would convolve their digits, so it
cannot be substituted for (11). Only eight selected-source fields are
needed, because each of the eight nonidentity letters updates a single
coordinate using its one mate. A full selection split of every register
under every letter is unnecessary.

Some fields in (11) may be zero. Supply instead their strictly positive
hats `S_hat=S+1` and `Z_hat=Z+1`. Define by paid arithmetic

    delta_i = (Zhat_i+ - Zhat_i-)
              - D(Shat_i+ - Shat_i-).                  (12)

Both `+1` shifts cancel exactly in the differences. Thus `delta_i` is
the packed signed state change from (7); its computed value need not
be positive. There are **20 strictly positive history fields**: four
`H_i`, eight `Shat` and eight `Zhat`. Together with positive geometric
parameters `q,P`, these are the supplied scalar coordinates of this
conditional interface. This is not a witness count for a completed
Diophantine certificate, because (9)--(11) and the regular controller
have not been compiled into a fixed polynomial system.

Now impose the four scalar comparisons

    B(H_i+delta_i) = H_i + E_i P - I_i,                 (13)

where `I_i` is `c0` or `d0`, and `E_i` is `U` or `V`, according to the
parity of `i`.

**Exact interface theorem.** Assume the stated synchronized digit
semantics (9)--(11). Then (13) holds if and only if the histories are
the actual shifted action of the selected physical word, with the
initial and terminal values (8). Combined with (3)--(5), this is exactly
the desired matrix-word acceptance relation.

To prove soundness, expand (13) in powers of `B`. Its constant residual
is `I_i-X_i(0)`, of absolute value less than `2D`. Its interior residual
at position `j>=1` is

    X_i(j-1) + change_i(j-1) - X_i(j).

By one-hot-or-idle selection and (10), the change has absolute value
less than `D`. Each interior residual consequently has absolute value
less than `3D<B`. Reduction modulo `B` forces the constant residual to
zero; divide by `B` and repeat to force every interior residual to
zero. The remaining top coefficient forces the terminal equality.
This final coefficient needs no advance size or sign assumption on
computed `U,V`. The already recovered recurrence and (6) prove their
positivity. Conversely any actual trace has the stated bounded digits,
and summing its local equations gives (13).

This is uniform in arbitrary `t`. It does not replace the unpaid digit
semantics by merely asserting that the packed integers are positive
or less than a common power. Those weaker scalar bounds would not
justify the coefficient argument.

## 5. Literal cost and the remaining implementation target

The checker contains the complete literal schedule. It first evaluates
(8), computes `B=4D` in one charged fixed-numeral multiplication, and
shares the two endpoint expressions

    R_even=U*P-c0,       R_odd=V*P-d0.                  (14)

Each coordinate then uses this seven-operation schedule:

    dZ=Zhat_plus-Zhat_minus;
    dS=Shat_plus-Shat_minus;
    DdS=D*dS;
    delta=dZ-DdS;
    next=H+delta;
    left=B*next;
    right=H+R_parity;

Compare `left=right` for free. Each lane costs `2M+5A`. The total is

| Part | Multiplications | Additions/subtractions |
|---|---:|---:|
| Ordinary-input boundary (8) | 4 | 6 |
| `B=4D` | 1 | 0 |
| Shared endpoint expressions (14) | 2 | 2 |
| Four lanes | 8 | 20 |
| **Conditional interface** | **15** | **28** |

The four comparison residuals have total degree at most five in these
supplied scalars; the term `-4q^4(Shat_plus-Shat_minus)` realizes degree
five. No final sum of squares or packed-word kernel is included in 43.

The remaining target is now precise: implement bounded four-register
signed-additive histories, with the eight digitwise source selections,
a fixed finite macro controller, and `q=2^t`, `P=(4q^2)^t` sharing the
same duration. The [PCP trace interface](matrix_pcp_trace.md) already
explains why selected weighted fields and missing digit bounds cannot
be free. This packet changes the matrix side of that problem: it pays
the input boundary explicitly and reduces the evolving matrix data
from eight coordinates to four using existing native power geometry.
It does not solve those remaining controller and typing obligations.

## 6. Exact checks and scope

Run the [stdlib checker](group_four_register_history.py) without
arguments to replay the [receipt](group_four_register_history.json).
It checks 564 signed determinant-one matrix factorizations and 128
regular macro fixtures. It checks 66,932 physical words, all words of
lengths two through five plus 512 longer randomized words, against
independent matrix multiplication and the entry/vector bounds. The
one-vector equivalence is checked in 535,456 matrix/input cases,
including inputs larger than the geometric parameter.

Fifteen actual positive packed traces include the ordinary-program
prefix `r=24x+12`. The literal 43-operation schedule has zero residuals
on them. Another 120 fixtures change a state digit and rebuild the
selected fields consistently; all are rejected. On 2,048 arbitrary
correctly typed histories the aggregate comparisons agree with direct
local recurrence and boundary evaluation. The checker also verifies
the explicit stabilizer counterexample when the height condition is
removed. These are finite audits of the source and proof interfaces;
they are not an unbounded history compiler or a membership decision
procedure.

Independent root full proof/source/default review passed, including the
entry bound with idle letters, determinant recovery, positive offset,
constant/interior/top coefficient induction and exact ledger. A second
independent full review also passed. Its separately written arithmetic
checks verified 2,048 arbitrary positive scalar assignments against four
manually expanded residuals and the 43=15M+28A count. Another 59,140
independently generated determinant-one cases checked the one-vector
implication with negative and large inputs, bounding only the required
upper-right entry. No findings were reported; these additional finite
checks remain supplementary to the parametric proofs above.
