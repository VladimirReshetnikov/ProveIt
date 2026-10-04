# Two target coordinates for a complete 193-generator recoding

The [complete array](matrix193_kernel_row_projection.json) retains the same
finite-U15-input membership language while admitting an exact two-coordinate
upper target interface. Given correctly indexed Pell coordinates, the entire
generic target assembly costs **6=4M+2A**, down from twelve for four upper
entries. The new even-block Pell parameter is **4417**. This is a conditional
target-assembly improvement, not a six-operation universal equation: the
index-coupled Pell relation and unbounded matrix-product certificate remain
unpaid. The established universal polynomial bound stays **84**.

The key invariant is stronger than determinant one. In the chosen upper and
lower groups, a matrix is uniquely determined by its first row. We prove this
for the entire groups, including all inverses, so dropping the other rows
cannot introduce a false target among actual semigroup products.

## 1. An elementary first-row lemma

Use the same matrices as the [193-generator predecessor](group_directed_semigroup193.md):

```
P=[[1,2],[0,1]], Q=[[1,0],[2,1]],
F=<P,Q>, K=ker(exponent_Q:F -> Z).
```

The integer matrix group F is free on P,Q. One direct ping-pong proof uses
the disjoint regions |x|>|y| and |y|>|x| in nonzero real vectors: every nonzero
power of P sends the second into the first, and every nonzero power of Q
sends the first into the second. Indeed
`|x+2ny| >= 2|n||y|-|x| > |y|` in the first case, with the roles reversed in
the second. The usual reduced alternating-word argument proves freeness;
the predecessor uses this same premise. Consequently exponent_Q is a
well-defined integer homomorphism. Every matrix in F is the identity modulo2.

**First-row lemma.** If M,N belong to K and have equal first rows, then M=N.

Proof: the first row of N M^-1 is (1,0). Its determinant is one, so it has
the form `[[1,0],[k,1]]`. Since it belongs to F, k is even and this matrix is
exactly Q^(k/2). But it also belongs to K. Its Q exponent is therefore both
k/2 and zero, giving k=0 and N M^-1=I. No division is performed in a target
circuit, and no extra determinant equation is appended. These are structural
properties of the actual matrix groups.

The subgroup condition is essential. I and Q^2 have the same first row and
both belong to the identity-modulo2 determinant-one group. The earlier
[1057 recoding](matrix193_schreier_recode.md) contains Q^2, so its first row
alone is not injective on its upper group. Determinant and parity by
themselves justify only a three-entry projection, not this two-entry one.

## 2. A faithful twenty-letter encoding inside K

Put `E_j=Q^-j P Q^j`. The twenty elements E_0,...,E_19 freely generate.
To see this directly, group a reduced word into nonzero powers of adjacent
distinct E_j. Expanding leaves nonzero P powers separated by nonzero Q
powers, with optional outside Q powers. It cannot reduce to the identity
in F. Each E_j has Q exponent zero.

Make the invertible free-basis change

```
a=E_0 E_1^-1, b=E_1; conversely E_0=ab, E_1=b.
```

Assign a to0, b to1, and E_2 through E_19 in order to
`A,...,O,[,],#`. Thus all twenty active letters have a faithful free-group
encoding Psi into K. The old inactive X is excluded. This is a full alphabet
construction; faithfulness of just the two tape letters would not suffice.

For every one of the unchanged 96 directed tiles, emit

```
A_i=diag(Psi(h_i), E_i),
B_i=diag(Psi(g_i)^-1, P^-1 E_i^-1 P),
C=diag(Psi([J1]#)^-1, P).
```

The receipt saves every entry of all193 matrices and keeps the parent rule
and tile arrays, identifiers, terminal word, and lower blocks. Every upper
block lies in K by the alphabet construction. Every lower block lies in K
because E_i and P do, and K is a subgroup. The same is consequently true of
both blocks of every nonempty positive product.

For a finite configuration word w, define the full target

```
T(w)=diag(Psi(w#)^-1,P).
```

The lower-marker proof from the predecessor forces every product at this
full target to be `A_(i1)...A_(id) C B_(id)...B_(i1)`. Faithfulness of Psi
then gives the unchanged literal equation

```
w# h(s)=g(s) [J1]#.
```

The existing rewrite/cleanup theorem therefore gives exactly the original
finite-input acceptance language. Alternatively, identifying the two
faithful upper images with the same abstract free group, while fixing the
lower image, preserves every generator-word equality and corresponding full
target. This is not an assertion that arbitrary unrelated SL4 matrices
represent the same predicate.

## 3. Exact projected membership, with two varying integers

Define one fixed relation R(u,v) on signed integer inputs as follows:
there exists a nonempty positive product Z of the193 fixed matrices with

```
(Z_11,Z_12)=(u,v), (Z_33,Z_34)=(1,2).
```

Positions here are one-based. All products are block diagonal; both blocks
belong to K. The first-row lemma applied to the lower block and P first
recovers the entire lower target. When `(u,v)` is the first row of
Psi(w#)^-1, the same lemma recovers the entire upper target. Thus

```
R(firstrow(Psi(w#)^-1)) iff T(w) belongs to the fixed semigroup.
```

This holds for every finite target word w, and in particular for every
valid finite U15 input. R is computably enumerable by enumerating finite
nonempty generator words, and it is many-one c.e.-complete by the inherited
U15 reduction followed by this explicit computable pair-valued map. The
lower first-row constants require no varying target coordinates.

The result concerns **actual certified products**. In a future polynomial
encoding, the proof that the witnesses describe such a product must remain
intact. Merely freeing the omitted entries of an arbitrary matrix does not
retain this equivalence. It also does not price conversion of the signed
target integers into some other natural-number interface.

## 4. The literal six-operation indexed target

The [fixed-context initialization theorem](u15_unary_block_interface.md)
remains valid because the physical word and machine have not changed. For
each selected c.e. set, use its parity-adjusted unary length2x+4, with the
decoding performed inside the simulated program. Its finite configuration
has the form `U_S (W^2)^x V_S`, where `W=01010111=(01)^3 11` and U_S,V_S are
fixed effective contexts. The four padding copies are in the fixed prefix.

For the present encoding,

```
Psi(W)=P^3 E_1^2=[[-87,-38],[-16,-7]], trace=-94,
B=Psi(W)^2=[[8177,3572],[1504,657]],
a0=trace(B)/2=4417,
D=B-a0 I=[[3760,3572],[1504,-3760]],
Delta0=a0^2-1=19509888, D^2=Delta0 I.
```

It follows by multiplication in this quadratic algebra that
`B^-x=chi_4417(x) I-psi_4417(x) D` for every natural x. Set the fixed context
matrices `L=Psi(V_S#)^-1`, `R=Psi(U_S)^-1`, `C=LR`, and `F=LDR`.
The two required target coordinates are the first row of

```
chi C - psi F.
```

The complete generic source is

```
cu11=chi*C11; dv11=psi*F11; target11=cu11-dv11;
cu12=chi*C12; dv12=psi*F12; target12=cu12-dv12.
```

The four coefficients are fixed computable signed integers for the selected
program. The six paid gates are four multiplications and two subtractions;
every gate and supplied port is live. This is an upper bound for all
contexts, without a minimality claim or a claim that every coefficient is
nonzero. Fixed coefficient preparation and the unbounded simulation are
not being confused with a varying arithmetic operation on x.

The supplied pair must be **correctly indexed at x**. The Pell norm alone
admits the index-one pair for every x; on a compiled singleton language
containing1, freeing that pair would accept all positive inputs. Nor has
this report emitted a fixed-arity certificate for R. The six-operation
component therefore does not replace the full84 universal polynomial.

## 5. Complete coefficient tradeoff and bounded evidence

| Resource | Original193 | Schreier1057 | Kernel4417 |
| --- | ---: | ---: | ---: |
| Generators |193|193|193|
| Integer entry slots |3088|3088|3088|
| Nonzero entries |1543|1541|1543|
| Maximum absolute entry |1304111120|5094184660|371425216|
| Maximum magnitude bits |31|33|29|
| Sum of magnitude bits |19321|20785|19888|
| Even-block Pell parameter |39979681|1057|4417|
| Displayed indexed assembly operations |12|12|6|

The original193 upper group also lies in K, so the first-row lemma gives
it the same six-operation projected interface if desired; the final row
reports the previously displayed four-entry templates for the first two
columns. The1057 construction has a smaller Pell parameter but lacks this
particular subgroup invariant. These figures are distinct resources, not
a total order or global optimality assertion.

The [fresh helper](matrix193_kernel_row_projection.py) reads six pinned
files as data only. It reconstructs all3088 old entries, emits all3088 new
entries, checks all193 unchanged lower blocks, the invertible basis change,
kernel exponents, congruences, block determinants and distinct matrices.
The retained accepted word `[110A0]` has its full167-generator product
checked in all16 entries, as well as its four observed coordinates.

Thirteen exact power pairs and1,300 complete target assemblies over diagnostic
context words check the literal six-row source against full matrices and
literal word products. These contexts are not claimed to be arbitrary
program-compiler outputs. The helper also checks457 distinct reduced words
in four generators and their first rows; this is bounded corroboration,
not the proof of row injectivity or freeness. The unrestricted proofs are
Sections1–3. The Q^2 counterexample records why parity alone is insufficient.

With the frozen trio installed, from any directory:

```sh
python3 /absolute/path/matrix193_kernel_row_projection.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/matrix193_kernel_row_projection.json
python3 -O /absolute/path/matrix193_kernel_row_projection.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/matrix193_kernel_row_projection.json
```

`--output FILE` writes the deterministic receipt instead. JSON comparison
is recursive and type-exact, and checks use explicit exceptions in normal
and optimized Python. No predecessor module, archive program, compiler
builder, historical suite or arbitrary-program compiler is executed.
