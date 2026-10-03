# A transport quotient change lowers the universal degrees to 178 and 134

The [complete source](complete86_transport_quotient_shear.py) and
[receipt](complete86_transport_quotient_shear.json) preserve the two actual
[first-root universal polynomials](complete86_factored_first_root.md) under
an integer coordinate change. Their operation counts remain **86=48M+38A**
and **87=47M+40A**, while their exact degrees fall from 179/135 to **178/134**.
Both retain nineteen strictly positive witnesses and the same ordinary
positive input and fixed-program numeral recipe. The separate established
comparison-system bound remains 74 operations.

The change is a full positive-zero bijection. Its positivity proof uses
only the transport factor being an integer unit and the supplied positive
coordinates; it precedes every inherited native-kernel or compiler theorem.
Neither direction preserves the entire positive orthant off the zero set.

## Actual source substitution

Write the existing paid quantities as

\[
q=(B-1)J+1,\quad r=q-1,\quad X=wq,\quad
C=q-F-Z-\alpha-\ell x,\quad U=q-F,
\]

where `ell=twice_cell_bits` is the positive fixed numeral `2d`, and
`K=Kconstant` is the positive compiler numeral `DC+B*DR`. In the literal
source these ports are `q,repunit,wn2,marked_rhs,q_minus_F`. They remain
computed and paid. In particular C is not a new supplied coordinate.

The parent transport factor is

\[
N_t=(K+wq)C+U-zr,
\]

with supplied positive `z=zplus`. Supply `t=transport_quotient` instead,
and change that factor to

\[
\boxed{N'_t=(K+w)C+U-tr.}
\]

In the complete literal source this changes only the second operand of
`kinner=Kconstant+wn2` to `w`, and the supplied quotient name at the one
consumer `local_rhs=zplus*repunit`. The intermediate `wn2=w*q` remains paid
and live in the other factors. All seven other factor definitions, all
seven final factor multiplications, and the final
subtraction of one are retained. There is no CSE, dead-code discount or
new fixed numeral hidden in the count.

The integer coordinate maps are

\[
t=z-wC,\qquad z=t+wC.
\]

C is independent of both quotient coordinates. Therefore the maps are
inverse on the entire integer coordinate spaces. Since `q=r+1`,

\[
(K+wq)C+U-(t+wC)r=(K+w)C+U-tr.
\]

This is an all-value polynomial identity over any commutative ring.
The old quotient has no other literal consumer. The other seven factors
are independent of it, so substitution preserves the **entire complete
polynomial**, including the actual finalizer, and not merely the vanishing
set of the transport equation.

## Full positive-zero theorem

For the positive-coordinate proof, `q>=2`, `K>=1`, `w>=1`, `F,Z,alpha>=1`,
and `ell*x>=1` suffice. The inherited compiler has the stronger actual
restrictions `B>=16` and `ell=2d`. No proposed arbitrary positive numeral
tuple is thereby certified as a valid universal program.

At any complete parent or child zero, the product of all eight integer
factors is one. Hence its transport factor is `epsilon` in `{1,-1}`.
For either positive quotient coordinate `v` one has

\[
U-v(q-1)=1-F-(v-1)(q-1)\le0.
\]

The coefficient of C is either `K+wq` or `K+w`, both at least two.
If C were at most -1, the corresponding transport factor would be at
most -2, contradicting its being a unit. Consequently **C>=0** at every
parent and child positive zero, before any computation is decoded.

For a child zero, restore `z=t+wC`. It is a positive integer, and the
complete graph identity gives a positive parent zero. All other supplied
coordinates and the ordinary input remain unchanged.

For a parent zero, the algebraic image `t=z-wC` is an integer, and the
parent transport identity gives

\[
(q-1)t=(K+w)C+U-\epsilon
       =(K+w+1)C+Z+\alpha+\ell x-\epsilon\ge2.
\]

Since `q-1>0`, this proves `t>0`. The complete graph identity gives a
positive child zero. Both maps are inverse, so this is a bijection on the
**full positive zero sets**, rather than only a canonical slice or an
existential re-encoding at a different radix. Both unit signs are covered;
there is no assumption that the transport factor has already been proved +1.

The parent's universal ordinary-input theorem now transfers to the new
source with exactly its old fixed numeral recipe. No decoded-history
conclusion was used to establish the positive inverse.

## Exact degree on every admissible fixed program slice

Numeral ports are held fixed when measuring degree. Put

\[
Q=(B-1)J,\quad k_0=\eta+\zeta,\quad g_0=\rho+\sigma,\quad
C_1=Q-F-Z-\alpha-\ell x.
\]

The new transport factor is quadratic with leading homogeneous form

\[
T_2=wC_1-tQ.
\]

It is nonzero uniformly: the coefficient of `tJ` is `-(B-1)`, which
does not vanish for an admissible program. The seven other factor
polynomials are unchanged, so their proved exact degrees and leading
forms transfer from the pinned parent. The resulting exact factor lists are

```
normalized: 22,18,32,56,7,2,34,7  (sum 178)
ordinary:   22,18,32,24,7,2,22,7  (sum 134).
```

Their complete leading forms are, respectively,

\[
-32Q^{107}h^2g_0\delta^2i^4k_0^{13}w^{17}s^{30}T_2,
\]

\[
+32Q^{79}h^2g_0\delta^2i^2f^2k_0^9w^{13}s^{22}T_2.
\]

They follow by replacing the parent's transport leading factor `wQ C_1`
by `T_2`, leaving the other seven homogeneous factors unchanged. Each
displayed product is nonzero in the polynomial ring on the witness/input
variables for every admissible fixed program slice. The final subtraction
of one cannot affect its leading term. This proves exact degrees 178 and
134 uniformly, not just at the saved numerical degree fixtures.

Simple maximum/sum propagation along the unchanged source overestimates
the main and input norms because it ignores their internal cancellations.
The receipt records those honest syntactic bounds separately as 188/144.
The sharper upper bound comes from the seven inherited exact factor bounds
and the new quadratic transport factor. Six complete dense univariate
expansions additionally attain the claimed degrees and displayed leading
coefficients; they supplement the uniform proof.

The present operation/degree catalogue therefore replaces 86/179 and
87/135 by **86/178 and 87/134**. Other maintained frontier points are not
recomputed or changed by this packet. In particular, no transfer to all
earlier grouped schedules is silently claimed. Minimum operation bounds
remain **74 certificate / 86 polynomial operations**.

## Executable evidence and replay

The standard-library helper authenticates the complete first-root
source/receipt/proof trio on every canonical public entry. It reads the
saved parents without executing historical Python. It accepts both
literal complete modes, emits all paid gates, and checks source closure,
every live supplied port, the nineteen-witness interface and full M/A
counts. The metadata distinguishes the two exact degrees from syntactic
gate-propagation bounds.

Its local proof expands the transport identity at independent
`r,w,K,C,t,U` cuts with exact integer coefficients. The verified literal
`q=r+1` and `X=wq` definitions connect those cuts to the actual circuit;
the other factors and complete finalizer then match structurally. There
are eighteen factor/finalizer identities across the two modes, 128 complete
numeric identities including 32 rational cases, six full dense degree
checks, and 1,270 bounded local transport-unit examples covering both signs.

These local unit examples are not full universal halting witnesses. The
unbounded positive-zero conclusion follows from the inequalities above,
and the universal conclusion uses the inherited theorem. No astronomical
native Pell tuple is materialized.

The public integer maps deliberately permit signed values. Separate
positive-zero maps demand a complete zero before applying the proved
positive transport. Explicit positive off-zero fixtures show a negative
restored old quotient in one direction and a negative new quotient in the
other. Strict packet/type checks, independent returned copies, changed-pin
rejections after warmed calls, and optimized-Python rejection are included.

From any working directory:

```sh
python /path/complete86_transport_quotient_shear.py \
  --root /path/to/native-stream-queue \
  --expect /path/complete86_transport_quotient_shear.json
```

`--output FILE` writes a fresh deterministic receipt. JSON types are
checked before writing and on exact saved-receipt replay. The receipt
records its checker source hash. This is a proved coordinate reduction
with executable evidence, not a Lean formalization or an unrestricted
arithmetic-circuit optimality result.
