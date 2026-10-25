# Independent mathematical audit: factorial-free certificate

Prepared as a separate derivation within the AI-assisted research workflow.
This is an ordinary proof audit, not a proof-assistant certificate or an
outside human referee report.

## 1. Polynomial multiplicities replace pairwise-coprime label weights

Let all labels lie in {0,...,t}, and let t rows satisfy the valid Horn flow
identities with weights W_j=1+jF, start F+1 and finish 1. Telescoping gives

    product_i (1+v_i F) = (1+F) product_i (1+p_i F)(1+q_i F).

The final choice is F=[2(t+1)]^t. Remove every unit factor with label
zero. If the remaining factor counts differ, let d be their minimum.
The left side has at most t factors, so d<=t. The side with more factors
is at least (F+1)^(d+1), while the other is at most [t(F+1)]^d.
But F+1>t^t>=t^d, giving a strict contradiction. Hence the counts are
equal and both are at most t. This includes d=0 without exception.

Each resulting product polynomial has nonnegative coefficients with
sum at most (t+1)^t<F. Thus every signed coefficient of the difference
has absolute value <F. A
polynomial with integer coefficients of absolute value <F cannot vanish
at F unless all coefficients vanish: reduce modulo F, remove the zero
constant coefficient, divide by F, and repeat. Equality of polynomials
then gives equality of multiplicities of the distinct linear factors
1+jZ for j>0. The factor for j=0 is one, as required for the free truth
label. The existing finite closure argument recovers a derivation of 1.

There is no need for the numerical label weights to be coprime. The
factor-count argument is essential for the final affine-base growth
choice: a blanket degree bound 2t+1 would require a larger F.

## 2. Generalized binomial CRT theorem

Put Lambda=lcm(1,...,t), and let R>=Lambda^2. For any i in {1,...,t},
R+i>Lambda^2, so there is a prime p for which

    v=v_p(R+i)>2 ell,   ell=floor(log_p t)=v_p(Lambda).

For j!=i, v_p(j-i)<=ell<v, and hence v_p(R+j)=v_p(j-i).
Let a=v_p(t!), b=v_p((i-1)!(t-i)!), c=a-b. For every prime-power d=p^r,

    floor(t/d)-floor((i-1)/d)-floor((t-i)/d)
       = floor(((i-1) mod d+(t-i) mod d+1)/d)

is zero or one, and is zero when d>t. Consequently 0<=c<=ell; this
also proves t*binom(t-1,i-1) divides Lambda. For

    B=binom(R+t,t),  e=v_p(B)=v+b-a=v-c,

we obtain e>ell and e<=v. Thus p^e>t and p^e divides R+i. Every row
therefore has a prime-power separator belonging to B, even though p
itself need not exceed t and the factors R+i need not be coprime.

For soundness, B|C+R+1 and N=B^K|binom(C,t) imply that C modulo p^(Ke)
is some s in [0,t-1]. Its residue modulo p^e is i-1, so p^e>t forces
s=i-1. The same range lemma recovers each bounded local witness modulo
p^(Ke). Local divisibility and 0<=L<2^K<=p^(Ke) give L=0.

Completeness must use ALL primes of B, not only the chosen separating
prime for each row. For every p|B, e=v_p(B) is at most
max_i v_p(R+i): the valuation of a binomial is a sum of zero-or-one carry
terms, with no nonzero term above that maximum. Choose an i with
p^e|R+i and assign p to that valid row. CRT modulo p^(2Ke) sets C and
all witness representatives equal to that row's data. This proves the
index and local divisibilities. A binomial range of lower index k<=K has
a falling-factorial numerator factor of valuation >=2Ke, and division
by k! loses at most k-1<K<=Ke. It is therefore divisible by p^(Ke).
Combining every prime yields every required divisibility by N.

The weaker hypothesis R>(t!)^2 is consequently valid as well. The
selected R=F^2 exceeds both thresholds by a large margin. A still sharper
sufficient rowwise numerical hypothesis is

    R+i > Lambda * [t*binom(t-1,i-1)]  for every i,

by the identical valuation argument with threshold ell+c rather than
2ell. This sharpening is optional and does not alter the chosen circuit.

## 3. Selected signed bootstrap with odd-square radix

Use q=(2z+1)^2>=1 and H=2+sum of the nine actual CRT representatives.
Their power requests at q+1>=2 force all actual representatives to be
nonnegative; hence H>=2. The raw row C0+F^2+1=B*iota excludes B=0.
The power request q=(BH)^x has a nonzero base of absolute value >=2.
The signed canonical-power lemma excludes x<0 (it would imply an
integer m with m*(BH)^(-x)=1), and then gives q=(BH)^x exactly.
The extension to a possibly negative base n=BH is valid: the original
proof uses absolute-value bounds and the congruence T=-1 modulo n for
T=2An-n^2-1. For 2<=|n|<W, |T|>W^W+W; signed canonical Pell
recurrences give m=n^k modulo T for k>=0 and m*n^(-k)=1 modulo T
for k<0. The frame bounds make these congruences exact, and the latter
integer equality is impossible when |n|>=2.

After the separately positive t-indexed power yields F, the beta
endpoints and y>=F+3 give x>=F+1 and x>=2+(t+1)y. With the square-multiple
replacement from ODD_SQUARE_BETA_PROOF.tex, y>=F is sufficient, provided
the x=0 and y=F exceptions are excluded in the stated order.

It follows that q=|BH|^x>=2^x>1 and |B|<q/2. Do not infer B>0 at this
stage, because x can be even. Instead, the true binomial coefficient
C=binom(F^2+t,t) satisfies C<q/64: use

    F^2+t<=F(F+1)<=2^(F-1),
    binom(F^2+t,j)<=2^[t(F-1)]<=q/2^(F+t+2)<q/64.

Consequently the largest relevant coefficient divided by q-1 is
strictly less than 1/32, which supplies the low-remainder margin needed
for the common norm's completeness.

The common centered remainder bound yields B=C modulo q, and
|B-C|<q forces B=C>0. The proof must obtain the bounded remainder for
this one digit without assuming that all the other digits are already
semantic. A sum-of-squares common budget gives the needed bound on each
individual remainder independently, so that order is valid.

The remaining powers are now positive genuine powers. The shift H=2+sum
also repairs the all-zero-representative edge case: max(1,n)+1<=H for
any largest syntax representative n. Thus h<=H^ell and the unchanged
derived-label coefficient bound follows from ell(t+1)<x.

## 4. Completeness parities

The final F has v2(F)>=t. Therefore v2(F^2)>floor(log2 t), and
v2(F^2+i)=v2(i) for 1<=i<=t. This proves B=binom(F^2+t,t) is odd.

Choose y an even multiple of t! large enough for all pending products;
the square-multiple replacement achieves this cofinally. The beta CRT
moduli are odd, so x may be chosen even. The later generalized-CRT
precision moduli are also odd, so each actual representative has freely
prescribable parity. Choose all representatives except the dominant
syntax representative a even, and choose a odd and sufficiently large.
Then the unchanged semantic anchor h=1+a+b modulo 2 is even, while
H=2+sum representatives is odd. Thus q=(BH)^x is an odd square.

There is no aggregate upper bound on those representatives in the
selected self-sized-radix architecture. Increasing them by their odd CRT
modulus to set parity and dominance is therefore allowed. Their actual
values are used to define H and q afterward.

## 5. Scope and points that must be preserved in the literal build

* Keep the strict beta-quotient lower indices equal to x (not x+1),
  because amplification is K=x.
* Keep the index range N|binom(C0,t); a fixed small canonical index is
  not a replacement for it.
* Include each changed power base, exponent and output in the square
  frame W. In particular the replacement base 2(t+1) must occur.
* Use p^e>t to identify rows; p>t is no longer available.
* Keep the fresh nonnegative arithmetic-sign recovery separate from
  the stored shifted representative coordinates, which may be negative.
* Do not reuse the old factorial fixed-point or reciprocal-modulus
  proof after deleting its ceiling rows. The theorems above replace it.
* Recompute the emitted coefficient support, exact degree and all
  monic-restoration certificates after the source mutations.

## 6. Independent literal power-interface check

The final raw affine-base source was also checked by
`audit_final_power_interface.py`, which imports no construction,
factorization, projection, or translation module. Its independent request
table reconstructs all eighteen power congruences, all five base moduli,
all thirty-seven distinct frame atoms, all fourteen principal-pair norms
and their complete orientation pool, and the one-step derived pair at
index t+1. It additionally checks the F/U alias, d=2(t+1), H=2+sum of the
actual representatives, both odd-square rows, the beta product, and the
cofinal horizon. It passed normally and with Python optimization enabled.

The audited raw-source byte hash is

    7b2d75791f10c717bbadca278e78e9f315508d56acdc8ad3eb82b63ddbb2e855

The machine-readable reports are `FINAL_POWER_INTERFACE_AUDIT.json` and
`FINAL_POWER_INTERFACE_AUDIT_OPTIMIZED.json`. Projection to the final
quartic must still be covered by its separate integral-restoration audit.

No gap was found in the mathematical replacements or this literal power
interface under the stated hypotheses. The inherited Pell theorem and
C222/ZFC calibration, and the final source-to-polynomial transport,
remain explicitly separate proof and audit boundaries.
