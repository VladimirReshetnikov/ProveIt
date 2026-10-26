# One oriented reciprocal certificate for every exact-power request

New mathematical construction in this iteration. Source168's reciprocal
pooling proof already suggests the oriented weights n_j as a possible
generalization. We credit that suggestion: the work here supplies the complete
zero-base-tolerant theorem, its acyclic simultaneous bootstrap, and the literal
P207 instance. This note is an ordinary arithmetic proof; finite coefficient
checks are a separate task. It improves the explicitly inspected direct branch
and makes no global minimality or literature-wide priority claim.

## 1. General theorem, including zero and negative bases

Let W>=258, |A|>W^W, and b=floor(sqrt(W-1)). Consider at most five base
blocks, with at most seventeen requests in total. For block j the integer
base is n_j; request i has integer output m_i and signed index k_i.
Assume n_j^2,m_i^2,k_i^2<W. Assume (X_i,Y_i) is the canonical signed Pell
pair at A and index k_i, and Z_i=A*Y_i. Define

    T_j = 2*A*n_j - n_j^2 - 1,
    H_j = sum_i Y_i*(m_i-X_i),
    S_j = sum_i ((m_i-X_i+Z_i)^2-Y_i^2),
    E_j = S_j - 2*n_j*H_j.

For zero bases T_j=-1. For nonzero bases,

    |T_j| >= 2*|A|-W > W^W,
    sign(T_j)=sign(A*n_j).

Consequently every T_j is nonzero, without assuming any base is nonzero.
The following one polynomial equation has an integer z exactly when every
request at every NONZERO base has its exact signed-index output m_i=n_j^k_i:

    sum_j n_j*E_j*product_{l != j} T_l - z*product_l T_l = 0.       (O)

At |n_j|>=2 it also forces k_i>=0. At n_j=+/-1 it permits the canonical
signed-index unit value. At n_j=0 it intentionally imposes no power
condition. This last feature makes a simultaneous sign bootstrap possible.

### Soundness proof

Put delta_i=m_i-X_i+Z_i-n_j*Y_i. Direct expansion using Z_i=A*Y_i gives

    sum_i delta_i^2 = E_j - T_j*sum_i Y_i^2.                    (1)

Divide (O) by the nonzero product of all T_j. It says sum_j n_j E_j/T_j
is an integer. Thus by (1), sum_j sum_i n_j delta_i^2/T_j is an integer.

Let J be the set of nonzero base blocks, s=|J|<=5, and set

    C = product_{j in J} n_j^b,
    d_i = C*m_i - (C/n_j^b)*n_j^(b+k_i)   (i in block j in J).

All these are ordinary integers: C/n_j^b is an integer and b+k_i>=0.
The product over an empty J is 1. The inherited canonical signed-Pell
congruence is

    X_i+(n_j-A)*Y_i = n_j^k_i modulo T_j.

The negative power is legitimate modulo T_j, since T_j=-1 modulo n_j.
Multiplying by C therefore gives C*delta_i=d_i modulo T_j. Squaring and
summing proves that

    V = sum_{j in J} sum_i n_j*d_i^2/T_j

is an integer. Contributions at zero bases were identically zero and
cause no denominator or clearing-factor issue.

All |n_j|,|m_i|,|k_i|<=b. For j in J,

    |d_i| <= b^(s*b+1)+b^((s+1)*b) <= 2*b^((s+1)*b).

Writing r<=17 for the total request count, this gives

    sum_{j in J} sum_i |n_j|*d_i^2
      <= 4*r*b^(2*(s+1)*b+1)
      <= 68*b^(12*b+1)
      < W^(6*b+2)
      <= W^W.

The strict comparison uses 68<W and b^2<W. The last comparison follows
from 6*b+2<=b^2+1<=W, valid because b>=16. Hence |V|<1, so V=0.
For every j in J, n_j/T_j has the SAME sign, sign(A). All summands in V
have that sign or are zero. Thus each d_i=0. Since C is nonzero, this
implies m_i=n_j^k_i in Q. At |n_j|>=2, a negative k_i would give
m_i*n_j^(-k_i)=1, impossible for integers. This proves the assertion.

### Completeness proof

At every nonzero base an exact power makes T_j divide delta_i. By (1),
T_j divides E_j. Therefore

    z = sum_{j:n_j != 0} n_j*E_j/T_j

is an integer and satisfies (O). A zero base has coefficient n_j=0 and
contributes nothing. No coprimality of distinct moduli is required.

## 2. Literal P216 instance

The exact source is
`../source/equation216.json`.
Its variables are x_0,...,x_215. The actual A is x_134+1. Actual Pell
differences D_i=X_i-A*Y_i are convenient, so form

    H_j = sum_i Y_i*(m_i-D_i-Z_i),
    S_j = sum_i ((m_i-D_i)^2-Y_i^2),
    E_j = S_j - 2*n_j*H_j.

The five bases are t=x_0, B=x_4, BH=x_186, q=x_94-1, q+1=x_94.
The seventeen requests and their exact existing affine ports are:

| request | block base | output m | signed index k | D | Y | Z |
|---|---|---|---|---|---|---|
|0|t|x3|x0|x138|x139|x140|
|1|B|x17|x1|x174|x175|x176+1|
|2|BH|x94-1|x1|x174|x175|x176+1|
|3|q+1|x95|x0+x3|x147|x148|x149|
|4|q|x96|x0|x138|x139|x140|
|5|q+1|x100|x8-1|x150|x151-1|x152|
|7|q+1|x103|x9|x153|x154|x155|
|8|q+1|x106|x10|x156|x157|x158|
|9|q+1|x109|x11|x159|x160|x161|
|10|q+1|x112|x12|x162|x163|x164|
|11|q|x113|x2|x165|x166|x167|
|12|q+1|x116|x13|x168|x169|x170|
|13|q+1|x119|x14|x171|x172|x173|
|14|q|x120|x1|x174|x175|x176+1|
|15|q+1|x124|x15|x177|x178|x179|
|16|q+1|x127|2*x16|x180|x181|x182|
|17|q+1|x130|J|x183|x184|x185|

Here the projected derived-label index is the explicit affine expression

    J=-4-3*x8-7*x9+4*x19+2*x22+2*x26+2*x28+2*x30+2*x32
      +4*x34+2*x35+2*x38+2*x41+4*x60+2*x61.

Delete coordinates 141,142,143,144,145,146,212,213,214,215 and rows
97,98,99,100,101,102,149,150,151,152 (all indices here zero-based in P216).
The deleted coordinates are three singleton modulus/quotient pairs and
the two K,L pool pairs. The remaining 143 rows use no deleted coordinate.
Add one new coordinate z and the one residual (O). Relabel the retained
coordinates in increasing original index order, followed by z.

This specifies 207 unrestricted integer coordinates and 144 residuals.
The first 143 residuals remain quadratic. The new residual is of degree12,
so the sum of their squares has exact degree24. In the ORIGINAL P216
coordinate IDs, its degree12 monomial

    x0^2*x4^2*x94^4*x130*x184*x186^2

has coefficient -2. Indeed x130 is the output unique to request17 at base
q+1. Its only degree12 contribution is
-2*n_(q+1)^2*x184*x130*product(other T_j), using -n_j^2 from the degree2
part of each other T_j. Every other choice includes the independent A
coordinate, and every term from S_j containing x130 has degree at most11.
No other block contains x130. Thus the degree12 homogeneous part is nonzero;
its square has degree24 and the retained quadratic squares cannot cancel it.
In the reduced207 IDs this monomial is
x0^2*x4^2*x94^4*x130*x178*x180^2.

## 3. Acyclic soundness bootstrap in the new system

The inherited Pell orientation and square frame use none of the ten
deleted power rows. Thus they authenticate the canonical signed pairs,
the actual affine-port square bounds, and |A|>W^W first. The theorem above
now says, in one step, that every request whose base is nonzero is exact.

1. t=16+4*d^2>=16, so its base is nonzero. Hence F=t^t is a positive even
   integer and F>=2^64.
2. The retained row B*h_B=C+F+1 has C even, so B is odd and nonzero.
   The retained H is 2 modulo4, hence nonzero and |BH|>=2.
3. The theorem therefore gives x>=0 and q=(BH)^x. Thus q is nonzero.
   The affine beta spacing y=F*(2*v+1) gives |y|>=F and
   |1+(t+1)*y|>1. If x=0, the terminal endpoint forces this last integer
   to divide -1, impossible. Thus x>=1 and |q|>=2.
4. The theorem applies to the q request with signed index y+1. It gives
   y+1>=0; but a negative y is <=-F<-1, so y>=F>0.
5. The initial endpoint x=F+1+(y+1)*u_0 forces u_0>=0, hence x>=F+1.
   The terminal endpoint then gives x>=2+(t+1)*y. Thus |q|>=2^x,
   so q+1 is a nonzero nonunit.
6. All q+1 requests are exact with nonnegative indices. The unchanged
   signed-binomial recovery gives B=binom(F+t,t)>0, H>0, q>0, and the
   complete inherited CRT/flow decoding gives a finite C222 refutation.

This is the same already-proved source bootstrap with each appeal to an
individual power or fixed-base pool replaced by the corresponding
conclusion of the zero-base-tolerant theorem. No as-yet-unproved sign is
needed to apply the theorem. It is essential that the theorem tolerates
zero bases, since B's nonzero value depends on first recovering F.

## 4. Restoration and the logical equivalence

After the bootstrap every base is nonzero. The theorem has recovered all
seventeen powers. Set each singleton modulus to T_j and its old quotient
to -delta_i/T_j (the literal old congruence row is delta_i+T_j*quotient).
For each of the two old multi-request pools set

    L_j=E_j/T_j,  K_j=2*H_j+(2*A-n_j)*L_j.

All are integers by exact powers and the canonical congruence. These
restore all ten omitted rows without changing the retained coordinates.
The original P216 zero therefore exists. Conversely any P216 zero gives
the canonical exact powers, so the preceding completeness proof constructs
z and a new zero. This is existential zero-set equivalence, not a global
polynomial bijection (restorations involve divisions known integral on zeros).

Composing with the precisely inherited P216 calibration proves in ZFC
that the new207-coordinate equation has no integer zero iff Con(ZFC).
This relies on the cited ordinary unbounded parent proof/calibration and
is not an emitted object-language ZFC proof or a new end-to-end Lean build.
