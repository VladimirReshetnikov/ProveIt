# Multiplier-dependent polynomial absorption of the strong Pell root

A fixed polynomial replacement of the strong root still has finite ordinary-
input projection when its arguments may include the strong multiplier i and
its two source products. This extends the earlier85-value interface to all
**88 values independent of f,T,y** in the literal complete84 source.

For each valid fixed compiler slice, let G be a fixed integer polynomial in
these88 formal arguments, t its degree, and L=max(1,sum of absolute coefficients)
after combining like terms. Use t=0,L=1 for identically zero G. Substitute
f=G literally while keeping every other supplied witness positive. Every
resulting zero satisfies

    G!=0,
    2d*x+b_source < R < c < max(12t,5)+1+ceil(log2(L²+2)).

The proof includes negative G and its impossible zero-value sector. It is a
fixed-substitution obstruction; the complete84 circuit and operation bound
are unchanged. It does not supply a paid implementation of arbitrary G.

## 1. Exact interface and inherited premises

The source is the unchanged complete84 array in
`complete84_scaled_strong_output.json`, SHA-256
`8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`.
Use

    A0=a+2, Delta=A0²−1, c=R10a, R=r_lhs,
    D=chi_R(A0), S=Delta*i*c², R16=S².

The inherited premises are the direct signed-domain rank and exterior bounds
in the [signed-quotient theorem](complete84_signed_quotient_absorption.md),
and the exact sign/zero-root identities in the
[strong-root theorem](complete84_strong_root_absorption.md). Their source and
proof bytes are authenticated by the fresh helper; the nine direct pins are
listed below. No positive-parent compiler theorem is applied to signed T.

A direct dependency propagation through all84 literal rows, removing the
supplied ports f,`auxiliary_quotient`,y, gives **66 computed and22 supplied
values**. Relative to the old64+21 boundary it adds precisely

    i,
    aux_coefficient_root = i * Ac2 = Delta*i*c²,
    R16 = aux_coefficient_root * aux_coefficient_root.

Here Ac2=Delta*c² is an already existing old-boundary value; S and R16 are
computed values, not independently supplied coordinates.

The complete66 computed names, in actual source order, are:

```text
tau_square repunit q Lbig n2 wn2 sn2 UM R10b ksn2
first_root_base first_next first_product norm_first R10a R12
cam2 D1 gamma_sum a4 a4m5 gam R14 L15 a_square A c2 Ac2
norm_main norm_pair q_minus_F q_minus_FZ C_after_alpha scaled_t
marked_rhs W odd_index index_product index_rhs difference_multiple
exponent_partial modulus_multiple exponent_rhs mu2 kappa2
scaled_kappa2 norm_input norm_triple hpm1 index_difference
gap_product gap Lm1 rproduct qMF mask_factor mask r_lhs norm_index
kinner innerC transport_partial local_rhs norm_transport
aux_coefficient_root R16
```

The complete22 supplied names are:

```text
Jrep F alpha transport_quotient h i s w tau_root eta zeta Z
delta rho sigma x Bm1 Kconstant twice_cell_bits inner_bits MC MF
```

Thus the boundary includes every literal f/T/y-independent computed and
supplied value, with its actual dependencies. In particular it excludes
f² and the scaled strong norm, both of which still depend on f.

Fix a valid compiler-numeral slice and an integer polynomial G in these88
formal arguments. Let t be its total degree and
L=max(1,sum of absolute coefficients), after combining like formal
monomials. Set t=0,L=1 for G identically zero. Coefficients are fixed while
input and witnesses vary. Substitute f=G literally and retain all other
supplied witnesses, including i,T,y, positive.

The existing exact simultaneous (f,T) sign identity still applies: all88
arguments are independent of f,T. If G has nonzero value, replacing f by
|G| and T by sign(G)*T preserves the full polynomial and every argument of
G. The resulting tuple lies in the signed-T lemma's exact domain. If G has
value zero, the existing full-source zero-f contraction excludes the tuple
before any native argument. Therefore at any putative zero the signed-domain
conclusions are available:

    c=psi_R(A0), D=chi_R(A0), f'=chi_m(A0)>0,
    psi_m(A0)=i*c², R*c divides m,
    2d*x+b<R<c, Delta<c, c>=2,
    |e_j|<c⁴ for every old85 boundary value e_j.

No positive restoration of T, R=3 mod4, X=2^R or full signed compiler
soundness is assumed.

## 2. Freeze the exterior values and form an integer polynomial in i

For this particular putative zero, fix its old85 integer values. Define

    g(z)=G(e85,z,(Delta*c²)z,(Delta*c²)²z²) in Z[z].

The coefficients of this auxiliary polynomial can vary from tuple to tuple;
the estimates below apply pointwise with uniform exponents determined by the
fixed G. The old85 source expressions contain no i, so this definition is
also literal substitution at the actual boundary, not a claim that source
obligations continue to hold when z is varied. At the actual positive
integer i, g(i) is exactly the substituted f.

For one degree-at-most-t monomial of G, let d_e denote its total exponent
in old85 arguments and d_i,d_S,d_Q its exponents in i,S,R16. Its coefficient
after substitution has absolute value bounded by its original coefficient
times

    c^(4*d_e+3*d_S+6*d_Q) <= c^(6t),

because |e_j|<c⁴ and Delta*c²<c³. The power of z is
d_i+d_S+2*d_Q; in particular deg g<=2t unless g vanishes identically.
Triangle inequalities remain valid after any coefficient cancellations, so

    ||g||_1 <= L*c^(6t).

This estimate does not require algebraic independence or positivity of the
old85 values, nor positivity of G.

## 3. A nonzero integer root polynomial bounds i

The normalized strong equation, unchanged by the simultaneous sign map, is

    g(i)²−Delta*c⁴*i²−1=0.

Define

    H(z)=g(z)²−Delta*c⁴*z²−1 in Z[z].

**H is not the zero polynomial.** If g is constant, including zero, its
z² coefficient is −Delta*c⁴. If deg g>=2, its leading square has degree
at least4 and cannot cancel. The only remaining case is g(z)=az+b with
a nonzero integer. Identical cancellation would require a²=Delta*c⁴.
But Delta=A0²−1 lies strictly between (A0−1)² and A0² for A0>=2, so it
is not an integer or rational square. Multiplication by the square c⁴
cannot change that. Thus H has a nonzero integer leading coefficient.

For a nonzero integer polynomial with leading coefficient h_n, the usual
Cauchy estimate gives any root z the bound

    |z|<=1+max_(j<n)|h_j/h_n|<=1+||H||_1.

For completeness, if r>1+max|h_j/h_n|, the sum of the lower terms divided
by |h_n| is at most M*(r^n−1)/(r−1)<r^n, so cancellation at modulus r is
impossible. The integer leading coefficient has absolute value at least1.

Submultiplicativity of coefficient norm and Delta<c now give

    i <= 1+||H||_1
      <= L²*c^(12t)+c⁵+2
      <= (L²+2)*c^b,       b=max(12t,5).

The last inequality uses c>=2, so c^b>=2. It is deliberately conservative.
It remains valid if specializing the old85 values lowers the degree of g
or cancels many coefficients.

## 4. Strong rank gives a conflicting lower bound

The Pell addition identities give

    psi_(R*c)(A0)=psi_R(A0)*psi_c(chi_R(A0))=c*psi_c(D).

Since m>=R*c and the psi sequence is increasing,

    i=psi_m(A0)/c² >= psi_c(D)/c.

The coefficient of sqrt(D²−1) in the positive binomial expansion of
(D+sqrt(D²−1))^c contains c*D^(c−1), with all other terms nonnegative.
Therefore psi_c(D)>=c*D^(c−1). The main norm and Delta>1 give D>c, hence

    i >= D^(c−1) > c^(c−1).

This holds for every strong completion. It uses the full R*c divisibility,
not merely c|m or a canonical choice m=R*c. As above, variable powers are
proof estimates, not source operations.

Put K=L²+2 and s=ceil(log2 K). If c>=b+1+s, then

    c^(c−1−b)>=c^s>=2^s>=K,

contradicting i>c^(c−1) and i<=K*c^b. Thus the extension has the
explicit strict cutoff

    2d*x+b_source < R < c < max(12t,5)+1+ceil(log2(L²+2)).

Here b_source is the compiler's `inner_bits`; it is distinct from the
temporary exponent bound b=max(12t,5). Equivalently one may write the input
bound as `odd_index<R` to avoid that notation overlap. This proves finiteness
of the entire ordinary-positive-input projection, including the zero sector
already excluded by the inherited source contraction.

## 5. Full source evidence and bounded corroboration

The [fresh helper](complete84_multiplier_dependent_root_absorption.py) reads
all nine predecessor files as inert bytes. It neither imports nor executes
any predecessor. It authenticates that the signed-domain theorem and the
previous root theorem refer to exactly the same actual84-row source. It
checks their explicit normalized rank and old85 exterior-bound statements,
then independently propagates dependencies through the source to obtain the
old64+21 and new66+22 interfaces. The receipt lists every included and
excluded computed name and every supplied argument.

All old85 sign/zero-root evidence is rederived from the source. Eight actual
exterior cuts expose the24 remaining output ancestors. Exact integer
polynomial expansion recovers all17 terms, the simultaneous f/T sign
identity and the four-term zero-f contraction. The result must agree with
the previous source-specific receipt; no finalizer or sign claim is accepted
merely as an unexamined formula.

A separate source pass checks c², Ac2, S, S², Delta*f² and the scaled strong
norm at their literal producers. It expands S and S² through the real c²
and Ac2 rows before recording the pointwise coefficient weights. Every one
of the88 arguments receives a coefficient-size weight and z-degree weight.
The additional i,S,S² weights are (0,1),(3,1),(6,2), respectively; each old85
argument has (4,0). These labels record the proved inequalities, not new
independent supplied coordinates or omitted arithmetic operations.

Finite symbolic corroboration verifies36 formal identities
psi_(rs)(A)=psi_r(A)*psi_s(chi_r(A)) for r,s=1..6, through index36;
120 instances of the leading odd-binomial bound; all495 four-class monomial
exponent patterns of total degree at most8; and108 (t,L) cutoff cases at two
integer endpoints each. The two endpoint checks include both the coefficient
norm upper bound and the strict-growth exclusion. The unrestricted results
rest on Sections2–4, not the finite ranges.

Nine small main/strong Pell components also check exact normalized strong
divisibility, the sharper i growth bound, and27 nonzero polynomial root
estimates. For each component, three affine g pass through the component's
actual (i,f). Their H polynomials are stored explicitly and checked to vanish
at i while satisfying the integer Cauchy estimate. These are auxiliary
arithmetic components. They are not full compiled positive zeros and do not
establish an accepting native history or a generic substitution compiler.

The standard-library helper rejects duplicate JSON keys and noninteger
number encodings, retains explicit checks under Python optimization, binds
its own bytes, creates receipts exclusively, and compares exact type-sensitive
canonical JSON on replay. Fresh normal and optimized replays from working
directory / passed:

```text
python3 /tmp/complete84_multiplier_dependent_root_absorption.py --root ABS_WIP --expect /tmp/complete84_multiplier_dependent_root_absorption.json
python3 -O /tmp/complete84_multiplier_dependent_root_absorption.py --root ABS_WIP --expect /tmp/complete84_multiplier_dependent_root_absorption.json
```

After installation, use the installed paths. `--output NEW_PATH` instead of
`--expect` authors a fresh receipt. No frozen replay is part of later review.

| Inert dependency | SHA-256 |
|---|---|
| complete84_scaled_strong_output.py | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| complete84_scaled_strong_output.json | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| complete84_scaled_strong_output.md | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |
| complete84_strong_root_absorption.py | `3d17fb1bdf7e3942bedcc873ee87a244ef66aa1188eaafb732828965ebfc670c` |
| complete84_strong_root_absorption.json | `424ba5aaa6e1ebc8525e4eaaaca7f7489282c7533d775dac86d10a659684986a` |
| complete84_strong_root_absorption.md | `b73fb50aebb8de23a282aff91c389d74b4bd96dadd355c43eb7e7783c1b6abc2` |
| complete84_signed_quotient_absorption.py | `cc5ed27ffcffefbd76b85ea36efa05637e06a0eb7fa221c6d9e31af9ea4f9d5f` |
| complete84_signed_quotient_absorption.json | `c9522c55adb3e602c2d355cb98d4e313c5e258a66e93bf0bbca52d56fddd9a00` |
| complete84_signed_quotient_absorption.md | `79800010986c07674fb681a93e02f624ee7bc6e5d39b99a1e77daf5021fa77c9` |

Helper SHA-256: `4fbb8595e4956f43829f91e42a57836bc726c3261bc5f9abf0b473d2493e80c4`.

Receipt SHA-256: `720c602d9d82d456fd50fb9b5c4f66132e6b4ca1222c9832694ddf0d9b92a46b`.

## 6. Remaining scope

G and its integer coefficients stay fixed while input and witnesses vary.
The interface covers exactly these88 source values with all dependencies
retained. Rational functions, variable-degree descriptions, arguments
depending on f,T,y, and altered strong equations are outside this theorem.
The bound is conservative and is not claimed optimal. It supplies neither
a new83 circuit nor a global arithmetic lower bound. The earlier85-value
result retains its stronger numerical cutoff on that smaller interface.
