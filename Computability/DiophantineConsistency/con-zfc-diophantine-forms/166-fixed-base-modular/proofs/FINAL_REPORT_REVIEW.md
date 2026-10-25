# Independent proof review of the final report

Reviewed file: `report/report.tex`.
Scope: the ordinary soundness and completeness argument, including the
fixed-binomial weight, signed modular interface, two-square center theorem,
and inherited semantic interfaces. Generated report inputs were excluded
from this review. This is a separate review within the AI-assisted workflow,
not outside human refereeing or a new proof-assistant verification.

## Overall conclusion

The mathematical construction is sound with the explicitly retained
Pell/index, local-calculus, CRT, and logical calibrations. The two-square
center theorem has a valid proof, and the revised squared-H completeness
choice correctly enforces q=3 modulo 6. I found no counterexample to the
construction or new need for an arithmetic hypothesis. Five report-level
corrections or clarifications are listed below. The first two close genuine
expository gaps in the displayed proof. None requires a polynomial change.

The parent has already agreed to correct items 1--3. Items 4--5 have been
sent with exact suggested content.

## 1. Define and justify the common-norm slack form

The current report uses the macro `\G` in the common centered norm, then
claims its nonnegativity and ability to represent every nonnegative gap.
Its mathematical definition has disappeared when the free-center section
was changed to use two squares. Restore it before the common-norm
subsection:

```tex
For integers $a,b,c$, put
\[
 \G(a,b,c)=a^2+b^2+c(c+1).
\]
This form is nonnegative and represents every nonnegative integer $g$.
Indeed, the three-square theorem applies to $4g+1$, which is not of
the excluded form $4^r(8s+7)$. Its representation has exactly one
odd coordinate and two even coordinates, by reduction modulo four.
Writing them as $2c+1,2a,2b$ and dividing by four gives the claim.
```

This supplies both the soundness inequality and the completeness witness
used by the norm budget. The G witnesses are distinct from the two-square
witnesses in the free Pell center.

## 2. State the possible preauthentication base B=1 case

Before authenticating the binomial, the bootstrap gives positive odd B,
so B=1 is still possible. The general exact-power paragraph currently
states only the case |n|>=2, while the subsequent argument uses N=B^x
to deduce N divides q. Add the following explicit unit-base observation:

```tex
For $n=1$, the same Pell-unit evaluation is identically $1$ modulo
$T_1=2(A-1)$, for every signed index. Hence the exact request gives
$m\equiv1\pmod{T_1}$. The frame bounds $|m|<W$ and $A>W^W$
force $m=1$. In particular, if the not-yet-authenticated $B$ equals
one, then $N=1=B^x$ as well. Thus $N\mid q$ holds uniformly.
```

This follows directly from evaluating the norm-one Pell unit at the
residue 1, and uses neither digit semantics nor B's eventual large value.
There is no need to exclude B=1 prematurely.

## 3. Correct the factor-count sentence

In the large-evaluation argument, replace “the smaller factor count is
below t” with “the smaller factor count is at most t.” The case of t
conclusion factors and t+1 factors on the other side is possible before
the contradiction is derived.

For full detail, if the smaller count is d<=t, its product is at most
`((t+1)B)^d < B^(d+1)`, whereas the side with at least one extra
positive factor is at least `(B+1)^(d+1)>B^(d+1)`. The actual condition
`B>(t+1)^t` therefore suffices, including d=t and d=0. The subsequent
coefficient and distinct-root arguments are correct.

## 4. Describe the actual signed-J certificate recurrence

The report currently describes a binary-gate weighting rule. That rule
is valid in itself, but the supplied certificate uses a different, directly
checked sparse-gate recurrence. Replace the description with the actual
formula, avoiding a claim that the existing ledger implements another
recurrence:

```tex
For a sparse arithmetic gate
$g=\sum_m c_m\prod_{i\in m}v_i$, with
$|v_i|\le H^{e_i}$ and $H\ge2$, set
\[
 e(g)=\left\lceil\log_2\sum_m|c_m|\right\rceil
       +\max_m\sum_{i\in m}e_i.
\]
The triangle inequality proves $|g|\le H^{e(g)}$.
The independent ledger checks all 91 ancestor gates of the actual
derived-label wire. It gives exponent $3\,649\,856$ for its stored
$J-1$ coordinate and $3\,649\,857<2^{22}$ for $J$.
```

The four signed seed coordinates satisfy `|a_i-1|<=H` because
`H>=2+a_i^2`. Thus this verifies the intended bound for arbitrary signed
global representatives, including zero and negative values.

## 5. Make the local derived-label bound explicit

The row-decoding paragraph says the derived label is treated with the
same local bound as the rule polynomial. This is correct but should be
justified separately from the global H bound, since H depends on the
large CRT representatives. A sufficient insertion is:

```tex
For the decoded syntax parameters in $[0,t]$, apply the same
constructor ledger with seed bound $t+1$. The constructors are
nonnegative on these local values, so
\[
 0\le J(\text{local})\le(t+1)^\ell
    <(2+t+x+y+B)^E<2^x\le p^{xe}.
\]
Its range residue is also in this interval; the congruence therefore
identifies the actual derived-label value and bounds it by $t$.
```

This directly validates the local label cap. It does not rely on the
enormous signed-global estimate H^ell being below the selector modulus.

## Detailed points checked and accepted

### Fixed-base selector and label-weight arguments

The bound `lcm(1,...,n)<=4^(n-1)` is valid. The central-binomial
divisibility argument works for even and odd n and has the correct
base case. Consequently R=16^t exceeds the required lcm square.

For each row, R+i>Lambda_t^2 guarantees a prime with valuation
v>2 floor(log_p t). The formula e=v-delta and the elementary
bound 0<=delta<=floor(log_p t) give a full selector p^e>t dividing
R+i. The converse prime-compatibility argument correctly accounts for
every prime factor of B, including primes not selected to prove a
particular row's soundness. This is the necessary completeness condition.

Every factor `(R+i)/i` exceeds t+1, proving B>(t+1)^t. The 2-adic
valuation cancellation proves B odd without assuming factoriality. Once
the factor-count sentence is corrected, the weight-product identity
forces polynomial equality and the correct multiplicity balance. The
Horn closure counting argument remains valid for cycles and repeated
premises.

### Bootstrap, frame, and signed modular digits

The order of sign recovery is acyclic. The fixed-base power gives R>1;
odd B gives B!=0; q=6z+3 gives |q|>=3; its exact y+1 request gives
y>=-1; the nonzero R-multiple y then gives y>0 and B>0. Squared H is
positive independently of signed representatives, and its exact BH
request makes x>=0 and q>0. The progression excludes x=0. The endpoints
then give x>=B+1>=2 and x>=2+(t+1)y. These estimates imply all the
later growth budgets before B has been authenticated.

The compressed square frame still gives W>=258. Its retained t and R+t
atoms bound R; its other removed affine atoms have direct bounds from
t and q. The successor output no longer needs an exact-power bound.
All fourteen principal nominal indices remain bounded for the anchor
and pooled orientation argument. Freeing A changes neither their
norms nor their congruence pool.

The common-root equation itself makes q+1 a unit modulo Omega, so the
signed Pell evaluation theorem is correct without an additional coprimality
premise. After bootstrap, the already proved N|q gives all required
divisor relations among the common modulus and digit moduli. Formal
negative-index binomial truncation is finite modulo the relevant powers;
no analytic convergence is being used.

The direct signed range-lemma proof by counting multiples in an integer
interval works for intervals entirely below zero as well as positive
intervals. Intervals containing zero are treated separately. The claimed
one-sided implication is valid, and the false converse is not used.

The coefficient bounds give C^2<=q uniformly, including the j=0
coefficient at a zero upper argument. The common centered norm therefore
recovers every signed low sum uniquely. The equality B=binom(R+t,t)
then follows from both positive values being below q/2. No positivity
of the global CRT representatives is imported from the removed exact
numerator powers.

### Two-square center theorem

The finite quadratic ring proof is valid, including primes dividing
the Pell discriminant. Raising the frame unit to the odd part of its
order gives a 2-primary unit. If its abscissa reduces to +/-1 modulo
an odd p, its ordinate vanishes modulo p: the norm proves this in the
nonramified case, and the square-zero nilpotent calculation proves it
in the ramified case. The congruence kernel is a p-group, so this
2-primary unit lifts exactly as +/-1 modulo p^a.

The required center difference is consequently either a unit or a
residue with even valuation. Each such residue is a sum of two squares
modulo every odd prime power, with a valid nonsingular lift for the unit
case. Separate CRT on both coordinates gives the desired center class.
An unrestricted lift of one coordinate makes A arbitrarily large.

The odd multiplier preserves Y_(Wk)(W+1)/W odd, exactly as the literal
lower frame requires. The fixed-frame counterexample W=4,q=3,Omega=9
is numerically correct: L=4801 and A0-L^2=3 modulo 9, which is not a
sum of two squares modulo 9. Thus the report correctly explains why
the frame choice, and not just a free-center assertion, is essential.

### Completeness and inherited dependencies

The beta construction supplies the necessary even multiple of t! while
retaining an odd square multiplier. Its moduli are pairwise coprime and
odd, so an arbitrarily large even beta code is available. The amplified
CRT uses every prime of B; its exponent 2xe leaves more than the required
xe after the factorial loss, since k<=x. All source polynomial
congruences survive the later representative lifts.

For squared H, two representatives outside the four schema inputs may
independently have square 0 or 1 modulo 3 while preserving even parity.
Their sum attains every residue modulo 3. Thus H is both odd and, when
needed, divisible by three. The selected a class may then be lifted in
an interval of length 6N^2 while retaining all congruences. Its lower
bound supplies the even dominant J, and its upper bound is compatible
with the cap estimate. Therefore q=6z+3 has a canonical witness.

The final center is chosen only after the semantic coordinates and frame
are fixed. The retained cap completion works at an arbitrary sufficiently
large positive A with the selected even dominant anchor. The new
two-square theorem provides exactly such centers, so the composition has
no hidden dependency cycle. The norm's completeness gap is nonnegative
by the eleven-remainder 1/32 estimate and is supplied by G.

The report appropriately distinguishes the retained C222/ZF/ZFC logical
interfaces from the new arithmetic proof and finite polynomial audits.
It does not claim an end-to-end formalization or a new proof of
consistency. These evidence boundaries should be preserved.
