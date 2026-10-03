# Independent review of the free-coefficient83 scout

**PASS, with no requested author change.** The [frozen author](complete83_free_coefficient_scout.md) emits the claimed complete 83=46M+37A arithmetic circuit, with 18 positive witnesses and exact degree 111. Its asserted failure of the literal integer inverse is valid on full positive witness fibers. Neither the author nor this review establishes an 83-operation universal representation or a false accepted ordinary input.

The [independent checker](review_complete83_free_coefficient_scout.py) and [receipt](review_complete83_free_coefficient_scout.json) read authenticated JSON and proof bytes. They import or execute no author, predecessor, archive or historical Python. This review reads the entire frozen author source and note, the immediate [84 proof](complete84_scaled_strong_output.md), the relevant [85 positive-zero proof](review_complete85_auxiliary_bezout_math.md), and the odd-index polynomial identities in the [half-parameter proof](../../1980/HALF_PARAMETER_PELL_92_PROOF.md#3-an-odd-index-polynomial-identity). Ten explicit author/dependency files are pinned. No repository or frozen predecessor file is changed.

## Literal source, paid interface and both whole-output maps

The reviewer reconstructs the candidate by removing exactly this one row from the actual saved 84 source:

    aux_coefficient_root = i*Ac2.

It replaces the supplied witness i by the removed row's name S=`aux_coefficient_root`. All other 83 instructions remain byte-for-byte equal as JSON rows. The ordinary input x, six fixed compiler numeral ports, their inherited interpretation, the remaining 17 witnesses and the complete finalizer are retained. The actual old consumer list is

| Coordinate/register | All consumers |
|---|---|
| i | aux_coefficient_root |
| f | L16, auxiliary_Tf |
| auxiliary_quotient | auxiliary_Tf |
| y_aux | aux_y2 |
| Ac2 | norm_main, aux_coefficient_root |

Consequently Ac2 remains paid and live in the main norm. All 83 instructions and all 25 free ports are live at the final output. The independently counted core is 76=40M+36A; its seven finalizer gates cost 6M+1A. The source still has 18 positive witnesses. There is no new equation or paid test enforcing divisibility of S.

The forward substitution S=i*Ac2 gives 83 exact retained-register identities, hence the complete identity F83(S=i*Ac2)=F84 over every commutative ring. A separate rational expression-DAG execution substitutes i=S/Ac2 and checks all 83 retained registers in the reverse direction. Thus F84(i=S/Ac2)=F83 whenever Ac2 is nonzero. These checks include the entire final output; they are not evaluations at a zero or identities only between the auxiliary factors.

Write Delta for source register `A`, c for `R10a`, T for `auxiliary_quotient`, and R for `r_lhs`. Source positivity gives Ac2=Delta*c²>0 before any equation on valid positive tuples. The inverse is therefore positive rational, but need not be integral. Ordinary-input completeness follows from the unconditional positive forward substitution; soundness cannot be inferred by rational restoration.

Source dependency propagation separately proves that replacing f,T,y_aux,S can change only the auxiliary and scaled strong factors. The first, main, input, index and transport factors have unchanged complete expressions. This is essential to the full-zero constructions below.

The actual finalizer is independently expanded at its seven factor ports and Delta. It is exactly their product minus Delta, with six product multiplications and the last subtraction paid. No argument here infers unit factors merely from a generic candidate product equaling Delta.

## Independent exact-degree certificate

All witnesses and x have degree 1; the six fixed numeral ports have degree 0. The checker expands each entire factor into a sparse integer polynomial while retaining those numeral symbols. It uses no author-provided cancellation cut or zero-only equation. The resulting sizes and exact weighted degrees are

| Factor | Collected monomials | Degree |
|---|---:|---:|
| First norm |70|22|
| Main norm |518|18|
| Input norm |1,175|32|
| Auxiliary norm |281|16|
| Index |19|7|
| Transport |16|2|
| Scaled strong norm |35|14|

These are 2,114 complete factor monomials. The checker multiplies their leading forms and obtains the full 72-monomial leader

    -32 Q^63 h (rho+sigma) delta² (eta+zeta)^5 w^12 s^17
        * S² * Nt_top * T² * f⁴,

where

    Q=Bm1*Jrep,
    C1=Q-F-Z-alpha-twice_cell_bits*x,
    Nt_top=w*C1-transport_quotient*Q.

The monomial

    Jrep^64*h*rho*delta²*eta^5*w^12*s^17*S²
        *transport_quotient*T²*f⁴

has coefficient 32*Bm1^64. This is nonzero on every inherited valid fixed-program slice because Bm1>0. Thus specializing the other fixed compiler numerals cannot erase the leader. The seven factor degrees sum to 111; the final subtraction of degree-12 Delta cannot cancel it. Exact degree 111 is a formal all-value polynomial result, independent of unresolved soundness. The separate naive gate recurrence gives upper bound 121.

The whole product polynomial is not densely expanded into all of its lower-degree monomials. Its actual complete finalizer, each complete factor polynomial and the entire leading product are checked separately; together they prove the stated full degree. Numerical assignments are unnecessary for this uniform attainment argument.

## Full positive-zero extensions: both cases are sound

Take any actual full positive parent zero on a valid fixed-program slice. The established 84-to-85 equivalence and native theorem give

    A=a+2, Delta=A²-1,
    p=R odd, p>=25,
    D=chi_A(p), c=psi_A(p), D²-Delta*c²=1.

Here A is the Pell parameter, not source register `A`. In particular c>1 is odd and gcd(c,D)=1. Oddness of c follows from the recurrence modulo 2 for every integer A; the construction does not need A even. The five factors outside the auxiliary/strong cone are already 1, and remain so by the complete consumer check above. Invoking the parent theorem at this point is legitimate: the starting tuple really is a parent zero. No candidate soundness is assumed.

For any positive odd ell=2v+1, the integer polynomial Q_v satisfies

    chi_S(ell)/S=Q_v(S²),
    Q_v(0)=(-1)^v*ell,
    Q_v(1-A²)=(-1)^v*psi_A(ell).

These identities follow from the two displayed recurrences in the pinned half-parameter proof. They use polynomial divisibility before modular reduction, not division by a possibly nonunit residue.

Choose f=chi_A(m), b=psi_A(m), S=Delta*b and put

    V=chi_S(ell)/S, y=psi_S(ell).

Then V,y are positive integers, Delta*f²-S²=Delta and S²*V²-(S²-1)y²=1. It remains to choose ell so that

    V=-c (mod f), V=-p (mod c), f²=1 (mod c).

Because gcd(c,f)=1, these congruences make

    T=(V+c+p*f²)/(c*f)

a strictly positive integer. They prove the literal source identity V=c*(Tf-1)-p*f². The definition of T is an existence proof for a supplied witness; it is not an uncharged circuit division.

For **p=3 modulo 4**, take m=ell=p. Thus f=D and S=Delta*c. Since v is odd, the two Q_v reductions give V=-c modulo f and V=-p modulo c. The main norm supplies f²=1 modulo c and coprimality. The inverse is i=S/(Delta*c²)=1/c, nonintegral.

For **p=1 modulo 4**, take m=2p, so f=chi_A(2p), b=2D*c and S=2Delta*D*c. Choose a positive ell satisfying

    ell=p (mod c), ell=3p (mod 8p).

Since c is odd, gcd(c,8p)=gcd(c,p) divides p, hence divides the residue difference 2p. The CRT conditions are compatible and force ell=3 modulo 4. Reduction modulo c again gives V=-p. In the quadratic ring modulo f, the Pell pair at 4p is (-1,0), and that at 8p is (1,0). Thus psi_A(ell)=psi_A(3p) modulo f. The exact identity psi_A(3p)=(2f+1)c gives psi_A(ell)=c modulo f; the negative Q_v sign gives V=-c. Coprimality and f²=1 modulo c follow from the doubled main Pell equation. Here the inverse is 2D/c, nonintegral because c is odd, greater than 1 and coprime to D.

In either case the new scaled strong factor is exactly Delta and the new auxiliary factor is exactly 1. The other five factors stay 1, so the **complete** 83 output vanishes. All supplied coordinates are positive. The construction alters only f,T,y,S and preserves the ordinary input and the remaining supplied data. It works for every actual full positive parent zero, not only a chosen canonical parent Pell fiber.

The resulting candidate tuple cannot lie in the image of the literal integer forward substitution, since that map would uniquely require the nonintegral i above. This proves strictly larger full witness fibers over every nonempty parent input fiber. It does not show a newly accepted input, disprove an alternative existential normalization, or establish universal83. The author's warning about divisor/sign cases in a generic product=Delta equation is correct.

## Bounded independent executable evidence

Beyond the symbolic proofs, the receipt records 36 complete forward evaluations, including 18 rational assignments, and 30 complete rational inverse evaluations: 5,478 retained-register comparisons. These are algebra diagnostics, not halting witnesses.

The independent Pell implementation uses a 2-by-2 matrix recurrence. For large auxiliary indices it obtains V modulo m by computing chi_S(ell) modulo S*m and dividing the resulting integer remainder by S. This independently checks the required quotient residue without copying the author's Q_v modular recurrence. The CRT indices are found by a short residue search rather than the author's modular-inverse formula.

Twelve cases cover both parity branches, even and odd A, and indices including p=27 and p=29. Four cases materialize complete positive main/auxiliary/strong subsystems: (A,p)=(2,3),(3,7),(2,5),(6,27). The p=5 case has ell=2,095 and a 41,445-bit V; its recovered T is integral and positive. The remaining eight cases check exact modular congruences without constructing their enormous auxiliary coordinates. The checker also verifies 21 full polynomial identities Q_v(1-A²)=(-1)^v*psi_A(2v+1) and 41 exact Q_v(0) values. These finite checks supplement the general recurrence proof; none is described as a full compiled positive zero.

The full-source theorem is the parametric extension from actual parent zeros proved above. No enormous complete compiler tuple is materialized by this review.

Run from any working directory after installation:

    python3 review_complete83_free_coefficient_scout.py --root ABS_WIP --expect ABS_RECEIPT

During staging, add `--author-root /tmp` to read the frozen new author trio there while all parent/proof pins resolve under ABS_WIP. `--output PATH` writes the deterministic receipt. Explicit exceptions remain active under optimized Python; receipt comparison is recursively type-exact. Fresh normal and `python3 -O` exact replays from `/` pass.
