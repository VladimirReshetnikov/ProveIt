# Independent review of the input-free-height obstruction

**PASS.** All four one-addition deletions admit full positive witness zeros at
infinitely many false raw-input/clean-time pairs. This is the specific
counterexample theorem in [the author proof](three_mass_input_free_height_obstruction.md),
not a claim that every input/time pair is accepted or that the sound parent
can be reduced by one gate.

The [independent helper](review_three_mass_input_free_height_obstruction.py)
and [receipt](review_three_mass_input_free_height_obstruction.json) authenticate
the frozen author source, receipt and proof plus every declared dependency.
No author, predecessor or archived Python is imported or executed. The
independent check reconstructs all four complete candidate arrays from the
actual saved parent, deleting exactly the private height addition and changing
its sole consumer. All interfaces, coordinates, comparison pairs and other
body rows remain literal.

The complete paid sources have 596/471/469/472 gates, including all nineteen
residual subtractions, nineteen squares and eighteen summations. Every gate
and supplied coordinate is output-live. The independent degree line maps
coordinate i to (i+11)z modulo 1,000,033, and obtains output coefficients
891573/11964/11964/11964 at the unchanged formal bounds
2344/1192/1192/1192. These nonzero integer-polynomial coefficients prove exact
degrees. They differ from the author's line and modulus; no primality claim
is needed for this nonvanishing implication.

## Complete parent lift and arbitrary-iterate symmetry

The parent-to-candidate substitution is

    eta_candidate = eta_parent + (5x+1).

After this substitution, the helper constructs every complete expression DAG
using exact shared expression interning. All 2,008 retained gate expressions,
including all full-finalizer expressions, equal their parent counterparts.
This verifies the all-value whole-polynomial identity. On the declared
natural x and positive witness domain the substitution is positive.

For the symmetry proof, the independent checker extracts the actual transport
and clock endpoints from their comparison rows. Recursive expansion at the
unchanged radix, scale, current/next history words and packed clock verifies
exactly

    B*next + 5x+1 - current - P*(5F+halt-5),
    2*Ctau + 192*(x+F)+208 - (B-1)*(clock_hat-1) - U.

It separately proves that every native register and the other seventeen
comparison cones are independent of x,F,clock_hat after the height deletion.
In a polynomial ring with an independent indeterminate r, it substitutes

    x -> x+rP(B-1), F -> F+r(B-1),
    clock_hat -> clock_hat+192r(P+1).

Both complete endpoint residual polynomials are identical coefficientwise.
Thus all 76 residual instances across the four sources are invariant for
arbitrary scalar r, and the independently reconstructed complete SOS is
invariant too. No native equality or inequality is imposed to prove these
identities. The result is stronger than checking only a numeric step or
an invariant zero set.

Thirty-two full signed parent lifts and thirty-two full signed shears,
including twelve rational cases of each, supplement those exact proofs.
All nineteen residuals and the entire evaluated polynomial are checked in
every case. These off-zero calculations are not represented as full positive
native witnesses.

## Why the identities give actual false-clock zeros

The proof first takes a genuine accepted parent history at its true clean
time, at a sufficiently large permitted dyadic height. Parent completeness
supplies the positive native witnesses; the verified positive lift preserves
all their equations. Only then is the polynomial symmetry applied. It leaves
the height, radix, packed history and native witnesses fixed, while positive
integer r increases all three changed coordinates. There is no application
of parent soundness to a shifted tuple with an unverified input bound.

At the genuine seed, P=B^t>1. Since B=2^18*h^2 with dyadic h, B is1 modulo3.
The shifted raw payload therefore preserves the zero3/positive3 acceptance
guards; both other fixtures accept every raw input. Direct instruction clocks
give first clean times 1584(x+1)+48 for inc2;dec2 and 768(x+1)+32 for the
other three. These times strictly increase with x, while the candidate keeps
U fixed. Its shifted claimed F also differs from the actual final payload
x'+1. The full positive counterfamilies follow from the identities and parent
existence theorem; no giant native Pell tuple needs to be materialized.

The NOP seed at x=0,U=800,h=1024 has B=P=2^38. Its first shifted parameter is
75557863725639445512192, whose true clean time is
58028439341291094153364256. This is a concrete outer example of the parametric
argument. The author checks its full outer equations and prescribed AND;
native placeholder values in that numerical fixture are explicitly not a
full polynomial zero. The other seeds have the same distinction.

The original height contribution cannot be deleted merely because a genuine
clock dominates an input size: establishing a genuine chronology already
requires the low-digit bound that was deleted. The explicit symmetry shows
failure of the representation, rather than just a gap in that reasoning.

## Review and replay scope

Root read the entire author source, proof and Report18 intake. A separate
mathematical reviewer checked the parent lift, domain, guard preservation,
clock formulas and false-time conclusion, and cross-read this helper.
The [Report18 intake](review_cellular_clock_domination18_intake.md) separately
checks its source-specific CA-clock theorem and 166 saved primitive records.
This independent source audit does not reconstruct the report's full literal
table or simulate its CA. Report18's clock is not substituted into the
three-mass source, and its theorem is not needed for the false-zero proof.

From any directory:

    python3 /path/review_three_mass_input_free_height_obstruction.py \
      --repo /path/Proofs \
      --expect /path/review_three_mass_input_free_height_obstruction.json

Before installation, add `--author-root /tmp`. Writer and fresh normal and
optimized exact receipt replays from `/` passed. All assertions use explicit
exceptions, and the saved comparison preserves exact JSON types. There is no
maintained public compiler API, improved universal bound, unrestricted lower
bound, ordinary-input loader or real/rational zero-exactness theorem here.
