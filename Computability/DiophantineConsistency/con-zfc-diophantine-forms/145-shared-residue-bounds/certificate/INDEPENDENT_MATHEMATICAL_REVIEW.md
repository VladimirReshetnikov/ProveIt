# Independent mathematical review of signed residue pooling

Reviewer scope: a separately assigned analysis of `PROOF.md`, the actual
aggregate source mutation, and the inherited `ORIENTATION_FIRST_PROOF.md`
and `STRICT_BUDGET_PROOF.md`. This is an internal AI-assisted review, not
outside peer review and not a proof-assistant verification of the full
unbounded theorem. The retained C222 calibration was reviewed separately
in `c222_internalization_audit.md`.

## Verdict

The new semantic reduction is valid relative to the identified inherited
signed-source theorem. It preserves existence of integer solutions over
the common semantic coordinates. The quadratic scaled merger is valid and
does not introduce a sign loophole. No circular dependency between deleted
remainder signs and power/factorial recovery was found.

## Checks of the new theorem

1. For integer a,b,c, `a^2+b^2+c(c+1)` is nonnegative. Conversely every
   nonnegative integer has this representation: apply the three-square
   theorem to `4n+1`; modulo four precisely one coordinate is odd, and
   dividing after writing the other two as even gives the displayed form.

2. The pooled certificate gives `2r_i^2<L^2`, so
   `|r_i|<L/sqrt(2)<3L/4`. A canonical residue in `[0,L/8)` is therefore
   less than L away. Congruence modulo positive L forces equality.
   This argument does not assume a sign for any supplied remainder.

3. The low-digit estimate follows from the binomial theorem and the finite
   geometric sum. It only bounds the canonical residue, so it can be used
   before the supplied residue has its arithmetic meaning.

4. Completeness has ample margin. The elementary converse works for up to
   **32** entries: strict bounds `c_i<L/8` give
   `2 sum c_i^2 < (m/32)L^2 <= L^2`. The final proof incorporates this
   strengthened bound; its concrete largest group has only seven entries.

5. The factor two is substantive for this proof. With a factor one,
   `L=9,c=1,r=-8` satisfies `r=c mod L`, `0<=c<L/8`, and
   `L^2-r^2-1=16=4^2`, but `r!=c`. This is a concrete false signed lift
   admitted by that weaker certificate.

## Dependency audit

The inherited orientation-first proof obtains all principal signed Pell
indices from its square frame and semantic anchor before interpreting any
remainder interval. In the strict-budget delta, the denominator request is
actually `q^x`, not the older `q^(x+1)`. Thus it gives x>=0 immediately.

The three retained scalar sign certificates give B>=1,q>=2. The canonical
t request and the raw ceiling give F>=1,B>F, hence B>=2. The two endpoint
rows then give

    x>=2+(t+1)y,  t>=16,  y=V(V-1)>F+2.

In particular x>=6. The numerator requests at the already positive base
q+1 force all actual representatives nonnegative. Only then is H0>=1 used
to interpret `(B H0)^x`. This establishes

    q=(B H0)^x >= B^6 >=16 B^2 >16V

before decoding a binomial or using F=t!.

The factorial binomial coefficients through t are bounded by V. One can
also verify that coefficient lemma directly by induction on t: for j<t,
Pascal's recurrence uses two terms bounded by `(F^2+1)^(t-1)`; for j=t,
the ratio `(F^2+t)/t` is at most `F^2+1`.

Only the `choose0` remainder is recovered next. Its own squared component
gives the required symmetric bound even though the other components have
not yet received canonical bounds. Therefore pooling the other residues
does not create a circular proof. The retained bound B<q then identifies
the exact binomial output, and the old factorial fixed-point theorem gives
F=t!.

The raw congruence `B | C0+F^2+1`, together with `B>F^2+1`, now gives C0>=1
and H0>=2. At this later stage the ordinary and derived-label coefficient
bounds in the proof are valid, including zero-valued representatives. The
inherited estimate `ell(t+1)<2F<x` supplies the required label margin.
Consequently all remaining signed residues are the canonical low residues.

Every deleted slack can now be restored as `s_i=L_i-r_i-1>=0`, and each
product `r_i*s_i` has the retained ternary nonnegativity representation.
All deleted rows are therefore genuinely recoverable; this is stronger
than merely deriving the final refutation semantics.

## Aggregate merger

For L=q^(t+1), the two remainders at modulus q^t are scaled by positive q.
Their canonical bounds scale to `[0,L/8)` and their congruences scale to
congruences modulo L. The existing wire Q2=q^2 and new wire

    S0=r0^2+r8^2

make `Q2*S0=(q*r0)^2+(q*r8)^2` exactly. Neither Q2 nor S0 is only an
inequality surrogate: both are defined by retained/new quadratic rows.
Thus the aggregate row is exactly the seven-entry norm certificate while
remaining quadratic in its wire variables. Positivity of q has already
been proved when dividing the bound back to modulus q^t.

Completeness extends any old solution by choosing S0 and by the ternary
representation of the nonnegative remaining budget. The number of such
auxiliary representations need not be unique, so the correct claim is
existential equivalence, not a bijection of full witness tuples.

## Logical and verification limits

Exact coefficient expansion, monic elimination and coordinate translations
are finite algebraic checks. The shared norm theorem and its staged
application require the unbounded argument above. The parent Pell,
factorial, CRT, Horn-flow and C222/ZFC calibration remain explicitly
imported mathematical results. This review does not replace those source
proofs, prove Con(ZFC), or establish a global minimum among Diophantine
equations.
