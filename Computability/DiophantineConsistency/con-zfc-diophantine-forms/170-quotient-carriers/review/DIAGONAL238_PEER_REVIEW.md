# Independent arithmetic review of the diagonal-growth construction

Reviewer: the alternative-formalism research branch, 25 October 2026.
Reviewed source: `agent_audit/new_construction/PROOF.md`, its literal
`build.py` changes, the emitted `diagonal_raw/raw_source.json`, and the
retained factorial-free selector, semantic-anchor and range proofs.

## Conclusion and scope

The changed arithmetic argument is valid. I found no circular use of a
front sign, factorial authenticity, parity, or the binomial interpretation.
The proof establishes the stated ordinary existence equivalence, subject
to the explicitly inherited C222/logical calibration and exact finite
compiler. This is an independent mathematical review, not a claim that the
transitive Lean development has been rebuilt. Final emitted-coefficient
replay belongs to the construction's separate finite checker.

## Points checked independently

1. **The evaluation base really may be `F=t^t`.** If the two products of
   positive factors `1+jF` have different numbers of nonunit factors, the
   smaller count `d` is at most `t`; the larger-count product is at least
   `(F+1)^(d+1)`, whereas the smaller is at most
   `t^d(F+1)^d`. Since `F+1>t^d`, they cannot be equal. Once both counts
   equal `m<=t`, every coefficient in each product through degree `m` is
   positive and at most `binom(t,k)t^k<=t^t=F`. Although equality with `F`
   can occur, the difference of the two positive coefficients has absolute
   value strictly below `F`. The lowest nonzero coefficient modulo `F`
   therefore proves equality as polynomials, and unique factorization
   recovers all nonzero label multiplicities. No individual coefficient
   needs the false strict upper bound `<F`.

2. **The new shift `R=F` satisfies the actual selector theorem.** For even
   `t`, `pi(t)<=t/2`, so the product of maximal prime powers at most `t`
   gives `lcm(1,...,t)^2<=t^(2*pi(t))<=t^t`. If
   `v_p(R+i)>2 floor(log_p t)`, the complete valuation of `B=binom(R+t,t)`
   is
   `v_p(R+i)-v_p(t*binom(t-1,i-1))`. The subtracted valuation is between
   zero and `floor(log_p t)`: each Legendre summand is zero or one, since
   `t=(i-1)+(t-i)+1`. Thus a full factor `p^e` of `B` divides `R+i` and
   exceeds `t`. Conversely the interval-carry expression for `v_p(B)`
   shows that every full `p^e` in `B` divides some `R+i`. Both directions
   needed by the retained CRT proof are present.

3. **Signed recovery has an acyclic dependency order.** The positive power
   at base and exponent `t` first gives `F=t^t`. The literal class
   `q=6z+3` gives `|q|>=3` and `|q+1|>=2` before either sign is known.
   Thus the old signed-power lemma gives nonnegative representatives,
   `x>=0`, and `y+1>=0`. The row `y=F(2v+1)` now forces `y>=F`.
   The index congruence gives `B!=0`; hence `|BH|>=3` and the self-power
   gives `x>=1`. The two beta endpoints then yield
   `x>=F+1` and `x>=2+(t+1)y`. No interpretation of `N=B^x` is needed
   while `B` could still be a negative unit.

4. **Negative radices are handled, not silently excluded.** For
   `Q=|q|` and `b=|B|`, the authenticated self-power gives
   `Q=(bH)^x>=2^x` and `Q>=9b^2`. All four denominator exponents
   `t,t+1,y+1,x` lie in `[0,x]`. The common remainder norm yields a
   symmetric interval of radius `|L|/2` for each signed denominator `L`.
   The actual binomial expansion at negative `q` has the same absolute
   tail bound as at positive `q`. Its low remainder is less than `Q^t/32`
   in absolute value. Therefore centered uniqueness gives the exact digit,
   and `|B|<=Q/9`, `binom(F+t,t)<Q/32` turn its congruence into equality.
   Only at this point does `B>0`, and hence `q>0`, follow.

5. **All inherited size budgets remain valid.** The general coefficient
   bound `binom(F+t,j)<=(F+1)^t` and
   `F+1<=2^(F-1)` give the claimed first-digit margin. The endpoint gives
   `2+t+x+y+F<2x`, while `x>=2^64+1`, well beyond the retained threshold
   `2^32` for `(2x)^(2^23)<2^x`. It also gives
   `2^22(t+1)<x`. The new `H=3+6 sum(a_i)` dominates the old
   `2+sum(a_i)` and its input-plus-one bounds, so the remaining range and
   derived-label margins are stronger. After recovering `B`, one also has
   `B>F+1`; the index row excludes `C0=0`, as in the old proof.

6. **The boundary `y=F` is disposed of at the right stage.** Local rows and
   bounded beta residues can first be extracted with `y>=F`. If `y=F`,
   the first residue is zero and the final residue is one. Positive label
   factors make every accumulator update propagate zero forward, a
   contradiction. Therefore the initial residue is actually `F+1`, and
   the positive product identity used in item 1 is legitimate.

7. **Completeness retains all parity freedoms.** Choose an even cofinal
   horizon `t=16+2h^2`. Its diagonal value satisfies
   `v_2(F)=t*v_2(t)>v_2(t!)`. If `O` is the odd part of `t!`, then
   `y=F*O*(2m+1)` satisfies the new linear odd-multiplier row, is divisible
   by `t!`, and can exceed every finite pending product. Its beta moduli
   are pairwise coprime and odd. Moreover, for `i<=t`,
   `v_2(F+i)=v_2(i)`, so `B` and `N^2` are odd. The same precision-`N^2`
   lifts therefore set the semantic-anchor parity and dominance. Finally
   `H` is automatically odd and divisible by three, and `x>=1`, so
   `(BH)^x` is exactly `3 mod 6`; its affine `z` is integral. No evenness
   constraint on `x` is needed.

8. **The literal source edits cover the frame.** The producer changes the
   power base to `t`, changes the horizon to `16+2h^2`, changes both radix
   rows, replaces the beta square multiplier by the stated linear row,
   deletes the private multiplier equation, and substitutes the old
   binomial-shift coordinate by `F` in every residual. Inspection of the
   emitted square frame and pooled-index row confirms that the shift and
   `F+t` occurrences are changed there too. Formerly distinct frame atoms
   may become identical and their square coefficients add; retaining both
   copies only strengthens the bounds. The growth-base atom is still
   explicitly framed. No private metadata is used as an unverified
   semantic equality.

The sole expository suggestion was to state `C0>=1` explicitly after
`B=binom(F+t,t)>F+1`. It is an immediate consequence of the retained index
row and does not require a further constraint or source change.
