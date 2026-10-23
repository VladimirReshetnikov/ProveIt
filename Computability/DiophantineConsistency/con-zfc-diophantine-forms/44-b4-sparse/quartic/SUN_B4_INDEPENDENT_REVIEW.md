# Independent review of the Sun B4 source replacement

## Conclusion and scope

The new source-encoding argument in `sun/SUN_B4_PROOF.tex` is sound on
independent mathematical inspection. The four-sum certificate and the
signed-coefficient carry construction preserve the required source
existence interface. No unproved q-divisibility shortcut from the parent
quartic investigation is used. The source quartic and its coherent mixed
compiler tuple are unchanged.

This review checks the new arithmetic interface and the displayed local
finalizer argument. It does not independently reprove Sun's imported
positive/reverse Lucas bridges, the full residue interpolation theorem,
or the K215 calibration. Those remain named mathematical dependencies.

## Checks of the universal argument

1. The 31 positive weights, with zero padding, distinguish all 52,360
   multisets of four elements. Thus they distinguish all witness monomials
   of total degree at most four. The relevant property is integer-sum
   injectivity; it does not depend on assuming the finite-field construction
   correct. The independent checker enumerates these sums directly.

2. For the signed coefficient polynomial D, the term at exponent 4t has
   coefficient 24P(0)>=24. Every other exponent is strictly smaller and
   distinct. The geometric-series estimate for their absolute sum proves
   D>0 before any witness digits have been decoded. Its upper bound by
   24H0 times the geometric sum is also valid with negative coefficients.

3. The actual coefficient bound implies beta_S>48*33^4*H0, and beta_S has
   even exponent. With c=32b and B=beta_S*b^4, this supplies the strict
   coefficient margin 48H0*c^4<=B-2, not just a bound that holds at already
   decoded witnesses. Hence every integer 0<=g<2bB^t satisfies the stated
   Jc, Sc and Tc bounds. The new t does not appear in this margin.

4. The base-B mask has digit B-b at each coded position and B-1 elsewhere.
   It therefore tests the entire intended digit shape when b is a power
   of two. The zero position is deliberately not a witness coordinate.
   For decoded digits, multinomial extraction gives exactly 24P(n), not
   P(n) or a nonuniform weighted sum. Adding B/2 to every signed coefficient
   places every digit strictly between zero and B. Dividing both carry
   operands by two is legitimate for the overlap test and detects exactly
   whether the distinguished digit is B/2.

5. For N=2^r, expansion gives

       X=(S+T)N^2+(N-1-S)N+(N-1-T).

   Although S+T can exceed N-1, this is harmless: it is the leading block
   and may occupy arbitrarily many bits. The two lower blocks are within
   range. Thus popcount(X)=2r-popcount(S)-popcount(T)+popcount(S+T), which
   proves the exact central-binomial divisibility criterion. The lower
   carry-free bounds are established before this formula is applied.

6. beta_S and b are 1 modulo 3; N=4B^(9t+2) is 1 modulo 3. Therefore
   3 divides X. Positivity gives X>=N^2-1>3b and Y=N^2>max(b,256). These
   are valid on the whole source branch, not only at genuine encodings.
   Completeness can choose arbitrarily large square powers of two b, so
   f=(b-1)/3 is a positive integer and the base-cofinality is preserved.

7. The displayed three-radical finalizer has sign-safe separation: writing
   A=|a0|>1 and M=Pn^2+K^2+2, one has |v1|=A>sqrt(A) and
   |v2|=A(M+1)>sqrt(A)+A sqrt(|a1|). The largest changed radical therefore
   cannot cancel under a field automorphism, including complex branches.
   The zero-Sigma case is excluded by the nonvanishing homogeneous quintic.
   The prime-valuation argument from S^5|Theta to S|T is correct even at
   the prime 23. Finally, b and its bracket are coprime; b=1 modulo 3
   excludes the negative-square branch and yields the stated positivity.

## Metadata corrections requested during review

The generator reused the name `weights` for three norm-weight node IDs and
then emitted it as `witness_positions`. The exponent-position list must be
preserved separately. Also, the old immutable `sources/data/INSTANCE.json`
still carries baseline values t=5^31 and Lcode=5^32. It is legitimate
provenance for the fixed coefficient payloads, but an active B4 instance
manifest must supply the new coding parameters and current equation path.
These issues do not change the arithmetic circuit, but are important for
an unambiguous repository artifact. Both fixes have now landed: the emitted
list has 31 positions with maximum 610895, and the circuit points to the
new active `../INSTANCE.json`; its proof path is `../SUN_B4_PROOF.tex`.

The abstract should say that the source replacement preserves existence
through the source interface, not that it preserves the literal integer
zero set: the encoded g changes with the exponent positions.

## Independent controls

`check_sun_b4_independent.py` imports neither the new nor the old generator
or verifier. Its exact checks comprise all 52,360 four-sums, 21,844 binary
packing pairs, and 762 arbitrary/decoded source assignments for the signed
coefficient polynomial (x-1)^2+(y-2)^2. The last example includes genuine
zeros and nonzeros, mixed coefficient signs, and pre-decoding arbitrary-g
bounds. The controls pass. They supplement the universal arguments above;
they are not claims to decide consistency or evaluate the astronomical
full polynomial on an actual accepting computation.
