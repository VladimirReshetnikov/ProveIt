# Represented divisors when the Pell parameter is even

## Pure arithmetic theorem

Let A>=2 be even, Delta=A²-1, and let x,y be integers. If the nonzero integer N=x²-Delta y² divides Delta, then exactly one of these forms holds:

- N is a positive square
- N<0 and Delta/|N| is a square

This is a complete classification of possible *norm values*, not a claim that every listed divisor is represented by a solution satisfying the full source constraints.

Proof. Write Delta=d m² with d squarefree. Since Delta=3 mod4, both d,m are odd and d=3 mod4. Let |N|=r z², r squarefree. The divisibilities N|Delta and N|x² imply z|m and z|x. Set X=x/z and Y=my/z. Then

  X²-dY²=epsilon r, epsilon=sign(N).

A prime dividing r must divide X. If it did not divide d, it would also divide Y, contradicting squarefreeness of the right-hand side. Therefore r|d, and r|X. Consequently

  U=(X²+dY²)/r, W=2XY/r

are integers satisfying U²-dW²=1, and U is odd. We may take x,y nonnegative without changing N.

Let alpha+beta sqrt(d) be the fundamental positive integer Pell unit. The existing unit A+m sqrt(d) has even first coordinate, so alpha must be even: an odd alpha forces beta even modulo2, hence every power has odd first coordinate. With alpha even, beta is odd and first-coordinate parity alternates with exponent. Therefore the odd U occurs at an even exponent, say U=chi_alpha(2h).

If epsilon=+1, then X²/r=(U+1)/2=chi_alpha(h)². Since r is squarefree this forces r=1, and N=z².

If epsilon=-1, then dY²/r=(U+1)/2=chi_alpha(h)². Since d/r is squarefree this forces r=d, so N=-d z² and Delta/|N|=(m/z)².

The zero-coordinate cases are covered by the same identities (or immediately give positive square N when y=0, and N=-Delta when x=0 and N|Delta).

## Application to exact83 factors

At any full83 zero with even A, main and input norm values have the two forms above. The strong factor is minus a represented Pell norm S²-Delta f², so it is either a negative square or a positive divisor d_s with Delta/d_s square. The separate auxiliary theorem gives a positive square, independently of parity.

In particular, if A is even and Delta is squarefree, then

  norm_main, norm_input are each 1 or -Delta;
  norm_strong is either -1 or Delta;
  norm_aux=1.

This still leaves the first/index/transport factors, and does not prove unit normalization or ordinary-input soundness. A-even and squarefreeness are additional hypotheses, not known consequences of a general candidate zero.
