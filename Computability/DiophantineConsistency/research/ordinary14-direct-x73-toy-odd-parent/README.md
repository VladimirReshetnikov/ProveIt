# Proposed all-J parent exclusion at the direct-X toy ports

At the **toy** ports `beta=4, K0=1, MC=2, MF=5`, the separately reviewed
[`q=5` symbolic witness](../ordinary14-direct-x73-q5-toy/) gives a positive
zero of the `14/73` direct-X graph. This packet proposes that the `14/74`
parent has **no** positive zero at those same toy ports for **any** positive
J. The argument uses the pinned existing source theorem statements and the
reviewed external universal trace bound; its fact-level application and
scope require independent review. It is a toy-port result, not a statement
about actual compact44 ports, a new Lean/iPRA theorem, a provider replay or
a proof about the displayed PDF equation.

If both the symbolic witness and the all-J source replay hold, they show the
two parameterized graphs' positive-zero existence predicates differ at these
toy ports. They do not decide whether the direct-X graph is equivalent to the
parent at the **actual** ports, where beta is odd and q need not be odd.

## Scalar and unit-factor premises for every J

Suppose a positive `14/74` parent zero exists at the toy ports. Write

```
b=4J, q=b+1, X=q*w, Y=q³*s,
C=q−F−alpha, G=b*(q−F)+alpha,
R=G*(q²−1)+J*(MC+q*MF).
```

All inputs J,F,alpha,w,s are positive. In particular q is odd and `q>=5`.
The reviewed parent five-unit proof forces its four Pell/auxiliary factors
and guard factor to +1. The guard factor gives

```
C*(X+K0)−F = b*(h−1) >= 0.
```

Since F>0 and X+K0>0, C>0 and hence `F+alpha<q`. The port hypotheses of
`ArithmeticAdaptiveRankWindow2011.scalar_rank_window` are satisfied for
**every** J: `beta=4>0`, `0<MC=2<4`, `0<MF=5<8`,
`q=beta*J+1`, and all relevant inputs are positive. Its stated conclusion
gives `R+q³+q+1<=q⁴`. Moreover `q−F>=alpha+1>=2`, so

```
G>=2*(q−1)+1=2q−1,
R >= (2q−1)*(q²−1) >= q³ >= 125 > 26.
```

Thus both `R>=26` and `R+1<q⁴` hold uniformly in J; no `beta>=46`
premise has been inserted into this scalar-window theorem.

## Fact-level exact-index and trace replay

The parent graph syntactically gives `Y=q³*s` and the positive first norm
`r²−m*(m+1)*k²=1`, where `m=X*Y²`, `k=eta+zeta>0` and
`c=eta+Y*k`. Its main, strong and direct-auxiliary factors equal +1.
The independently reviewed direct-auxiliary argument in
[`ordinary14-aux-root78`](../ordinary14-aux-root78/) uses these norms to
recover a positive u with `y=V+u`; it does not require beta>=46 or an old
literal zero.

With `U=Y*q²=q⁵*s`, `a=Y*(X+1)` and `H=4a+3`, the modified main
carrier is

```
Dstar=U*(X+a*c)+H*(U*gamma−k+R+1).
```

It is positive from the same explicit inequality used in the reviewed
[`14/84` replay](../ordinary14-qcube84-probe/): `c>Y*k`, q>=5 and
Y>=q³ give `U*a*c>H*k`. Its norm therefore gives a positive integer d with
`Dstar=U*d` and `d²=1+Delta*c²`. Reducing the carrier equation modulo q⁵,
the factor-three cancellation works even when 3 divides q because
`H=3+4*q³*s*(X+1)` has gcd with q⁵ at most 3. Thus
`q⁴|(R+1−k)`. The first Pell classification gives positive n and
`k=2*n+4*m*v`, and q⁴ divides 4m. Together with the rank window,
`mu=q⁴` satisfies the exact residue/window hypotheses of
`P72Exact.indices_ordinary`.

Its other explicit inputs are q>=3, positive X,s,eta,i,f, the main norm,
`c=eta+Y*k`, `a=XY+Y`, the ordinary strong norm with **`i_prime=i`**, and
the recovered positive-u auxiliary norm. These are supplied by the factors
above. The theorem statement yields `n>=13`, a main Pell index equal to R,
and `2n=R+1`. Since `Y=q³*s`, the first recurrence also gives

```
k=R+1+U*W,  W=4*X*q*s*v >= 0,
d = X+a*c+H*(gamma−W).
```

The last equality is understood over the integers if `gamma−W` is
negative; it yields the **unscaled** congruence `d≡X+a*c (mod H)`.
The reviewed universal trace lemma applies because eta,zeta>0 give
`Y*k<c<(Y+1)*k`: its Pell-ratio bound puts `2^R<H`, and the trace identity
therefore gives `X=2^R` without an X>=16 hypothesis.

But the parent syntactically has `X=q*w`, while q=1+4J is odd and greater
than 1. An odd integer greater than 1 cannot divide a power of 2. This
contradiction excludes a positive parent zero for **every** J at these toy
ports, subject to the source-theorem replay described above. It does not
invoke the parent wrapper that has an extra `beta>=46` premise.

## Checks and limitations

The checker pins the parent graph, the q=5 toy receipt, the universal-bound
record and relevant Lean source statements. It checks the scalar-window and
parity conclusions on 22,540 finite positive tuples for J=1 through 20.
Those controls do not prove the all-J assertion, the symbolic toy witness,
or the unbounded Pell/source-theorem applications. No Lean process was run.

```
python3 -I -S -B research/ordinary14-direct-x73-toy-odd-parent/check.py > /tmp/direct-x73-toy-odd.json
cmp /tmp/direct-x73-toy-odd.json research/ordinary14-direct-x73-toy-odd-parent/result.json
```

Independent source review is recorded in
`../../reviews/ordinary14-direct-x73-toy-odd-parent-independent/`.
