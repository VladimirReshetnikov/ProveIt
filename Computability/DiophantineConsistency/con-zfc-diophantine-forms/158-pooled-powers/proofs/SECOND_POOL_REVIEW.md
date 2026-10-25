# Independent internal audit: pooled power congruences

25 October 2026. This is an independently worked ordinary mathematical review
within the AI-assisted research session, not external peer review and not a
compiled Lean/Rocq or object-language ZFC certificate.

The reviewed mathematical transformation replaces multiple congruence
quotients for the same requested power base by two quadratic aggregate rows.
The source is the current signed Pell construction after the strict-horizon
change. I also inspected the literal producer
`code/build_pools.py` (ported from the reviewed research producer) and its polynomial identity checks.
That inspection is narrower than an independent complete release replay.

## A. Exact quadratic encoding identity

Fix one nonzero integer base n shared by r power requests. For request i,
write m_i for the proposed output, (X_i,Y_i) for its already classified and
oriented signed Pell pair, and Z_i=A Y_i for the retained multiplication
wire. Set

    T = 2An-n^2-1,
    H = sum_i Y_i(m_i-X_i),
    S = sum_i [(m_i-X_i+Z_i)^2-Y_i^2].

Introduce only K,L and impose

    K = 2H+(2A-n)L,
    S-nK+L = 0.

All expressions in these two equations have degree at most two in the
actual materialized coordinates. In particular Z_i is an existing wire,
not an unmaterialized product hidden inside a square.

Let e_i=m_i-X_i+(A-n)Y_i. Substitution gives the exact identity

    sum_i e_i^2 = T*(L-sum_i Y_i^2).

For example, expanding S-2nH gives
sum_i e_i^2+T sum_i Y_i^2, so the second row and the first row imply the
claimed formula immediately. No individual congruence is assumed here.

The optional norm reduction in the producer adds to S the retained Pell
residuals X_i^2+Y_i^2-Z_i^2-1. They are already zero. This is an elementary
residual-row operation, so it preserves the simultaneous zero set and the
argument above. It may change the collected polynomial's coefficients,
but it does not change the meanings of the witnesses.

## B. Recovering every individual power using the existing frame

No strengthening of the inherited frame is needed. The important bound is
the actual sum-of-squares identity, not merely its weaker consequence that
every atom has absolute value below W. The frame has

    W = 2 + sum(actual_atom^2),       W>=258.

Every actual base n, output m_i, and requested index k_i belongs to this
finite atom list. Therefore n^2,m_i^2,k_i^2<W. Put

    b = floor(sqrt(W-1)).

Then b>=16, b^2<W, and |n|,|m_i|,|k_i|<=b. The existing odd frame already
gives |A|>W^W. Signed orientation gives X_i=X_{k_i}(A), Y_i=Y_{k_i}(A).

The Pell power congruence is
X_k(A)+(n-A)Y_k(A)=n^k modulo T. For negative k this is interpreted using
the invertible residue n, because T=-1 modulo n and hence gcd(n,T)=1.
Every exponent b+k_i lies in [0,2b]. Thus the following are ordinary
integers:

    d_i = m_i*n^b - n^(b+k_i),
    E = sum_i d_i^2.

Modulo T, d_i is congruent to n^b e_i. Section A implies T|E. We have

    |d_i| <= b^(b+1)+b^(2b) <= 2b^(2b),
    0 <= E <= 4r b^(4b).

The actual groups have r=11 and r=3, and the conservative r<=15 suffices.
Because 4r<=60<W and b^2<W,

    E < W^(2b+1).

Also 2b+1<=b^2+1<=W, so

    0 <= E < W^W.

For any integer |n|>=1, the same square bound gives

    |T| >= 2|A||n|-n^2-1
         >= 2|A|-W
         > |A| > W^W.

Thus 0<=E<|T| and T|E force E=0. Every d_i=0. If k_i>=0, cancellation
of n^b gives m_i=n^{k_i}. If k_i<0, it gives m_i n^{-k_i}=1, which is
impossible when |n|>=2. Thus all those indices are nonnegative and all
outputs are exact. For n=1 the output is 1 for every signed k_i. For n=-1
it is the appropriate parity sign; neither unit base is claimed to force
index nonnegativity.

No square-root or variable exponent is added to the final polynomial.
The integer b and the powers n^b are proof devices for interpreting the
unchanged quadratic source.

## C. Independent audit of the actual frame atoms

I independently reconstructed the literal frame row as W minus 2 minus
36 squares of affine expressions. The reconstruction matches the complete
expanded row exactly. It includes the actual base, exponent and output of
all 17 retained power requests. The executable check is
`code/check_all_frame_atoms.py`; `verification/ALL_FRAME_ATOMS.json` records one checked
principal-stage identity. The check should be rerun on the sealed final
object if subsequent changes alter its equation hash.

The centered coordinate names by themselves would be misleading. The
actual affine interpretations verified in this check are:

* the stored `t0` coordinate is actual t;
* the stored `crt.encoded.a` coordinate is a+1, so actual a is that
  coordinate minus 1;
* the stored other CRT parameter coordinates b,c,d,S,Sp,u,vq are their
  actual values;
* `crt.encoded_index_minus_one` is actual C after the recorded translation;
* `add.380` is actual h;
* `pow2.output` is q+1, so actual q is that coordinate minus 1;
* after the beta contraction, `pow0.output` is V=y+1.

The frame contains both q^2 and (q+1)^2, so the two aggregate bases have
the square bound independently. It contains (F^2+t)^2, all nine actual
representative squares, h^2, x^2, t^2, and every retained power output
square. The V=y+1 identification produces two equal V squares; that
multiplicity is harmless. The redundant (t+1)^2 atom remains even though
the q^(t+1) output and its request have been deleted.

The inherited odd frame is retained exactly:

    A^2-[(W+1)^2-1]*[W(2z+1)]^2=1.

It supplies |A|>W^W by the parent's standard signed Pell classification.
Its completeness is already part of the retained source proof. There are
no frame-row edits in the final pooling transformation. An earlier draft
used a larger frame at 4W+1; the sharper atom-square estimate makes that
change unnecessary and it is not part of the reviewed final construction.

## D. Completeness of the pooled equations

For genuine powers with canonical Pell pairs, every e_i is divisible by T.
Since T is nonzero, set

    L = sum_i Y_i^2 + (sum_i e_i^2)/T,
    K = 2H+(2A-n)L.

Both are integers and the two aggregate rows vanish. This shows that
pooling adds no new restriction on a genuine finite family of powers.
Unrestricted integer witnesses are essential: no sign assertion about K or
L is needed.

## E. Bootstrap order and unit-base cases

The three singleton requests at bases F^2+1, B and BH are retained. Before
any factorial interpretation, they give V=(F^2+1)^t, x>=0 and
q=(BH)^x with |B|>=2 and H odd. If x=0 then q=1. The pooled base-q lemma
at the unit base 1 gives M=1, contradicting B|M and |B|>=2. It is NOT
necessary to infer any index sign from the unit-base lemma.

Thus x>=1 and |q|>=2. The pooled base-q requests recover q^t and q^x.
Their normalization ratio yields x>=t>=16, so |q|>=2^16. Only at this stage
is the base-q+1 group used to force nonnegative representative indices:
now |q+1|>=2^16-1>=2. This avoids the premature use of that conclusion in
the temporary signed possibility q=-2, q+1=-1.

The inherited frame and its original W^W bound continue to justify all
three singleton power arguments. The rest of the
rounded-factorial bootstrap and the F=0 repair are exactly the argument
in `proofs/STRICT_HORIZON_AND_BETA.md`.

## F. Cofinal beta base and padding check

For y=V-1, the finite proof tree has L expansion steps before padding.
Choose t=16+z^2 with t>L, before F=t!. Starting from one formula, each
expansion increases the number of pending formulas by at most one.
The number of pending formulas is therefore at most L+1<=t. Truth padding
leaves the pending-state product unchanged; it does not introduce new
nontrivial pending formulas. Thus extending the trace to exactly t rows
does not invalidate the bound.

Every formula label is below t. Its weight is at most 1+(t-1)F<F^2+1,
so every pending product is <(F^2+1)^t=V. Hence all states are <=V-1=y.
The divisibility F|y and the beta CRT proof follow. The original centered
coordinate convention is actual y=X2-1 and V=X6, as verified from the
parent translation certificate and both endpoint rows. Therefore the new
literal definition is indeed X2-X6=0. This was checked independently of
its variable name, which by itself would not establish the shift.

## Verdict and limitations

The pooled power lemma with the unchanged inherited frame, the cofinal
strict-range change, and the linear beta-base change are mathematically
compatible. I found no
circular sign or factorial dependency in the described recovery order.
The independent arguments above establish the quantified claims; finite
artifact verification must still authenticate the exact emitted polynomial,
its coordinate maps and inherited source closure.

The review does not establish absolute minimality, worldwide priority,
a newly compiled formal certificate, or the truth of Con(ZFC).
