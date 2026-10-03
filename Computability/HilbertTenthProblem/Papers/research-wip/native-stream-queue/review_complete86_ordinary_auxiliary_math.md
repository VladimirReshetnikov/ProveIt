# Independent mathematical review of the ordinary auxiliary projection

The ordinary-strong variant supports the same deletion of one auxiliary
coordinate as the normalized 85-operation source, but it requires a different
integrality argument. The decisive step is to recover the ordinary Pell rank
*before* restoring the deleted positive quotient. The resulting circuit has
86 operations, 18 positive witnesses and exact degree 131, subject to the
full saved-source checks in the [author packet](complete86_ordinary_auxiliary_projection.md).

This review's [bounded helper](review_complete86_ordinary_auxiliary_math.py)
and [receipt](review_complete86_ordinary_auxiliary_math.json) authenticate the
frozen author and inherited proof files. They execute no author or historical
Python. Finite modular, inequality and auxiliary examples support the proof
below; none is advertised as a full compiler zero.

## 1. Actual ordinary interface

Use the inherited mathematical notation

    q=(B−1)J+1, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=Y(X+1), A=a+2,
    Delta=A²−1, H=4a+3,
    Kindex=k−hE, R=the actual packed-index expression.

All compiler numerals are fixed on a valid language slice. Source register
`A` denotes Delta; mathematical A above is a+2. The retained ordinary factor
and auxiliary base are

    Ns=(ic²)²−Delta(f²−1)+1,
    Kaux=Delta(f²−1).

Replace positive o,j by positive T and compute

    V=c(Tf−1)−Rf²,
    Na=Kaux V²−(Kaux−1)y²,
    Nk=Kindex−R.

The product still retains first, main, input, auxiliary, index, transport and
strong factors. The omitted factor was `Nl=of−c−jc+Kindex`.

For independent j and o=cT−Rf, the exact all-value correction is

    Fparent+1=(Fchild+1)(Nk+V+R−jc).

On c≠0 one may set j=(V+R)/c, giving

    Fparent+1=(Fchild+1)Nk.

This is a rational change of variables away from zeros. The circuit contains
no division, and the proof of integral positive j at every positive child zero
is essential. The normalized formula involving R Delta i²c³ must not be
substituted into this ordinary source.

## 2. Recover the ordinary rank first

At a positive child zero, every retained integer factor is a unit. The
first-root argument from the parent excludes its negative unit for XY²>1.
Since Delta≡0 or3 mod4, the main and input norms cannot be−1. The ordinary
strong factor cannot be−1 either: modulo4 it is a square plus1 when Delta≡0,
and a sum of two squares when Delta≡3. Hence Ns=1 and Kaux=(ic²)². Reduction
of Na modulo4 then excludes−1 because Kaux is a square. The remaining index
and transport signs agree; write Nk=Nt=epsilon∈{−1,1}.

The actual sheared transport and packing equations are unchanged from the
85 proof. Without using auxiliary positivity, they give C≥0, F+Z<q, R>0,
R+2<q⁴≤E, a>R+2 and Delta>R. In particular this construction does not have the
signed19 candidate's input interface, whose complete negative family permits
F>q and negative computed W.

The first and main positive Pell norms give

    k=2 psi_P(n), P=2XY²+1,
    c=psi_A(p), D=chi_A(p).

The first congruence is `2n≡R+epsilon (mod E)`. Its least positive
representative gives n≥(R−1)/2≥24. Since P>A and c>kY>k, p≤n is impossible;
thus p>n. The usual Pell growth bound now gives

    c>A Delta².

No sign of V, quotient j or auxiliary rank was used to obtain this size bound.

Apply the inherited [relaxed auxiliary rank proof](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md)
to Ns=1 with this c=psi_A(p). Its proof is valid for mathematical A≥2 and
does not require the historical a+4 parameterization. It yields

    f=chi_A(m), ic²=Delta psi_A(m), p|m, c|m.

Strong divisibility gives c|psi_A(m) from p|m. Therefore

    c² | (f²−1).

The last conclusion is enough here. One must not claim c²|psi_A(m) for the
ordinary source: that stronger assertion can fail when gcd(c,Delta)>1.

## 3. Recover positive o,j without circularity

The strong equation and i≥1 imply f²≥1+c⁴/Delta. Since c>A Delta²,

    c²>4Delta, c²>Delta+c,
    f²>4c² and f²>Delta+c.

Together with Delta−R≥1 this proves the ordinary gap

    Kaux−Rf²−c=(Delta−R)f²−Delta−c>0.

This replaces the normalized source's different lower-bound calculation.

Write v=|V|. The auxiliary equation is

    Kaux v²−(Kaux−1)y²=1.

V=0 is impossible. If v>1, then y≥v+1 and

    v²−1≥(Kaux−1)(2v+1), hence v≥2Kaux−1.

But T>0 gives V>−Rf²−c>−Kaux, excluding the negative nontrivial branch.
The cases V=±1 are also impossible: V≡−c (mod f), while f>2c and c>2 give
0<c−1<c+1<f. Consequently V>0.

Restore

    o=cT−Rf=(V+c)/f,
    j=(V+R)/c=Tf−1−R(f²−1)/c.

The first is an integer by its polynomial expression, and the second is an
integer by the recovered divisibility. Both are positive. Their two actual
congruences are `V=of−c=jc−R`. This establishes integral positive values
before any invocation of the parent compiler theorem.

## 4. Recover the positive index sign, then transfer the parent

The ordinary rank gives c|m and m≥c>2p. Also a>R+2 and the size bound give
c>2R. The fixed-minus auxiliary step-down used in the parent and independently
reviewed for 85 therefore yields p=R: the residue alternatives ±p modulo c
have unique representatives in the required positive interval. The quotient
restoration has made the linear target exactly R, regardless of epsilon.

Now `2n=R+epsilon+vE` with v≥0. If v≥1, E>R+2 gives 2n>2R, contradicting
n<p=R. Thus v=0. If epsilon=−1, p=2n+1. The duplication identity and
chi_A(2)>P give

    psi_A(2n)>2A psi_P(n)=Ak,
    c=psi_A(2n+1)>Ak>k(Y+1),

contrary to the retained eta/zeta interval. Hence epsilon=1. Restored Nl=Nk=1,
and all eight parent factors equal1. Only now is the full positive parent
zero theorem invoked. It transfers the same ordinary input and program
numerals to the represented language.

Conversely, start at any full positive ordinary parent zero. Its established
factor/rank theorem gives R>0, all factors1 and c²|(f²−1). The parent linear
and index factors give of+R=c(j+1). Multiplying by f modulo c gives

    o+Rf≡0 (mod c).

Therefore T=(o+Rf)/c is positive integral. The computed child V is the old
of−c, and all seven retained factors stay1. The two maps recover each other
on the complete positive zero sets, including noncanonical ordinary auxiliary
indices. They are not maps between arbitrary positive off-zero tuples.

## 5. Independent finite evidence and limits

The helper checks 256 ordinary strong-factor residue cases, 64 square-base
auxiliary cases, and the main/input residues. It checks 192 cleared integer
gap inequalities under the actual large-c hypotheses.

Four independently constructed auxiliary tuples use (A,p)=(2,3),(3,3),(4,3)
and(2,7), with m=pc/g and g=gcd(c,Delta). They verify both ordinary factors,
both congruences, positive forward/inverse quotient maps and exact coordinate
recovery. The (2,3) and (4,3) cases have ordinary indices that fail the stronger
normalized divisibility; they demonstrate why the distinct proof matters.
The (2,7) tuple has c=2911>A Delta² and a largest coordinate of 232,299 bits.
It satisfies the rank-size hypothesis but remains only an auxiliary example,
without the complete packed input/first/main constraints.

The uniform arithmetic degree claim is a statement about the full source
polynomial and independent supplied coordinates. It cannot be justified by
substituting the zero-only rank identities above. The author packet's source
and [independent source review](review_complete86_ordinary_auxiliary_source.md)
are separate from this mathematical review.

    python3 /absolute/path/review_complete86_ordinary_auxiliary_math.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/review_complete86_ordinary_auxiliary_math.json
