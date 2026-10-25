# A signed Pell cap with pooled index residues

Status: proved abstract replacement/orientation lemmas and a proposed source transfer.
No source, compiler, quartic, operation count or canonical page is changed.
This extends the mathematical cap mechanism of package124 from natural
principal ordinates to signed integer principal ordinates. Its application
to the accepted Round15 source still needs an exact source certificate.
The original natural cap theorem and the relevant signed Round15 interfaces
are pinned in SOURCE_PINS.json. No incoming program has been executed.

## 1. Precise abstract hypotheses

For an integer A>=2 write D=A²-1 and define

    X_0=1, Y_0=0,
    X_(j+1)=A X_j+D Y_j, Y_(j+1)=X_j+A Y_j.

Assume integers W>=4, A-1>4W³, a nonnegative integer m<=W-2 and
integer requested indices k_1,...,k_m with |k_i|<W. A positive cap
ordinate V is independently certified to be Y_W(A). For every i let
x_i,y_i be unrestricted integers satisfying

    x_i²-D y_i²=1.                            (1)

Impose two integer polynomial conditions:

    V²-sum_i y_i²-1 = a²+b²+c(c+1),            (2)
    sum_i(y_i-k_i)² = (A-1)h.                 (3)

Here a,b,c,h are integer witnesses. There is no sign predicate on h:
the left side of (3) and A-1>0 already imply h>=0. The right side of
(2) is nonnegative for every integer triple. Every nonnegative integer
has such a representation by the previously accepted Legendre/parity
lemma. Thus (2) is exactly the nonnegative quadratic cap predicate.

The conclusion is

    y_i=sgn(k_i) Y_|k_i|(A),
    x_i=+/-X_|k_i|(A).                         (4)

At k_i=0 the convention is y_i=0 and x_i=+/-1. In particular k_i>0
forces y_i>0. The conclusion does not orient any x_i. Positivity of
the cap and its actual requested index are separate hypotheses, not
consequences of a sum of squares of arbitrary signed coordinates.

## 2. Proof of signed index recovery

Integral Pell classification gives unique j_i>=0 and independent signs
with |x_i|=X_(j_i), |y_i|=Y_(j_i). If y_i!=0 put sigma_i=sgn(y_i);
at y_i=0 choose either sign. The quadratic cap implies |y_i|<V. Since
V=Y_W and Y_j is strictly increasing, j_i<W.

Reduction of the two recurrence equations modulo A-1 gives
X_j=1 and Y_j=j modulo A-1. Therefore

    y_i = sigma_i j_i modulo A-1.

The actual pooled row (3) now implies divisibility of the FINITE INDEX
ERROR

    E_index=sum_i(sigma_i j_i-k_i)²            (5)

by A-1. Each |sigma_i j_i-k_i|<=j_i+|k_i|<=2(W-1), so

    0<=E_index<=4m(W-1)²
                 <=4(W-2)(W-1)²<4W³<A-1.

Hence E_index=0. Every summand vanishes: sigma_i j_i=k_i. This proves
(4), including the zero and negative requested-index cases.

The giant quantity in the actual polynomial row is sum(y_i-k_i)². It
is generally NOT less than A-1. Only its congruent finite expression
(5) is bounded. The quotient h is an arbitrary integer at the start
of the proof, and neither h nor the actual sum is asserted to be zero.
Confusing those quantities would invalidate this proposal.

## 3. Why the natural modulus hypothesis needs strengthening

The natural theorem bounds j_i-k_i between -(W-1) and W-1. Signed
ordinates instead produce sigma_i j_i-k_i, whose absolute value can
reach2(W-1). Thus A-1>W³ by itself is not a sufficient signed theorem.

An explicit countercase is W=5,A=129,m=3,k=(4,4,1). Take

    x=(X_4,X_4,X_1), y=(-Y_4,-Y_4,Y_1), V=Y_5.

All three norms hold, |k_i|<W, m=W-2 and A-1=128>W³=125. The
canonical positive cap dominates the sum of their squares because
Y_5>(2A-1)Y_4 and Y_1=1. Yet E_index=64+64+0=128, so the actual
pooled sum is divisible by A-1 while the first two ordinates have the
wrong sign. The nonnegative cap has a Legendre witness as well. The
strong scale condition of the proposed application excludes this case.

The accepted Round15 square frame has W>=4 and the norm

    A²-W³(W+2)Z²=1, A>=0, Z>=1.

It identifies (A,WZ)=(X_l(W+1),Y_l(W+1)) with l>=1. Modulo W,
W|l, hence l>=W and A>=(W+1)^W. For W>=4,

    (W+1)^W-1>4W³.

One proof is (W+1)^W>W^W>=4W³, with equality in the last comparison
only at W=4; even there5^4-1=624>256. Thus the ACTUAL polynomial
scale supplies the stronger modulus before interpreting any power.
From merely A>W^W at W=4 one should use the non-strict A-1>=4W³
with the strict error bound, rather than assert the stronger inequality
without the actual scale argument.

## 4. The cap must certify its own index without a circular bound

Condition (2) alone proves V>=1 if V is known positive. It does NOT
prove W<=V. Package124 removed the cap's old V-minus-W witness only
because its natural aggregate row explicitly gave V>=W+1. The new
quadratic row must not silently inherit that deleted argument.

Two sound alternatives are available:

1. Retain the cap's OWN full indexed-Pell certificate, including its
   requested-index lower bound V>=W. Its private sign hypotheses and
   comparison/congruence witnesses must be checked under their actual
   signed-domain implementation. Then V=Y_W is known before (2) is used.
2. Replace (2) by the slightly stronger single quadratic predicate

       V²-W²-sum_i y_i²-1 = a²+b²+c(c+1),      (6)

   and independently enforce V>0. Before any index interpretation,
   (6) implies V>W. This supplies the full cap certificate's W<=V
   hypothesis acyclically. Its indexed-Pell conclusion then gives
   V=Y_W, after which the proof of section2 is unchanged.

Both alternatives retain one COMPLETE certified cap. A single cap norm
and a few unqualified congruences are not a replacement for the inherited
indexed-Pell theorem. All natural or strict hypotheses on its private
coordinates need explicit signed guards or an independent proof. No
unsupported new signed auxiliary-index lemma is assumed here.

The quantities V,x_i,y_i, cap private witnesses, comparison bases and
quotients are excluded from the semantic frame W. In particular W does
not depend on its future cap or the Pell ordinates it will bound.

## 5. Constructive completeness of both cap predicates

Given genuine target indices with |k_i|<W, choose

    x_i=X_|k_i|(A), y_i=sgn(k_i)Y_|k_i|(A), V=Y_W(A).

They satisfy (1), and y_i=k_i modulo A-1. Thus the actual sum in (3)
has the explicit nonnegative integral quotient

    h=sum_i(y_i-k_i)²/(A-1).

Since |y_i|<=Y_(W-1), the recurrence gives

    V>(2A-1)Y_(W-1),
    V²-sum_i y_i²>((2A-1)²-m)Y_(W-1)².

Our size hypotheses imply A>W+1 and Y_(W-1)>=1. Hence the last
expression exceeds W²+1. Both (2) and the stronger (6) therefore
have nonnegative left sides and explicit Legendre-triple witnesses.
No extra growth condition on already chosen semantic outputs is needed.

For an actual source, choose the genuine semantic front tuple FIRST.
It fixes all base/exponent/output atoms and W. Choose A from the scale
Pell pair, then all main pairs, then the complete cap certificate, and
finally h and the quadratic-cap triple. Any common comparison-unit/CRT
witness used by the full cap or retained t/K certificates is chosen
AFTER the needed main/cap ordinates. Its finite-ring product modulus
must contain exactly their required squared divisors. No parameter
that enters W is chosen after A or V. These are fresh private witnesses,
not unchanged old Pell coordinates.

## 6. Power orientation is still a separate obligation

For a positive recovered index k, (4) gives y=Y_k>0, but x can still
be +/-X_k. For an actual base2<=n<W and signed candidate output m
with |m|<W and k<W, let T_n=2An-n²-1>W^W and retain

    x+(n-A)y=m+T_n q_n.

The positive-x branch gives m=n^k modulo T_n. The negative-x branch
gives m*n^k=-1 modulo T_n: indeed for H=X_k+(n-A)Y_k and
J=X_k-(n-A)Y_k the identity HJ=1+T_n Y_k² holds, and H=n^k modulo
T_n. The frame bounds give

    |m*n^k+1|<T_n, |m-n^k|<T_n.

Since n^k>=2, no integer m satisfies m*n^k=-1. The negative branch
is impossible and the positive branch forces m=n^k>0. The power
quotient needs no sign. This is the accepted signed-output lemma at
an actual positive ordinate, with its precise hypotheses retained.

For n=1, the negative branch m=-1 is possible. For k=0 the analogous
exception is also real. Such cases cannot be dismissed by the cap.
They may be interpreted only after a supporting n>=2,k>=1 call has
oriented the SAME pair. For a requested negative index, the cap merely
recovers its signed ordinate and does not license ordinary positive
integer exponentiation. Positivity must be established before a call.

## 7. Conservative transfer to the accepted Round15 source

A first source proposal should retain the original t and K support
mechanisms and replace only the thirteen selected comparisons by the
signed-cap mechanism. Its cap targets are their ACTUAL requested even
indices e_i=2k_i, not the old undoubled k_i. Keep their norm and
squared-output congruence rows until a separate theorem licenses any
further simplification. The derived t+1 pair remains the original
one-step addition from the positively oriented t pair.

The square frame is already W=2(2+sum a²) over the complete original
semantic atom set. Its literal consequences give |a|<W,2|a|<W and
a²<W. Therefore |e_i|<W and every selected squared power output is
below W. The source has t>=16 as a semantic atom, so W>=516; in
particular the thirteen (or all fifteen) independent targets obey
m<=W-2 without assuming all other indices are already positive.
The base of the cap is this same A, and its requested index is W.

The retained raw factorial and weighted interval rows first establish
B>=1,q>=2 and the needed ordinary front signs. Recover the positively
oriented t pair using its base-q supporting request; its other request
then yields (F²+1)^t even at the possible base-one endpoint. The
factorial ceiling restores F>=1,B>F and q>=3. Only then orient the
K pair at base B>=2 and recover N=B^K and q=N^K. The derived pair
and q-power denominator calls precede the terminal successor calls.

The signed cap may be interpreted as soon as its frame and full anchor
are certified. It recovers each selected y_i=psi_A(e_i)>0 when e_i>0.
The existing squared-output sign/residue-one proof then applies with
stronger main-pair information. All eleven successor outputs retain
their actual remainder substitution, and the two selected q outputs
retain their positive interval interfaces. The original staged native
proof resumes after all eighteen powers have their licensed meanings.

The existing positive_seed_certificate.json in fact proves all fifteen
ORIGINAL seed exponents positive before power recovery, without a prior
carrier meaning. That permits the conservative even targets above.
Using the generic signed theorem does not excuse deleting or changing
that certificate without rebinding its complete raw leaf/sign chain.

A possible later simplification is to use the original undoubled targets
and signed unsquared outputs once the cap has proved y_i>0: section6
then recovers each output at every n>=2. The base-one t request is
still handled only after its supporting base-q call. This might remove
the purpose of the even-index/residue-one machinery, but it is a
DIFFERENT proposed source transformation. It has no literal artifact,
cost claim or acceptance in this note.

## 8. Remaining source and finite-certificate obligations

Before any equation or metric claim, a complete future packet must:

- Bind every actual primary pair, target affine expression, norm,
  supporting call and exceptional base to the old source rows; identify
  exactly which comparison subgraphs and product factors can disappear.
- Emit a fully certified cap at index W, with an explicit proof of its
  positive ordinate and W<=V premise by one alternative in section4.
  Bind all private sign predicates and guard triples used by that proof.
- Replay the whole square-frame identity, |e_i|/output bounds, m bound
  and the scale proof A-1>4W³ before interpreting a power. Keep every
  future cap/private coordinate out of the semantic atom inventory.
- Bind the complete pooled quadratic row and cap predicate, distinguishing
  their actual large values from the bounded index-error representative.
  Ensure each target is affine in the emitted coordinates, so residual
  degree remains two after all substitutions.
- Reprove all front signs, t/F/K support order, derived-pair recurrence,
  output orientation and subsequent native/binomial/CRT calibration at
  the unchanged semantic interface. Rebuild every needed private witness
  in both existential directions; do not claim pointwise old tuple maps.
- Independently validate all row maps, guards, private-variable nonescape,
  projections, complete collected polynomial and whole fixed coefficients.
  Normal/optimized corruption controls must include a missing cap-index
  lower bound, an underpowered modulus, a signed abscissa, negative or
  zero target indices, base-one output, an omitted pooled term and a
  private coordinate accidentally inserted into W.

The abstract signed-cap theorem and its witness construction are complete
under the explicit hypotheses above. Its application to Round15 is a
mathematically supported proposal with these exact remaining obligations.
There is no generated successor source and no projected numerical frontier.

## 9. A stronger joint row can orient a signed scale as well

Root proposed a further variant after the positive-A analysis above.
Allow A to be signed, put a=|A|>=2, and assume W>=4 EVEN,
|A-1|>4W³, m<=W-2 and |k_i|<W. Keep the primary norms (1), whose
coefficient is unchanged because A²=a². Independently certify a POSITIVE
cap C=Y_W(a), with C>=W. Use either quadratic cap (2) or (6), replacing
V by C. Change the pooled row to

    sum_i(y_i-k_i)²+(C-W)²=(A-1)h, h in Z.     (7)

The cap is included in this congruence, but not in the semantic frame
or the primary squared cap sum. Its index is W, not a falsely asserted
index less than W. The quotient h must remain signed when A is signed.
The actual left side can be enormous; it is not the bounded error below.

The following elementary recurrence identities hold also for negative A.
With epsilon=sgn(A), for j>=1,

    X_j(A)=epsilon^j X_j(a),
    Y_j(A)=epsilon^(j-1)Y_j(a),
    Y_j(A)=j modulo A-1.

Consequently a signed primary ordinate y_i=sigma_i Y_(j_i)(a) has
residue tau_i j_i modulo A-1, where
tau_i=sigma_i epsilon^(j_i-1). At j_i=0 assign tau_i arbitrarily.
The positive cap C=Y_W(a) has residue epsilon^(W-1)W. The cap inequality
again gives j_i<W. Thus (7) implies divisibility by A-1 of

    E_joint=sum_i(tau_i j_i-k_i)²
             +(epsilon^(W-1)W-W)².            (8)

Every primary difference has absolute value less than2W, and the cap
difference has absolute value at most2W. Therefore

    0<=E_joint<=4m(W-1)²+4W²
                    <=4(m+1)W²<4W³<|A-1|.

It follows that E_joint=0. Since W is even, epsilon=-1 would make the
cap term exactly4W², impossible. Hence A>0. Now tau_i=sigma_i and
each remaining equality gives sigma_i j_i=k_i exactly as in section2.
The joint row therefore proves BOTH the sign of A and every requested
signed primary index. For integer k define Y_(-k)(A)=-Y_k(A) and
X_(-k)(A)=X_k(A); the conclusion is y_i=Y_(k_i)(A), with x_i still
allowed either abscissa sign.

Both evenness of W and positivity of C are essential to this argument.
For odd W a negative A has epsilon^(W-1)=1 and the cap term in (8)
does not detect its sign. If C were allowed to have the sign of
Y_W(A), a negative A at even W would likewise escape. Squaring the cap
in its range inequality does not supply the required sign of C.

## 10. A full cap certificate at |A| can be proved without A>0

It is not enough to cite the natural cap certificate with a signed A
without checking its hypotheses. Here is an explicit sufficient signed
version of the inherited three-norm certificate. Keep integer variables
Xc,Uc,Vc,Bc,Sc,Rc,d,e,f,g,r with

    Xc²-(A²-1)C²=1,
    Uc²-(A²-1)Vc²=1,
    Sc²-(Bc²-1)Rc²=1,
    C>=W>=4, Vc>0, d>=0,
    Vc=C²(e+1), Bc=1+4Vc(d+1),
    Bc=A+Uc f, Sc=Xc+Uc g, Rc=W+4C r.         (9)

The quotients f,g,r and abscissas may be signed. Vc>0 already implies
e>=0, so no separate assertion about e is needed. All displayed norms
are the usual lowered quadratic macros; (9) is a semantic interface,
not a claim that multiplying its displayed abbreviations creates no gates.
Alternative (6), together with C>0, can supply C>=W instead of a
separate cap-index lower predicate.

To prove the claim put a=|A|. Pell classification gives

    C=Y_i(a), |Xc|=X_i(a),
    Vc=Y_H(a), |Uc|=X_H(a).

Since C>=4, i>=2 and i<C. The squared-divisibility lemma applied to
C²|Vc gives i<=H and C|H. The constructor makes Bc>=5 and
Bc=1 modulo4C. Classify the last norm by an index j>=0 and independent
signs. It has j>0 because Rc=W modulo4C cannot be zero when0<W<=C.

Modulo |Uc| the base-transfer identity now reads

    X_j(Bc)=X_j(A)=epsilon^j X_j(a).

Together with Sc=Xc modulo Uc and the independent coordinate signs,
this gives X_j(a)=+/-X_i(a) modulo X_H(a). The inherited up-to-sign
abscissa residue lemma yields j=+/-i modulo2H. The sign of A is
absorbed into the allowed sign here; no claim Bc=a modulo Uc is made.
The range i>=2,H>=i avoids the exceptional small endpoint of that
residue lemma noted in the accepted Round15 review.

Modulo4C, base transfer at Bc=1 and Rc=W gives j=+/-W. Since C|H,
the two congruences imply i=+/-W modulo2C. But0<i<C and0<W<=C.
The negative case would require i+W=0 or2C, both impossible, and the
positive case forces i=W. Thus C=Y_W(a)>0, which is exactly the
absolute-base anchor hypothesis of section9. This argument uses only
norms, divisibility and comparisons, not a power meaning or F>=1.

All private sign/strict predicates in (9) still need an exact source
implementation. Dropping A's guard does not authorize dropping C's
positive guard, Vc's strict positive guard, d's lower guard or the
frame ordinate guard. Their roles in the proof are different.

## 11. Frame, completeness and the staged t bootstrap for the joint variant

The unchanged square frame W=2(2+sum atoms²) is even and at least4.
Keeping Z>=1 in A²-W³(W+2)Z²=1 proves
a=|A|>=(W+1)^W before a sign of A is known. Hence
|A-1|>=a-1>4W³. No power request or positive-A lemma was used to
obtain this modulus. All cap/private witnesses remain outside W.

For completeness choose the ordinary positive A and canonical pairs
after the genuine semantic front fixes W. Choose C=Y_W(A)>0, construct
the full certificate (9) using the inherited finite-ring/CRT witness
argument after C and any retained seed ordinates are known, and fill
the quadratic-cap triple by section5. The extra difference C-W is
itself divisible by A-1. Therefore (7) has the explicit nonnegative
integral quotient

    h=[sum_i(y_i-k_i)²+(C-W)²]/(A-1).

No quotient is chosen before its defining coordinates. This proves
completeness of the joint abstract module. A negative-A completeness
map is not required: the module has just proved that a zero has A>0.

For a source transfer the first power must be reproved at the new
index interface, rather than citing an old F-dependent theorem about
a changed kernel. The following order is available:

1. Replay the retained raw factorial/remainder and weighted-anchor rows
   to obtain B>=1,q>=2 and t>=16, with the square frame's absolute
   port bounds. No Pell power meaning is assumed.
2. Use (9), the quadratic cap and (7) to obtain A>0 and every signed
   requested main ordinate. In particular the t target gives
   Yt=Y_t(A)>0 without a separate Yt-minus-t sign guard.
3. Apply the signed-output proof of section6 to the actual base-q
   supporting request at t. This orients Xt positively and gives
   its output exactly q^t. Apply the other t congruence at baseF²+1
   using this SAME already positive pair. The base may equal1 at
   this stage; positive orientation makes that endpoint valid.
4. Recover V=(F²+1)^t>=1, then use F*B=V+fact_slack with B>=1 to
   infer F>=1,B>F and q>=3. This is the first use of the carrier
   interpretation, and it precedes the K and remaining power calls.
5. When the raw/partial arithmetic certifies K>0, the joint index
   equality supplies YK>0. The base B>=2 supporting request orients
   XK and gives N=B^K, followed by q=N^K. Recover the derived t+1
   pair by its ordinary one-step recurrence. All other targets are
   used as ordinary powers only after their positivity is licensed.

This order is a proved interface argument, not a claim that all
corresponding source predicates can already be deleted. In particular
the new cap's comparison unit and its own sign guards do not disappear.

## 12. Additional obligations of the stronger source proposal

In addition to section8, a future literal packet must bind the complete
certificate (9), retain its hypotheses under all early sign omissions,
and prove its unit/divisibility interfaces with the actual shared helper
coordinates. Reusing an old common helper is optional; its product
modulus must contain the cap's squared ordinate and the squared
ordinates of every still-retained comparison certificate. Its old
factors cannot be removed by an informal witness-count argument.

The exact row making W even, the strict frame ordinate and the
positive cap must precede joint orientation. The pooled term for C
must use its actual requested index W, not W-1 or an already assumed
positive-A residue. The error bound is modulo |A-1|, not |A|-1
when A<0. Missing any one of these distinctions changes the theorem.

Required adversarial controls now also include negative A with even W,
negative A with odd W, a reflected negative cap, an omitted cap term,
a zero frame ordinate, and a signed power output at the base-one
endpoint before its pair is oriented. These are proof-boundary controls,
not a replacement for the unbounded arithmetic argument.

The joint abstract theorem is sound under the explicit full-anchor
hypotheses and can in principle supply the missing A sign before the
t/F bootstrap. The fallback positive-A theorem remains independently
valid. Neither variant has a materialized successor source or metrics.
