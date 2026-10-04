# Independent review of strong-root polynomial absorption

**PASS. No correction requested.** For the stated fixed compiler slice and
fixed integer polynomial G in the85 auxiliary-independent values, every
positive zero after substituting f=G satisfies

    G!=0,       2d*x+b<R<c<4*deg(G)+ceil(log2(max(1,||G||_1))).

The full ordinary-input projection is therefore finite, including when G
takes negative values. This is a substitution obstruction, not a new paid
circuit or a global circuit lower bound.

## Frozen subject and exact read scope

| File | SHA-256 |
|---|---|
| `complete84_strong_root_absorption.py` | `3d17fb1bdf7e3942bedcc873ee87a244ef66aa1188eaafb732828965ebfc670c` |
| `complete84_strong_root_absorption.json` | `424ba5aaa6e1ebc8525e4eaaaca7f7489282c7533d775dac86d10a659684986a` |
| `complete84_strong_root_absorption.md` | `b73fb50aebb8de23a282aff91c389d74b4bd96dadd355c43eb7e7783c1b6abc2` |
| `review_complete84_strong_root_absorption.py` | `3fa3e0425417e9b92a04715512523cfdff36b1cff46c1d16b1245d2e42b1d02a` |
| `review_complete84_strong_root_absorption.json` | `bbaa398335eb798dc124b5150873e4237f969a2ae05903c914fc934d4e544c7f` |

I read the complete new proof and helper and compared its84-row source,
census and factor claims with the authenticated actual source. The entire
signed-quotient theorem and its normalized-rank dependency were independently
reviewed immediately beforehand in
`review_complete84_signed_quotient_absorption.md`. Its direct signed-domain
conclusions are the inherited premises used here. All nine new declared
dependencies are authenticated; no frozen author or predecessor program was
executed or imported in this review.

## Quantified proof challenge

The use of the stronger rank condition is correct. In the signed-quotient
domain, c=psi_R(A0), f=chi_m(A0) and R*c divides m. Therefore monotonicity
and Pell-unit composition give

    f>=chi_(R*c)(A0)=chi_c(D),       D=chi_R(A0).

The main norm with Delta>1 gives D>c. Since c>=2, the even binomial
expansion of chi_c(D) has D^c and a strictly positive term at exponent2
of the square-root factor. Thus f>c^c for **every** allowed strong completion.
No least-index or canonical auxiliary choice is assumed. The variable
exponent is used as a mathematical estimate, not as a free source operation.

The signed substitution map has the precise needed domain. The only direct
f consumers are f² and T*f, and the latter is the only direct T consumer.
Simultaneously reversing f,T preserves these values and the complete
polynomial. Every argument of G is independent of all four auxiliary ports.
For nonzero g, replacing (g,T) by (|g|,sign(g)*T) leaves those arguments
unchanged and gives a zero with positive f and unrestricted integer T.
This is exactly the previously proved signed-quotient domain. It does not
claim positive T after the map or an inverse to the positive-T compiler.

Consequently |g|>c^c and every argument has absolute value<c^4. Dependencies
among the85 arguments do not invalidate the coefficient-norm estimate
|g|<=L*c^(4t). For s=ceil(log2 L), c>=4t+s would give
c^(c−4t)>=2^s>=L, contradicting strict growth. The strict endpoint c<4t+s
is therefore correct, including L=1 and degree0. The inherited
2d*x+b<R<c then makes the ordinary-input projection finite on each fixed
slice. The theorem fixes G and its coefficients while input and witnesses
vary; no varying-degree or rational-substitution conclusion is inferred.

The zero-value sector is excluded before this map or any index recovery.
At f=0, V=−c and S²=Delta²*i²*c⁴. Exact expansion gives

    F84|f=0 = -Delta*(Delta*i²*c⁴*P5*Na0+1),
    Na0=Delta²*i²*c⁴*(c²−y²)+y².

All quantities are integers and Delta>=8 already follows from the unchanged
positive X,Y boundary. The parenthesized expression is1 modulo Delta and
cannot be zero. This covers an identically zero formal G and a nonzero G
that vanishes on its dependent arguments. It does not import any native
conclusion into a zero-f tuple.

## Independent source and arithmetic evidence

The fresh checker authenticates the complete84 source and signed theorem,
recomputes dependencies through all84 rows, and obtains exactly64 computed
plus21 supplied arguments. It checks the two f consumers, sole T consumer,
the positive-discriminant producer chain,25 original free ports and the
unchanged84=47M+37A ledger.

Eight actual auxiliary-independent cuts expose the24 remaining output
ancestors. The independent expansion verifies the full17-term factorization,
simultaneous sign identity, and four-term zero-f contraction, including
disappearance of T. These match the source-specific saved coefficients;
the check does not replace the literal finalizer by an assumed formula.

For bounded corroboration, a separate **closed even-binomial expansion**
constructs chi polynomials, independently of the author's recurrence. It
verifies all36 recorded composition identities through degree36,120 growth
cases and108 coefficient-norm thresholds at both recorded endpoints. These
finite checks support, but do not replace, the quantified proof above.
They are not full native zeros or a generic G compiler.

Fresh normal and optimized runs of the **new independent checker only**
from `/` reproduced the exact review receipt. With the signed dependency
installed and the author trio staged, the commands were:

```sh
python3 /tmp/review_complete84_strong_root_absorption.py \
  --root /absolute/path/to/native-stream-queue --author-root /tmp \
  --expect /tmp/review_complete84_strong_root_absorption.json
python3 -O /tmp/review_complete84_strong_root_absorption.py \
  --root /absolute/path/to/native-stream-queue --author-root /tmp \
  --expect /tmp/review_complete84_strong_root_absorption.json
```

If the signed dependency is also staged, add `--signed-root /tmp`. Both
optional roots default to `--root` after installation. The review does not
reaudit the parent's exact degree or change the complete84 frontier.
