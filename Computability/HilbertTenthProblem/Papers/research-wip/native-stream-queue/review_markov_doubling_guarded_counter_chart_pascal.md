# Pascal review of the guarded doubling counter chart

**PASS for the corrected fixed-chart theorem and inherited paid interfaces.** One scope finding is retained below as numbered Review remark 1 and in the corrected author's Remark 2. The explicit masks, operator actions, positive-integer guards, denominator statement and operation ledgers pass independent mathematical review.

## 1. Frozen versions and exact read scope

| Material | SHA-256 |
|---|---|
| /tmp/markov_doubling_guarded_counter_chart.md | 501f0d1abe19fc43ef4870b2f3ea6f451436d40de0c57519f64c5cba8e7b921d |
| /tmp/markov_doubling_guarded_counter_chart.json | 395a41413cb8db9122f3b76e2e80cd06229765574b176a81cee09c3230705301 |
| Superseded markov_doubling_guarded_zero_decrement.md | f2e1a56a8acf047774e8c5280ec8029616038e5dfc4f4d04bc99154786623f9c |
| Superseded markov_doubling_guarded_zero_decrement.json | 557af1f28780c291c9e910ba12d51df7f002c91ba10240f2c07f99b9510a50f7 |

I read the complete original 200-line note, the complete correction diff and its added eight-line remark, and the complete new metadata receipt. The corrected 208-line proof differs only in the opening chart qualification, the Section 3 heading, and the retained numbered correction. I authenticated both original and replacement byte pins after recovery; no original repository artifact was changed by this review.

For the charged arithmetic I read all of markov_positive_guard_savings.md, SHA-256 901accac868c13967883c56ff5b5a949ef42fcfd82a470999f042272ead8dc15, and lines 1–106 of markov_projective_counter_step.md, SHA-256 01003a2063d442fa71d4a5e80dfd8218edb7940c22fcc90d6b847079fd63a5d2. I also read the full all-scale fixed-point obstruction, SHA-256 4d3393be942ad20441f49c4846f9eba7e328d9b065fc88c2d2c73e2bfa36f1fb. These WIP notes were read as inert mathematical text; none of their helpers or arrays was evaluated.

## 2. Masks, basis and admissible branches

The masks contain only odd nonconstant frequencies and are therefore normalized at doubling. For decrement, the exact numerator is

    9*a_D=9+16t-8t^3,   -1<=t<=1.

The endpoint magnitude of the odd part is 8. Its interior extreme magnitude has square 2048/27<81. Hence a_D is strictly positive; the zero mask is at least 1/3.

Direct coefficient calculation gives the physical sine matrices

    T_D: [[2/3,1],[-1/9,0]],
    T_Z: [[1/3,1],[0,0]].

For f=3s1-s2 and g=-3s1, these become D/3 and diag(0,1)/3. Thus c*f+g decrements correctly for c>=1, while the zero mask preserves only the admitted c=0 line up to scale. Its off-line action resets c illegally, so the zero guard remains necessary.

The positive-hat chart is C=c+1, and a raw representative is (X-H)f+H*g with X/H=C. Applying the masks on their permitted branches gives exactly

    DEC: 3X'=X-H, 3H'=H;
    ZERO with X=H: 3X'=H, 3H'=H.

The note correctly distinguishes signed coordinate functions from probability densities and does not infer integral ratios from arbitrary positive supplied X,H.

## 3. Increment obstruction and the retained finding

Every normalized doubling mask sends s2 to s1. Hence T_a(f+g)=g/3. A full increment in this same fixed chart would instead require T_a(f+g)=nu*(2f+g), incompatible with independent f,g for nu>0.

The all-integer-state projective extension is also correct. Two state vectors span the coordinate space; if all their images stay on target rays, the operator has a matrix [[p,q],[r,s]] there. The identity

    p*c+q=(r*c+s)*(c+1)

for every nonnegative integer c forces r=0 and p=q=s>0. State-dependent positive scales therefore collapse to the already excluded constant-scale full increment, provided the chart itself remains fixed.

**Review remark 1 (false basis-independent reading, retained with counterexample).** The superseded opening said: “A full positive increment is impossible on the same two-sine space, at any action scale.” Read as an assertion independent of the counter chart, this is false. On the same abstract space replace the basis by F=-f,G=g. The existing positive decrement mask then satisfies

    T_D F=F/3,  T_D G=(G+F)/3,

which is a scaled full increment in that new basis. The counter orientation and its nonnegative ray have changed. The correct theorem fixes the states c*f+g and their chart, as its explicit equations already did. The replacement opening and heading now state this qualification, and the author's numbered Remark 2 retains the original broader wording and this counterexample. No branch equation, mask, denominator computation or ledger needed correction.

## 4. Exact scope of the denominator minimum

For f_lambda=s1-lambda*s2 and g_lambda=-s1, the required physical matrix is [[2lambda,1],[-lambda^2,0]]. Its action on s1 uniquely determines the continuous normalized mask:

    a_D(lambda)=1+2*(2lambda-lambda^2)*cos(theta)
                   -2lambda^2*cos(3theta).

The division used in this uniqueness argument is only away from the finite zero set of sin(theta); continuity determines the values there. It rules out repairs using non-even or higher-frequency continuous masks for that exact action.

At lambda=1/q and cos(theta)=-1/2 the value is 1-2/q-1/q^2. It is negative for q=1,2; q=3 has the strictly positive construction already checked. Thus reciprocal integer action denominator three is minimal in the specified two-sine Jordan family. This does not assert a global denominator optimum over coordinate encodings. The actual Fourier-coefficient denominator of the displayed decrement mask is nine.

## 5. Paid integer schedules and history limits

I checked the transfer to q=3 against the unrestricted positive-integer proofs of the frozen guard note. With t=B-2 and u=C-1, the direct residuals t*u and C'-u+t force exactly ZERO or DEC by positivity and integrality. For raw coordinates, the three residuals

    t*(X-H), 3X'-(X-H)+t*H, 3H'-H

force the same guarded ratio actions. Endpoint links or the paid integral initialization remain necessary. The raw affine expression agrees with the reset mask only on its guarded zero branch; the corrected note does not claim an off-branch polynomial identity.

The full inherited SOS counts and witness interfaces check:

| Interface | M | A | Total | Positive witnesses |
|---|---:|---:|---:|---:|
| Direct local, supplied C,C' | 3 | 5 | 8 | 1 |
| Raw ratio local, supplied X,H,X',H' | 7 | 7 | 14 | 1 |
| Linked raw local, supplied C,C' | 11 | 11 | 22 | 5 |
| Direct fixed T>=1 | 3T+1 | 6T | 9T+1 | 2T |
| Raw fixed T>=1 | 7T+2 | 8T | 15T+2 | 3T+1 |

Multiplication by fixed numeral three remains paid. The fixed-duration proofs include ordinary positive input x, its initialization, all guards and selectors, and the endpoint. Their language is exactly x<=T. Raw completeness uses H_0=3^T*H_T as a witness-existence formula at fixed T, not an emitted variable-duration power primitive. The inherited local/direct-history degree is four and raw-history degree is six; substituting q=3 does not remove their leading guard terms.

The optional physical coefficient conversion is also exact: u=X-H, v=u-H, A=3v, Bcoef=-u gives A*s1+Bcoef*s2 in 1M+3A. This separate producer is neither a sine-evaluation primitive nor silently included for free in the chart-coordinate counts.

These are checked all-size template consequences. No new q=3 source array was emitted or evaluated in this review, and the author makes no such claim. No integer gate count improves merely by changing the operator representation.

## 6. Final boundary

The corrected note supplies a finite guarded ZERO/DEC operator representation and a precise inherited integer interface. It supplies neither both counter directions in one fixed chart nor a universal program, fixed-arity unbounded history, or smaller Diophantine compiler.

Only inert text, exact symbolic reasoning, a read-only correction diff and ordinary byte hashes were used. No supplied, archived, copied, committed, frozen, author or predecessor helper/program, source array or builder was executed or imported. No numerical search, repository edit or Git mutation occurred.
