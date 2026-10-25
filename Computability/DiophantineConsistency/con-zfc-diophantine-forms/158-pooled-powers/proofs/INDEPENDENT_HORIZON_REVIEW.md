# Independent review of the strict-horizon reduction

Reviewer: a separate AI-assisted mathematics agent, 25 October 2026.
This is an internal mathematical audit, not external peer review or a checked
Lean/Rocq theorem.

## Verdict

The transformation from the pinned Joint_Norm P245 polynomial to the proposed
P241 polynomial is mathematically sound, provided the proof includes the
adjusted bootstrap estimates below and recompiles the parent boundary exactly
as in `code/strict_horizon.py` (the packaged version of the audited transform). It tightens the four schema-parameter
and one derived-label local ranges from at most t to strictly below t. It is
not a bijection of the old and new zero sets. Completeness uses a larger
cofinal horizon when necessary.

## 1. Exact semantic change

The altered rows are precisely the four parameter digit rows and the single
derived-label digit row. They use q^t in place of q^(t+1), so the binomial
divisibilities become N | binom(A,t). The natural range decoding gives the
strict inequality A_local<t. Every other range, numerator power, actual local
Horn polynomial, code constructor, carrier F=t!, factorial digit, and proof
calibration stays at the same semantic value.

The shared q^t denominator already exists for the exact factorial binomial.
Redirecting all five rows to its existing normalization ratio removes the
separate q^(t+1) power output, its private power quotient, the private
discriminant product used solely for the one-step Pell power recurrence, and
the old normalization ratio. These are four integer coordinates and three
quadratic residual rows. Removing the deleted output's square from the frame
does not invalidate a bound used by any remaining power request.

## 2. Bootstrap repair is required and available

The parent used q^(t+1)|q^x to infer x>=t+1. The new system retains q^t|q^x;
after the same initial proof of |q|>=2, it gives x>=t. Since t>=16, all margins
needed by the signed factorial bootstrap still hold.

Let b=|B|, Q=|q|, and V=(F^2+1)^t. The rounded-ceiling part still proves b>=2,
|F|<b, and V<b^2 before any factorial interpretation.

For F!=0, the low-coefficient bound is unchanged. Its normalized-tail bound is

    V/(Q-1) < 2/b^(x-2) <= 2/2^14 = 1/8192 < 1/32.

Moreover b+binom(F^2+t,t)<b+b^2<b^x<=Q, so the centered congruence still
identifies B with the positive exact binomial rather than merely its residue.

For F=0, one must retain the parent's separate argument: V=1, s=-1, and b>=3.
Now Q>=3^t, hence

    2^t/(Q-1) < 2^(t+1)/3^t = 2*(2/3)^t < 1/32.

The final strict inequality holds already at t=16: 32*2^17=4,194,304 is less
than 3^16=43,046,721. Increasing t multiplies the bound by 2/3. Thus centered
recovery gives B=1, contradicting b>=3, exactly as required. The parent's
factorial fixed-point argument then applies without further changes.

All requested CRT-exponent signs are recovered because |q+1|>=2^16-1>=2.
The shared frame, signed Pell classification and squared semantic anchor do
not rely on the deleted power output. No principal Pell pair was deleted;
only a derived t+1 power request and its private auxiliaries disappeared.

## 3. Completeness is cofinal, not circular

Start from a fixed finite C222 refutation tree. Its proof labels and the
values of every schema parameter a,b,c,d in each chosen local branch are
fixed natural integers. The derived-label polynomial J depends only on those
schema parameters and the fixed code constructors. In particular it does
not depend on the factorial F, the pending-multiset accumulator, the beta
base y, the global beta code x, or the radix q.

Choose t=16+z^2 strictly larger than the finite proof-trace length, all these
schema parameters, all their J values, and the J value of the all-zero
truth-padding tuple. Cofinality of 16+z^2 guarantees such t in elementary
arithmetic. Only then define F=t!, build the pending-multiset accumulators,
choose the beta parameters, and perform the inherited precision-2x CRT lift.

Accumulator coordinates S,Sp and beta quotients u,vq may grow with F, but
their bounds are respectively y+1 and x, not the tightened t bound. Thus
their growth creates no circular requirement on t. All newly strict local
range residues are already smaller than t before the later CRT construction.
The original binomial valuation argument, with lower index t rather than
t+1, applies with at least the old precision margin.

The anchor construction also survives. It enlarges one encoded CRT
representative within its permitted residue class so that the derived index
h is even and dominates all other requested indices. It does not assert that
the huge *encoded* value h is below t: only each decoded local J value is
below t. Keeping these two uses of the derived-label expression distinct is
essential. Removing one power request cannot create a new domination
requirement.

## 4. Formalization boundary

The proof is ordinary arithmetic plus the retained explicit C222/ZF and
ZF/ZFC refutation calibration. Every new argument uses finite coding,
integer arithmetic, elementary estimates, and the inherited explicit
number-theoretic theorems, hence is formalizable in ZFC. No new object-level
ZFC proof term or end-to-end Lean/Rocq build was supplied by this audit.
The finite coefficient verification is a separate check of the emitted
polynomial, not evidence deciding whether it has a zero.

## 5. The linear-beta companion

The further replacement y=V-1 for y=V(V-1), with V=(F^2+1)^t, is sound after
the strict horizon has been chosen. This does not change a needed early
bootstrap hypothesis: before factorial recovery the signed frame uses y only
through its square, while the power-pool/denominator argument supplies the
large radix independently. The endpoint inequalities requiring y>F+2 are
used only after F=t! has already been recovered. At that point V-1>F+2.

For constructive completeness, if the fixed proof trace has L real steps and
t>L, the pending multiset in the standard reverse proof-tree expansion has
at most L+1<=t entries at every step. Every proof label n is below t and
F=t!>=t, so its weight 1+Fn is strictly below F^2+1. Hence every accumulator
state S is strictly below (F^2+1)^t=V, including the empty product 1; therefore
S<=V-1=y. Also F divides V-1, which gives the same coprime beta moduli as
before. Truth padding preserves the pending accumulator and creates no new
label or size requirement.

The coordinate-level edit is exact. In the pinned P245 variables, X2 is
actual y+1 and X6 is actual V. The old row

    -1+X2+X6-X6^2=0

expresses y=V(V-1). Its replacement X2-X6=0 expresses y=V-1. Eliminating X2
by the monic equality is an integral substitution. In the square frame it
simply replaces the old (y+1)^2 atom with another V^2 atom; all actual power
bases, outputs, and indices remain individually square bounded by W.
