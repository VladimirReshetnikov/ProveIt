# Independent review: exceptional k=0 first-factor branch

The [reviewed audit](../../research/ordinary13-independent-k-exceptional-kzero-audit/README.md) gives a sound standard-integer argument for `F+alpha<q` at a zero of the exact independent-k graph at the specified fixed symbolic tuple, subject to the stated source/tuple interpretation. I found no mathematical mismatch in the factor extraction, exceptional congruence or interval argument. This review does not prove a Lean theorem, any arbitrary-model statement, k>0, eta≤k, an unrestricted zero map, provider compatibility or a PDF binding.

At an integer output zero, the four displayed factors multiply to 1, hence are each ±1. The reviewed checker structurally binds the exact 84-row graph to those factor formulas. Independent enumeration here confirms that none of the four formulas is −1 modulo four, for all 1,600 respective residue assignments. Therefore each factor is +1; the first and main residuals vanish. This is an integer units argument, not an independently checked formal model extraction.

For k≥1, the reviewed earlier first-factor argument gives the gap. For k=0 and a failed gap, the only first-root case is r=0 and `Bt=−(q−1)`. With `d=X+K0` and signed `qF=q−F`, substitution indeed gives `qF(d+1)=alpha*d+1`. The fixed K0 satisfies K0≥7 because `paramKernel rho` includes the nonnegative summand rho³⁰ and rho=2⁶⁷. Thus d≥7; the equality forces qF≥1 and, since alpha is integral, alpha=qF+t with t≥0 and `d*t=qF−1`. F≥1 implies `qF≤q−1=J*beta`, hence `7t< J*beta`.

The exact first/main graph formulas show that J=0 is incompatible with the first residual and that U is a positive multiple of q. The main norm then implies q divides its signed root, and the k=0 root formula reduces this to q dividing `3(R+1)`. No cancellation of 3 is used. In the exceptional case set `u=J*MC+1−t`; the exact rank polynomial has

```
R+1−u = q * (qF*(q²−1) + t*q + J*MF).
```

For the prescribed low mask, the last base-2⁶⁷ digit is 2⁶⁷−1; the stated support and special index place it outside both exceptional cases. This gives `6MC>5beta`, while a lower special digit gives `MC<beta`. The source definitions for `ports K`, `fixedK`, the four symbolic components and both digit/kernel recipes have been checked together, adding tuple-selection links not pinned by the reviewed checker. This checks source recipes; it does not authenticate any compiled provider, historical bytes or displayed PDF.

Because `7t<J*beta` and `3MC−2beta>beta/2`, one has `3t<J(3MC−2beta)`. Therefore `3u>2q`; the strict bound `MC<beta` and t≥0 give `3u<3q`. Thus q cannot divide 3u, contradicting the congruence. This verifies the argument even when 3 divides q and makes no assumption X>0. It says nothing by itself about zeros in the remaining positive-gap k=0 branch.

The receipt reproduces the two author checkers, independently enumerates the four factor residue sets, pins and checks the symbolic tuple/constant source links, and exercises 2,847 exceptional branches and 5,836 rank-interval controls. Finite controls and lexical source checks are not substitutes for a formal arbitrary-model proof. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-independent-k-exceptional-kzero-independent/check.py | cmp - reviews/ordinary13-independent-k-exceptional-kzero-independent/receipt.json
```
