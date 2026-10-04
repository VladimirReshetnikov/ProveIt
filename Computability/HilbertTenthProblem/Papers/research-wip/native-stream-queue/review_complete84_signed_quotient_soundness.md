# Independent review: signed auxiliary quotient recovers positivity

PASS, with no requested correction. On the full valid inherited compiler-numeral slice, the frozen proof establishes that every complete84 integer zero with only `auxiliary_quotient` T allowed signed has T>0. This restores the original positive tuple itself, not merely an accepted input with different witnesses. The consequent signed-f positivity statement, when T remains positive, also follows.

Author files reviewed:

- `complete84_signed_quotient_soundness_scout.md`: `b2f1c37ebf68216e657006acaebbac0b27faedb325e1603983786085d580f44a`.
- Its provenance/source-binding JSON: `0e31841fce2a8db87c930c8f5fcfeeab3e3761547897c218d2c964e1dab906cf`.
- Actual complete84 JSON: `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`.

Fresh reviewer metadata receipt: `review_complete84_signed_quotient_soundness.json`, SHA256 `2551ffd6511d2e39254bed4c2f44ec270e71123ea5485389176cff37c59205a9`. It authenticates all twelve source/proof dependencies, all author-declared span hashes and all 63 selected literal bindings against the untouched actual84 array. Authentication of a declared span is not a claim that I read its body. No predecessor program was executed/imported; only a new metadata/row-comparison script ran.

## Mathematical challenge

The dependency order is sound. The accepted signed-T argument first supplies positive f, normalized units, odd R, the actual first/main indices, `Rc|m`, the large moduli, and the asymmetric outer bounds. None of the new steps invokes the positive-T parent before proving T>0.

I independently rederived the lower ratio from the elementary psi bounds: the denominator contributes `(1+1/(2XY²))^r` and the numerator contributes `(1+3/(2a))^(2r)`. The strict comparison follows from `6XY²>a`. Together with the literal ratio interval this gives `a>X^(r+1)/3`, enough for exact `X=2^R` from the main-root congruence. It needs X>=q>=16 and Y>=q³, not the old stronger lower scale on X and not odd r.

Only afterward is the upper error sharpened. Dropping the positive lower-denominator correction gives `c/k0<=xi*(1+2/a)^(2r)`. The geometric bound then gives the stated error below one half. The binomial fractional tail is below one quarter, so its half plus the ratio error is below one. Thus Y=M/2 and the exact central-binomial valuation follow without using R modulo4 or an auxiliary-root sign.

The population argument consequently yields the actual shifted AND masks. The fixed mask's low residue is essential: `MC≡2 (mod4)` and `J≡1 (mod4)` give `TC≡3 (mod4)`, hence `Z≡1 (mod4)` and then `R≡3 (mod4)` from the literal packed-index formula. This uses the valid compiler recipe. It is not justified for arbitrary positive numeral assignments.

For the auxiliary step I checked the stronger plus-sign chi step-down, including the modulus4m. It yields `ell=epsilon R+2mz`. Keeping both original unsquared congruences produces the two ordinary sign equations with exponents `r+mz` and `r+(m+1)z`. The strict bounds c>2R and f>2c exclude residue collisions; their quotient forces z even, for either epsilon. Therefore `e*(-1)^r=-1`; the independently obtained odd r forces e=+1. The literal equality `cTf=V+c+Rf²` now proves T>0.

The input audit is independently consistent: the signed-domain bound j<R<A0 distinguishes the odd and even psi representatives modulo Delta, forcing j=u. The recovered power satisfies `2^u<X<a`; together with the initially signed bound |W|<q this makes the exponent congruence exact and proves W>0. The full historical compiler is still an inherited theorem; no fresh full compiler certification is claimed.

Finally the actual f consumers are precisely f² and Tf. Simultaneously negating f,T leaves every computed value unchanged. A negative f with positive T would therefore produce a positive-f, negative-T zero, excluded above. The f=0 sector is independently excluded by the normalized strong factor being unable to equal a unit.

## Review limits

I read the complete new proof, complete signed-quotient absorption proof, half-binomial42 kernel, modified75 compiler, and normalized85 independent mathematical review; I also read fixed-minus parity lines18–185, fixed76 lines1–170, and all84 literal rows. The receipt records this scope separately from dependency authentication. No large native fixture, compiler execution, proof-assistant certification, new arithmetic count or theorem about additional signed coordinates is supplied by this review. In particular, a later root-elimination source needs its own algebraic and integer-domain inverse proof.
