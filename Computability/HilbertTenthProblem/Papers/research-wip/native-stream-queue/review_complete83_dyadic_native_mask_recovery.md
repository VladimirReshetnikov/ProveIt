# Independent review: dyadic native-mask recovery for shared-projection83

PASS for the stated conditional theorem; no author correction is requested. On a valid inherited modified-compiler slice, a positive shared-projection83 zero with dyadic `q` and `W=0` has the exact population and native mask conditions. This does **not** establish dyadicness at all zeros, decode the two-rotation difference as a computation, or prove universal83.

The complete author proof and helper were read inertly. Frozen author pins:

- `/tmp/complete83_dyadic_native_mask_recovery.md`: `6fc07e4989926e868587cc43a4140c8534cde57358859dfe940b9151be21ac94`.
- `.json`: `f094621d6314b1297c5317398c5dbac2de3980a57b039f0db1aa8f6187860469`.
- `.py`: `4ea248a62a3866c2b30a51ba282fda198e2663b323eae0eb384bd77714eaeaeb`.

No author or predecessor helper was executed/imported. I wrote a separate standard-library checker.

## Source and premise binding

Read scope includes the actual83-row JSON array; the complete shared-projection offset and even-radix notes; the negative-offset pretyping/layout/low-residue interface; the complete modified75 compiler note; complete76 §1 and complete78 §§1–3; and transport-shear §1. Prior Pell classification and quantitative ratio recovery remain accepted dependencies, not newly certified ancestor theorems.

I also read the actual compiler code inertly: modified75 `compile_windows`, `new_constants` and relevant layout guards; complete76's compiler construction; complete77's Start/End export; complete78's numerical-property definitions; and the modified75 source alias. They bind the required facts:

- `B=V0^L`, `d=bL`, with `b,L` powers of five, and modified radix target `V0>=4(K+2)(2 sum c_e+6)+8`. Thus `b>=5`, `V0>=32`.
- The baseline `MC` excludes End position1 from the permitted positions; the modification subtracts exactly `2 V0^e_*`. Consequently `Dmask=B−1−MC` has ordinary digits at most1 and the single dummy digit3.
- All baseline field-mask exponents are positive. The exporter adds exactly4, so the **native** `MF0≡4 mod V0`. The source uses `MF=MF0+B−1`. Neither is silently replaced by the cached baseline mask.
- `DR=V0^Hlayout` with `Hlayout>1`, and all `DC` exponents are positive. The optional high monomial is included, and `L>g+Emax` bounds the full unshifted product degree.

The independent checker recounts all83 rows as46M+37A with18 supplied witnesses and checks acyclicity. It expands the complete26-row ancestor set of eight actual outer registers into exact integer polynomials: `q,X,Y,C,W,u,R` and the transport factor. It does not numerically evaluate the inherited native DAG. The strict-positive witness domain, six fixed numeral ports and unresolved universal-language status remain unchanged. Degree187 is inherited, not re-proved.

Global pretyping supplies `C>=0`. The stronger `C>0` used here is justified on the declared `W=0` branch by `C=Z>0`; no stronger global pretyping assertion is needed.

## Valuations for every admissible u

Dyadic repunit divisibility gives `t=dN`. Since `R>t`, divisibility of `X=2^R−2^u` by `q=2^t` forces `u>=t`. Then `u−t=d(2x−N)+b`, with `0<b<d`, gives `u>=t+b`. This uses the actual `2d` and `b` ports, not an arbitrary scalar slice.

Write `p=pc(r)`, `k=v2(r+1)`, `l=v2(r+3)`, `h2=v2(r−1)`. For odd `r>=3`, the four adjacent binomial valuations follow from the central identity and exact consecutive ratios. Assume `p<3t+1`.

If `k=1`, then `h2,l>=2`. The low `l` bits of `r` are those of `2^l−3`, so `l<=p+1`. The weighted cubic term has valuation at least `3u+h2−2>=3u>p`; the first two noncentral terms also exceed `p`. The central term is uniquely least.

If `k>=2`, then `h2=l=1`. When `k<u` the central term is uniquely least. When `k>u` the linear term is uniquely least, at valuation below `p<3t+1`. These exhaust arbitrary admissible `u`; no finite-range assumption is needed. The tied case `k=u` is deliberately not dismissed by this argument.

All terms of index at least4 vanish modulo `2^(3t+1)` because `u>=t+b`, and `R>3t+1` permits replacing `X` by `−2^u`. Thus any low-population escape must satisfy `k=u`.

## Exceptional case and the no-borrow challenge

The remaining steps are sound before typing any supplied word:

1. The literal index modulo `q` is `Z−Dmask J−1`. With `v2(R+1)=u+1>t`, it forces `Z=Dmask J`: both representatives lie strictly between0 and `q`. Therefore `C=Z`.
2. The literal transport equation, using its already established positive unit sign, factors by `J` after `q−1=(B−1)J`. Hence `F=fcell J` for a positive integer. The raw bound yields `fcell+2Dmask<B−1`, thus `0<fcell<B−1`. No field-mask premise is used.
3. Modulo `B−1`, transport gives `fcell≡(DC+DR+2^R−V0)Dmask`. This uses `wq=X`, `q≡1`, and `u≡b mod d`, without assuming whole-cell temporal alignment.
4. Direct expansion gives `R+1=q[q^3−q^2F−qZ+(fcell+MF0)J]`. The bracket is divisible by `2^(u+1−t)`, hence by `V0`. Its first three terms are divisible by `V0`, and `J` is odd. Thus `fcell≡−MF0≡V0−4 mod V0`. The **+4** modification is essential; merely knowing a binary valuation would not suffice.

The checker independently proves this factorization, the shifted-packing difference, the low-residue quotient and the transport-`J` factor identity as exact polynomials, not numerical fingerprints.

For the competing representative, `G=(DC+DR)Dmask` is the actual nonnegative coefficient string for a repeated permitted cell. Its coefficients are at most `V0/4−2` and its degree is below `L`, including the optional high monomial. A cyclic binary rotation `Yrot` has digits at most `3V0/4`, or at most `V0/2+1` in the spill case. Therefore `Tplus=G+Yrot` is carry-free with digits at most `V0−2`; in particular `0<Tplus<B−1`.

The subtraction need **not** be borrow-free. Since `DR>V0`, the integer `Tactual=(DC+DR−V0)Dmask+Yrot` is positive, and `Tactual<Tplus<B−1`. It has the same congruence as `fcell`, so uniqueness in this interval gives equality. Reduction modulo `V0` removes both fixed unshifted terms even if internal subtraction borrows occur. The unit digit is that of `Yrot`, at most `3V0/4<V0−4` for `V0>=32`. This contradicts the forced congruence and excludes the tied case on the actual compiler slice.

## Population equality and the unresolved boundary

The inverse-population lemma gives `pc(R)<=3t+2`. In the no-overflow case equality is precisely absence of binary carries; overflow strictly loses population. The valuation argument forces `pc(r)=3t+1`, hence equality and both asserted AND conditions.

The origin bit in the low mask makes `Z−1` even. Adding1 inserts exactly Start without a carry; End stays absent in every cell. Because `C=Z`, it also lacks End. This is not yet a decoded-history contradiction: the transport multiplier is a difference of two rotations, and the old one-rotation synchronization/marker proof has not been established for it. The open ordinary-input boundary is correctly retained.

## Fresh evidence and limitations

The independent checker produced:

- 292,571 exact nonexception binomial/cubic-residue cases, covering both denominator patterns and both sides of `k=u`, plus seven tied cases retained as ties.
- 7,942 synthetic rotation/transport cases, including **6,690 with internal subtraction borrows**, all satisfying the representative/low-digit inequalities.
- 21,336 exhaustive inverse-population cases through seven-bit blocks, including boundaries and overflow.
- The source recount, eight full outer polynomial expansions, four exact formal identities, eight predecessor byte pins and five compiler-code pins.

Synthetic words are not asserted to be emitted universal-compiler layouts. No enormous Pell tuple, actual computation or full positive zero was materialized. Finite evidence corroborates the elementary proofs; it does not replace their quantified arguments.

Fresh normal-Python generation and optimized-Python exact receipt comparison both passed from `/`. Only the newly authored independent checker ran; no predecessor helper, including the frozen author helper, was executed/imported. No repository file was changed.

Independent frozen artifacts:

- `/tmp/review_complete83_dyadic_native_mask_recovery.py`: `79795f4ce899cf209ccf2b4ae16e0f06268d8fc4d1b89722d4a45d72c34a1845`.
- `/tmp/review_complete83_dyadic_native_mask_recovery.json`: `20c4723b408bafe137b6ff2f20c8f5a04ab741c11582d598f8895bb4036c6ef1`.

The conclusion is conditional native-mask recovery, with no new source, witness saving, arithmetic saving or universal83 claim.
