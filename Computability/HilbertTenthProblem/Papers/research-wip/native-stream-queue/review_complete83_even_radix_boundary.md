# Independent review of the even-radix boundary

**PASS in the stated scope; no correction requested.** I read the complete author proof, helper and receipt, authenticated the unchanged complete83 source, and independently checked the new arithmetic and positive completion. The theorem establishes even q and a four-term reformulation of the cubed scale on valid compiler slices. Its q=76 construction establishes a full positive zero only for the displayed diagnostic scalar numerals. It does not establish a valid-program counterexample or universality below84.

The frozen author pins are:

| File | SHA-256 |
|---|---|
| `complete83_even_radix_boundary.py` | `b469fb611d4b020fab1cdd5d4946ec1b56d81f1f8682cc3e9a4a7210d9eeef89` |
| `complete83_even_radix_boundary.json` | `68ab9c241c7b8f6e610f1eae697558938630d25b7cdaffff8b17196c9c5fbc0a` |
| `complete83_even_radix_boundary.md` | `eba3e2944154dd7ff28e5b20d5e32e8ee6a0138b515c8e5f3846979dadaaa8dc` |

## Proof and source interface

The parity argument has no premature binary-decoding assumption. On a valid compiler slice, B is even. If q=(B−1)J+1 were odd, J would be even, so both summands in the literal packed R expression would be even. This contradicts the accepted pretyping result R=3 mod4. Thus q and X=wq are even.

The exact offset identity and the independent pretyping bounds u<2q, |W|<q and R>3q+1 imply X>2^(R−1). The strict first/main Pell estimates can therefore be reused without assuming X=2^R: their upper-error hypothesis is established by the preceding lower estimate a>X^(r+1)/3>8r. The lower binomial tail is less than1/2, the upper Pell error is less than1/2, and the central coefficient plus the even-X terms make M even. Consequently both strict unit intervals have the same integer endpoint Y=M/2. No population threshold or native mask is needed.

For j>=4, X^j is divisible by q^4, hence by2q^3 because q is even. This proves the exact four-term equivalence. It is a reformulation of one necessary scale condition, not a complete certificate by itself.

I checked the displayed q, X, Y, packed-index, transport and shared-root interfaces against the inert source receipt, SHA `dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c`. My helper guards22 literal definitions. This review does not redo the predecessor's whole-source count/liveness/degree audit or evaluate its DAG. The accepted shared-projection mathematical note (`1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c`), its independent review (`8ed2a92dfdc4a8a4c799cdef86adda5af467050704eaefc451eea14ffbed80bb`), and half-binomial42 §5 (`0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992`) were read inertly for the inherited index/offset and quantitative ratio premises. The normalized rank and compiler proofs behind those accepted premises are inherited, not newly certified here.

## Diagnostic and all positive witnesses

Independent small arithmetic gives q=76, C=1, W=−28, u=9, R=30562815 and r=15281407. Modular lifting modulo5700 gives X=4028 and w=53 mod75, so the positive transport quotient (w+97)/75 is integral and its factor is one. Independent factorial valuations and base-2/base-19 Kummer carry counts both give

```
v2(C_0,C_1,C_2,C_3)=(16,8,9,8),
v19(C_0,C_1,C_2,C_3)=(3,3,3,3).
```

Thus each of the first four coefficients is divisible by2q^3; the tail is also divisible by that modulus. This establishes positive integral s=Y/q^3. The failed native AND values4 and2 are correctly retained as diagnostics and not treated as valid-program evidence.

The proof supplies every remaining positive witness, rather than only a main/input subsystem. At the constructed X,Y, the strict Pell sandwich gives positive eta and zeta. Their sum is k. The recurrence at P=1 modulo E gives E dividing k−R−1, and strict growth gives positive h. The odd discriminant residue and growth similarly give positive integral delta.

For the changed root equations, U=E_9+28 is positive. The sequence E_j/2^j is strictly increasing from j=1 onward: its scaled recurrence gives `F_(j+1)=A F_j−F_(j−1)/4`, with F_0=F_1=1 and A>2. Therefore E_j−2^j is strictly increasing for j>=2. This proves the positivity of

```
sigma=((E_R−2^R)−(E_9−512))/H.
```

The congruence E_j=2^j modH proves integrality. Substituting X=2^R−540 and W=−28 restores both literal roots exactly. Also U=540 modH with H>540, so H does not divide U.

The auxiliary completion is valid at these newly constructed Pell parameters. Writing m=2cR, the multiple-index identity `psi_A(m)=c psi_D(2c)`, together with D^2−1=Delta*c^2, shows c^2 divides psi_A(m). This makes i positive integral. The strong norm yields S^2=Delta*(f^2−1), f^2=1 modc and gcd(c,f)=1. The odd auxiliary index makes V=chi_S(R)/S integral; r odd gives V=−R modc and V=−c modf. Consequently cf divides V+c+Rf^2 and the resulting T is positive. These are the actual auxiliary quotient and norm equations. First, main, input, index, transport, auxiliary and normalized strong factors are all one, hence the scaled83 output is zero.

This is a complete parametric existence argument for the18 supplied witnesses. Neither the author nor this reviewer materialized Y, c, f or the resulting huge tuple. The displayed fixed numerals are explicitly outside the certified universal-compiler claim, so this construction does not conflict with the separate valid-layout dyadic negative-branch exclusion.

## Fresh independent evidence

Only the new reviewer helper was executed. No author or predecessor helper, supplied archive program, copied predecessor program, or build was run or imported. The new checker authenticates the author bytes and source receipt, guards22 literal interface producers, independently recomputes the diagnostic residues and both valuations, compares complete sums to cubic truncations in3,920 small cases, and checks120 odd-q parity instances. Its direct comb/pow modular sums and Kummer carry counts supplement the mathematical proof; they are not native acceptance tests.

Fresh normal and optimized Python (`-O`) exact receipt replays from `/` both pass. Frozen reviewer companions:

* PY `da2b8f8a4faf091bc9ca45fe5d8b9d9e7643bbab26e544399d047074ca646f4b`.
* JSON `f8a6becd3d7567d745f1b3c524aff462cec5093b4063ab4c3d65403934c5cf8e`.

The remaining boundary is actual fixed-program soundness in the surviving even-q, nonzero-offset sector. No claimed operation improvement follows from this review.
