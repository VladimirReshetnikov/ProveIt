# Grill Tag: a positive affine orbit with a paid finite-history projection

This is a new local arithmetic lead, not a new universal operation bound. A Grill Tag macro has a special relation between its output length and content. Changing the content coordinate exposes two affine branches with only one program-dependent coefficient. A terminal history then certifies its own dyadic width. An aggregate equation removes the intermediate content coordinates with an exact positive-zero bijection.

The repository search found no Grill Tag, Genera Tag or BIX Queue scout in the WIP or report TeX. I checked the existing two-stack affine loader, prime-payload residue-affine compiler, binary-tag four-tile history, native dual-rail FIFO and clockwise-CTS initialization obstruction. Those already cover broader queue/counter routes; the mechanism below is the special affine relation of Grill appendants, rather than another generic queue encoding.

## Primary-source status

The source is **ais523's informal creator construction**, not a peer-reviewed universality result. The [original 2023 account](https://codegolf.stackexchange.com/a/265539) gives a finitely initialized two-state, fourteen-symbol TM implementation. The [Grill Tag construction, revision181950](https://esolangs.org/w/index.php?title=Grill_Tag&oldid=181950) reduces a restricted [Genera Tag, revision182460](https://esolangs.org/w/index.php?title=Genera_Tag&oldid=182460), with explicit symbol encodings and cyclic run formulas. Its claimed halting-preserving universality has not been independently established by this scout.

Two source cautions matter. The [creator's correction](https://esolangs.org/w/index.php?title=Talk:Grill_Tag&oldid=181840) confirms that command `11` appends `01`, not `10`. Also, root found an unresolved literal discrepancy: Encoding E says its second grill has `a−2` ones, giving total length `7a+4`, while the displayed length and inverse-generation runs require `a−4`, giving `7a`. Do not silently repair this and call the universal compiler verified. Root's separate `review_grill_encoding_e.md` records a bounded investigation; it is not a dependency of this arithmetic checker. The creator's Perl interpreter/compiler endpoints timed out, so neither was executed.

## Exact transition and positive coordinates

A fixed program is a nonempty finite tuple `(n_0,...,n_{K−1})` of natural numbers. Macro i removes the front bit `d`; if `d=1`, it appends `0(10)^{n_i}`. The phase advances cyclically. Empty queue halts. This is precisely `n_i` copies of command `11` followed by command `10`.

Write the front bit in the least significant position:

```
P=2^length(w),       X=sum_j w_j 2^j,
H_i=4^{n_i},         C_i=2(H_i−1)/3,
```

so the appendant has scale `2H_i` and value `C_i`. Its key identity is `3C_i=2H_i−2`. Ordinary queue arithmetic gives

```
2P' = P + (2H_i−1) P d,
2X' = X − d + C_i P d.
```

Set **Z=P−3X**. The exact replacement is

```
2P' = P + (2H_i−1) P d,
2Z' = Z + P d + 3d,
d(d−1)=0.                                             (1)
```

Thus, on a valid positive code,

```
Z even: (P,Z) -> (P/2,Z/2),
Z odd:  (P,Z) -> (H_i P,(Z+P+3)/2).                    (2)
```

There is only one coefficient depending on the program phase. A generic conditional binary-word append has independent scale/content coefficients. This specialization is the possible packed-compiler saving; the number of commands alone would not establish it.

The positive code cone is `P=2^ell`, `1<=Z<=P`, `Z≡P mod3`. It represents `X=(P−Z)/3`, hence `0<=X<P/3`, with precisely ell bits including high zero padding. It does not represent every binary word at its shortest width: word `1` gives `(P,Z)=(2,−1)`. The creator's proposed Encoding E consists of separated grills and zero runs and lies in this cone under either version of the disputed length; that does not validate the rest of the compilation.

For a nonempty code, P is even. Equation(1) modulo2 forces `d=Z mod2=X mod2`. If d=0 the cone is preserved by halving. If d=1, `P−Z` is a positive odd multiple of3, hence `Z<=P−3`; therefore `0<Z'<=P<=H_iP=P'`. Congruence modulo3 is preserved because `H_i≡1 mod3`. The decoded transition is exactly the macro above. At the empty code `(1,1)`, the second row would say `2Z'=1+4d`, which is impossible for integer Z'. There is no uncharged emptiness-test gadget.

For arbitrary integer coordinates the row identity is exact: if E_P,E_X are the original width/content residuals and E_Z is the replacement, then `E_Z=E_P−3E_X` under `Z=P−3X`. Consequently the SOS difference is `E_P²−6E_P E_X+8E_X²`. This proves a zero-set equivalence under the coordinate change; it is not an off-zero polynomial identity, and positivity is justified separately by the cone.

## The terminal state pays for dyadic width

Assume every state coordinate is strictly positive, use positive head witnesses `D_i=d_i+1`, impose (1), and fix `(P_t,Z_t)=(1,1)`. Backward induction through `P_{i+1}=P_i/2` or `4^{n_i}P_i` proves every P_i is dyadic: its odd part cannot change. No separate power predicate or width exponent witness is needed.

Also `2(P_{i+1}−Z_{i+1})≡P_i−Z_i mod3`, so all code congruences follow backward from the endpoint. This conclusion does not hold for an isolated step: `(P,Z)=(6,3)` to `(6,6)`, with n=0,d=1, satisfies all three local rows but has no dyadic width.

For ordinary positive input x, introduce just a positive initial Z_0 and **define** `P_0=3x+Z_0`. This costs one multiplication and one addition, with no extra equality or positivity condition. The complete terminal history forces P_0 dyadic, so x is exactly the queue's binary content at some width with `P_0>3x`. Forward induction using the initial cone proves that the whole history is genuine, with no earlier empty queue. Conversely any such padded-input halting run has a unique lift at its chosen width and time.

This pays for an actual ordinary-integer input relation, but not yet a universal raw-input decoder: it recognizes whether the fixed Grill program halts on **some zero-padded binary x** satisfying that width constraint. The creator's block encoding of a Genera input is not a proof that one fixed Grill recognizer recognizes every desired recursively enumerable set through this padding convention.

## A complete finite-history reduction

At an externally fixed t, replace all Z-transition rows by

```
2^t = Z_0 + sum_(i<t) 2^i d_i(P_i+3).                 (3)
```

Retain the width rows, Boolean rows, positive initial Z_0 and computed `P_0=3x+Z_0`. Only `P_1,...,P_{t−1}` and the t positive head witnesses remain.

For each k, the prefix numerator

```
A_k=Z_0+sum_(i<k)2^i d_i(P_i+3)
```

is strictly positive. Subtracting the suffix of (3) shows `2^k | A_k`, since all suffix terms and `2^t` are divisible by `2^k`. Thus `Z_k=A_k/2^k` is a uniquely restored positive integer. It satisfies every old Z-row and gives Z_t=1. Conversely telescoping the old rows proves(3). This is a bijection of complete positive zero sets. The proof needs the entire final equality; an endpoint count alone is not substituted for causal content.

The [literal source](grill_tag_affine_scout.py) emits both complete circuits and a [receipt](grill_tag_affine_scout.json), including their input gates and all residuals. Its default finalizer squares the width/content residuals but adds each Boolean factor `B_i=d_i(d_i−1)` directly. Every B_i is nonnegative for integer d_i, so this has exactly the same full integer zero set as the all-squared reference mode. The complete off-zero correction is `F_SOS−F_default=Σ_i(B_i²−B_i)`. It saves t multiplications, with no real-zero equivalence asserted. Constant-only arithmetic and multiplication by0/1 are folded; every emitted register is live. Let `z(t)` be the number of phases with `n_i=0` among the first t macrosteps. In the declared binary `+,-,*` model, with fixed program/horizon numerals free:

| Complete ordinary-x compiler | Multiplications | Add/subtract | Total | Positive witnesses | Residuals |
|---|---:|---:|---:|---:|---:|
| Full P/Z history | `6t+1−z(t)` | `12t−2` | `18t−1−z(t)` | `3t−1` | `3t` |
| Aggregate projection | `6t+1−z(t)` | `9t+1` | `15t+2−z(t)` | `2t` | `2t+1` |

The exact saving between these emitted circuits is **3(t−1) additions**, t−1 positive witnesses and t−1 residuals. Both remain quartic: d is a shifted positive witness, the largest residual degree is two, and a nonzero squared width residual supplies a quartic term; its homogeneous leading square cannot cancel against the other squared quadratic rows or the degree-two Boolean factors. These are literal schedule counts, not optimality claims. For the nonuniversal fixture `(0,1,1)`, horizons1,2,3 give full totals16,34,52 and projected totals16,31,46. The ordinary positive-input relation has no solutions at horizons1 or2; `x=1,Z_0=1,P_0=4` halts in3 macros. Thus the smallest nonempty example saves6 additions, not a claimed universal improvement.

## Evidence and next obligation

The independently written string oracle checks12,282 micro/macro orientations,4,122 arithmetic transitions and10,000 signed row/SOS corrections. The checker evaluates57,344 bounded complete local candidates;24 live complete DAGs cover natural-head fixed-input, positive-head fixed-input, positive ordinary-input and projected forms. It checks90 signed complete finalizer outputs,120 complete signed corrections against the all-squared mode,16 actual positive ordinary-input halting histories and their exact projection/restoration, and2,600 short-horizon candidates. The original example program `(0,1,1)` is a fixture, not an instantiated universal program. No finite test is offered as a universality proof.

The next implementable reduction is to adapt an existing packed affine-history kernel to **one width chronology plus Boolean heads and (3)**, taking advantage of the program-independent Z-row. This still must pay cyclic program-phase certification and the weighted sum `Σ2^i d_iP_i`. A history-dependent dot product cannot be replaced by an ordinary product without a convolution/extraction proof and bounds. The literals `2^i`, `2^t` are free here only because t is external; quantifying t requires a paid uniform representation. In parallel, the primary compiler discrepancy and the padded-raw-input recognizer need resolution before asserting universality. The fixed finite phase table, input decoder and packing costs cannot be inferred from the local transition.

Run `python grill_tag_affine_scout.py --expect grill_tag_affine_scout.json`. This scout uses standard Python, no repository imports or downloads, and writes only when `--output` is explicitly passed. It makes no fixed-arity universal operation claim.
