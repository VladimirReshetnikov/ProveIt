# Independent review of the native ternary exclusion

**PASS; no requested change.** This review covers the full frozen proof and bounded helper for the digit-class exclusion below. It does not establish that the class occurs on any actual compiler history, decide the independent-gamma83 input language, or certify a new arithmetic circuit.

## Frozen material reviewed

The complete author trio was read and authenticated:

| File | SHA256 |
|---|---|
| `complete83_gamma_native_ternary_exclusion.py` | `9b9c6a55756b425b356a2bc1e653ea829edc1133a96f5697dd4c172d4c3fed66` |
| `complete83_gamma_native_ternary_exclusion.json` | `7d93331f7aec61e68b5fe3220f07d6c44f3c7df58ac8aee045fd702b5e04da12` |
| `complete83_gamma_native_ternary_exclusion.md` | `6eee2ade562b73c264358f3e051efda02e832c102d43f79ba3ade9e9d68ff77b` |

Relevant inherited proof text was read as data:

| File | SHA256 |
|---|---|
| `complete83_gamma_power_tests.md` | `4e8f358a2d651e4cc20946dd3632491d15ad3ee69eb32474a21289e052ec5e4b` |
| `complete75_independent_gamma87_period.md` | `dfe1c4a9c438bfe3907b187a3d407280616a5a7eaaf3aa68048de9938b8ac784` |
| `complete75_gamma87_compiler_order_filters.md` | `43d613204d6dc7192763e87e120f84ea0e3f18849a4fd23be26f56ca45b9fcc3` |
| `complete75_half_binomial_compiler.md` | `68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117` |

The first three proof notes were read in full, and the modified compiler's actual mask recipe, shifted packing, native-word recovery and padding sections were checked. The fresh author replay authenticates all eight declared dependencies, including the independent-gamma83 receipt and companion and the predecessor power-test source/receipt. None of those predecessor Python files was imported or executed. This review uses their established genuine-history interface; it does not repeat the complete native-kernel or universal-compiler audit.

## Mathematical challenge

For ternary digits of r restricted to 0 and 1, doubling r has no ternary carry. Thus the central binomial coefficient is a unit modulo 3, and floor(2r/3)=2 floor(r/3). Removing multiples of 3 from both factorials therefore gives exactly the author's unit recursion modulo 9, with no unaccounted power of 3. Writing r=9k+t with t in {0,1,3,4}, both complete-block signs cancel because 2t<9. The remaining four ratios are 1,2,1,8. Iteration proves

    binom(2r,r) = 2^(s+2z) mod 9,

where s counts the 1 digits and z counts adjacent 11 pairs. This is an unrestricted identity on that digit class; the seven-digit check is supplementary evidence.

For the positive r used in the native application, the two alternating-tail identities are correct:

    G_r(-1)=binom(2r,r)/2,
    G'_r(-1)=binom(2r-2,r-1).

The second also equals r*binom(2r,r)/(2(2r-1)). On the restricted class r is a positive multiple of 3, so the derivative is divisible by 3. Taylor coefficients of the integral polynomial about the integer -1 remain integers. With delta0=2^R+1 divisible by 3, all terms beyond the constant contribution to delta0*G_r(-1+delta0)/2 vanish modulo 27: the derivative term has three factors of 3 and the higher terms contain delta0 cubed. Division by 2 and 4 is legitimate modulo 27. Finally r=3*epsilon mod 9 gives R=1+6*epsilon mod 18, and delta0/3 is respectively 1 or 7 modulo 9. These facts reproduce every entry of the six-entry table and the condition e=3+2*epsilon mod 6.

If a=6 mod 27, then v3(Delta)=2 exactly, while 27 divides H. The local order ord_(3^h)(2)=2*3^(h-1), for h=v3(H), divides the full order O. Consequently 9 divides O, and

    v3(gcd(2Delta,O))=2.

Other prime factors of H can increase v3(O), but cannot increase this gcd beyond the exact valuation of Delta. This is why the stronger exact statement here is consistent with the predecessor's warning that local order data need not determine the full gcd in other residue classes. The actual compiler's d is a power of 5, so dividing by gcd(g,2d) removes no factor of 3: v3(m)=2 exactly.

The all-e exclusion is also direct: v3(H-1)=0 and v3(H-3)=v3(4a)=1. Multiplication by any power of 2 preserves these valuations, whereas every exponent yielding 1 modulo H must be divisible by 9. No inference from a finite run of failed squarings is needed.

The inherited fixed-history alias criterion then excludes input differences not divisible by 9 on this same history. In particular the proposed shifts from ordinary input 4 to 3 or 1 fail there. This does not exclude another history or another mechanism. The actual shifted-mask parity calculation additionally makes odd duration, even selector count and even tile-alphabet size necessary for the class; it does not make them sufficient or construct a history.

## Helper and evidence scope

The full helper uses explicit exception checks, duplicate/nonfinite JSON rejection, exact-type receipt comparison and strict dependency hashes. Its prime-power row recurrence retains the 3-adic valuation separately from the unit, including while a coefficient vanishes modulo the selected power; it does not lose information needed when later valuations decrease. The exponent update starts at X^(-r), so row positions j>=r contribute exactly the intended upper half-binomial tail.

Fresh normal and optimized exact replays from `/` both passed against the frozen receipt. They authenticate all eight dependency entries and the helper self-hash, and reproduce:

- 128 exact central-coefficient checks and 128 pairs of tail-identity checks;
- 32 native-formula samples in the declared odd-r range, including 11 in the exclusion subclass;
- 64 freely chosen arithmetic hosts, with complete small orders and alias checks for d=5,25,125;
- the 511,999-coefficient streaming calculation at R=511999, q=32, giving a=6 mod 81.

The last parameter satisfies the displayed numerical range, parity and population prerequisites. It supplies neither compiler masks nor transport nor a computation, and is correctly labelled as no compiler history. The small order hosts have the same limitation. No full polynomial zero or new complete source is emitted.

Replay, with the research directory supplied explicitly:

    python3 /absolute/path/complete83_gamma_native_ternary_exclusion.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/complete83_gamma_native_ternary_exclusion.json
    python3 -O /absolute/path/complete83_gamma_native_ternary_exclusion.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/complete83_gamma_native_ternary_exclusion.json

Only the new bounded helper ran. No repository or frozen predecessor file was changed.
