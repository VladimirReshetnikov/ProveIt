# One monomial can serve both label-copy families

This isolated finite checkpoint merges the two bare label-copy monomials
into one. It preserves all 943 decoded indexed selectors, all 34 weighted
labels, both zero-weight dummies, the physical zero-weight Start marker,
and all 980 native mask tests. No accepted equation is changed here.

Use `rho=2^47`, `M=2^44`, and the following physical blocks:

| Role | Positions |
|---|---|
| Selectors | 0..942 |
| South | 943..951 |
| North | 961..969 |
| Dummies | 970, 971 |
| West | 972..979 |
| East | 981..988 |
| Start marker | 1008 |

The old selector coefficients are unchanged. South, west, north and east
label weights remain `2^(35+j)`, `2^(27+j)`, `2^(18+j)`, and `2^(10+j)`.
Both dummies and the physical marker have coefficient zero. Let `Phi`
denote this full coefficient polynomial. Then the entire changed kernel is

```
Lambda = rho^1998 + rho^3007
DC = rho^18 + rho^1008 + Lambda*Phi(1/rho)
DR = rho^9
K = DC + rho^(L+9)
```

The shared `rho^18` occurs exactly once. It copies south into north at
961..969, and west into 990..997, where `DR` supplies the east bits.
The spatial predecessors 952..960 of the north tests are absent. The
spatial tests 990..997 are themselves absent from the physical support.
The marker's other predecessors 990 and 999 are absent. Reflection starts
at 1010, above every copy or marker test. The probe compares every tested
field and both clause predecessors against the complete convolution.

The clauses at 1998 and 3007 have gap 1009, larger than the whole physical
support span. The lower predecessor is exactly the adjacent coefficient
sum; the upper has the one additional term `c_0*x_1008`. The `rho^1008`
term applied to non-marker inputs ends at 1996; its marker input contributes
at 2016. Neither affects the clauses or their predecessors. The complete
last product is at 4015 with coefficient `c_0*x_1008`. Padding comprises
18 full fields 4016..4033 and low 29 bits at 4034, preserving 875 padding
bits and 980 total tests.

Start's south-one tests are 962..969. Together with marker 1008, any
nonzero integral offset satisfies `20<=r<=962`. At `r=20`, target 962
forces selector 942 and target 963 forces south bit zero at position 943.
The already decoded tile 942 has complemented south 74, whose bit zero
is zero. For `r>=21`, targets 962 and 963 demand two distinct selectors
in one cell. The exhaustive support calculation finds exactly 934
candidates: zero, 932 multiple-selector contradictions, and the calibrated
exception at 20. Fractional-phase exclusion retains the full low-band
carry reset. The marker still encodes the shifted Start indicator.

For contrast, marker 1007 admits a local offset-19 pattern: decoded tile 4
has complemented colors `(255,507,247,511)`, so selector 942 is zero,
south bits 0..7 are one, and east bit 7 is one. These reproduce all nine
Start south-copy bits and the marker test under that offset. This is a
local obstruction to that phase argument, not a complete native witness
or polynomial zero.

The complete Boolean and extra-dummy convolution maxima both equal
3829914518407087, at the two clause fields. All carry, reset, safe-dummy
and scalar-box checks pass. The safe-dummy exponents are 3977, 979 and
970, with their exponent-plus-one margins checked explicitly.

The first admissible prime length is `L=4049`, `d=190303`; in particular
4039 is composite. Exact base-two and B orders are 23 modulo 47 and
506 modulo 4049, with all prime factors 2, 11 and 23 tested. The spacing
is 506. Auxiliary prime `lambda=190763=377*506+1` exceeds d and has lift
quotient 65850. The complete new K gives controller values
`H=(34,3240,43425)` modulo 47, 4049 and lambda. Dense polynomial,
direct decoded-tile and whole-integer K calculations agree.

The complete four-port raw size is **95,205 bytes**, 1,841 fewer than the
97,046-byte Start-marker1031 tuple. There is also one fewer summand in the
printed K recipe. This does not change the retained 66-gate polynomial
front or establish a global minimum. The full source chain is pinned
before decoding; arrays and receipts are deterministic under Python with
and without `-O`.

```
python research/merged-copy-probe/probe.py --write
python research/merged-copy-probe/probe.py
python -O research/merged-copy-probe/probe.py
```

The script supplies complete finite evidence and a proof lead. A separate
complete ordinary proof, independent review and full page/port binding
remain required before this tuple replaces an accepted source.
