# An explicit 87-operation primality certificate

Independent verification of Theorem 5 (1976).

All fourteen residuals are checked symbolically against the accompanying TeX; they also match the degree-25 prime polynomial after the documented shift of k.

## Counting convention

a,...,z nonnegative; k>=1; candidate N=kp1. Intermediate signed integers may be supplied. Equality/domain checks and reading the certificate are not arithmetic operations.

An independently constructed upper-bound certificate, not an optimality proof, not a reconstruction of the authors' undisclosed evaluation order, and not a bit-complexity bound or witness-finding algorithm.

The displayed straight-line schedule has subtractions. In a certificate using literally only addition and multiplication, supply each intermediate integer and replace `t = a - b` by the one-addition check `t + b = a`. All other assignments are checked directly. Hence the same schedule uses exactly 40 additions and 47 multiplications.

Supply k as part of the certificate and verify N=kp1; kp1 was already computed. Thus converting the tested number N to k does not add a subtraction.

| No. | Equation block | Assignment | Addition/multiplication check |
|---:|---:|---|---|
| 1 | 1 | `hj = h + j` | `h + j = hj` |
| 2 | 1 | `wz = w * z` | `w * z = wz` |
| 3 | 1 | `rhs1 = wz + hj` | `wz + hj = rhs1` |
| 4 | 2 | `gk = g * k` | `g * k = gk` |
| 5 | 2 | `gkg = gk + g` | `gk + g = gkg` |
| 6 | 2 | `gkgk = gkg + k` | `gkg + k = gkgk` |
| 7 | 2 | `zprod = gkgk * hj` | `gkgk * hj = zprod` |
| 8 | 2 | `rhs2 = zprod + h` | `zprod + h = rhs2` |
| 9 | 3 | `kp1 = k + 1` | `k + 1 = kp1` |
| 10 | 3 | `np1 = n + 1` | `n + 1 = np1` |
| 11 | 3 | `fourk = 4 * k` | `4 * k = fourk` |
| 12 | 3 | `fourkn = fourk * np1` | `fourk * np1 = fourkn` |
| 13 | 3 | `fourkn2 = fourkn * fourkn` | `fourkn * fourkn = fourkn2` |
| 14 | 3 | `kkp1 = k * kp1` | `k * kp1 = kkp1` |
| 15 | 3 | `fprod = kkp1 * fourkn2` | `kkp1 * fourkn2 = fprod` |
| 16 | 3 | `rhs3 = fprod + 1` | `fprod + 1 = rhs3` |
| 17 | 3 | `lhs3 = f * f` | `f * f = lhs3` |
| 18 | 4 | `twon = 2 * n` | `2 * n = twon` |
| 19 | 4 | `pq = p + q` | `p + q = pq` |
| 20 | 4 | `pqz = pq + z` | `pq + z = pqz` |
| 21 | 4 | `rhs4 = pqz + twon` | `pqz + twon = rhs4` |
| 22 | 5 | `ap1 = a + 1` | `a + 1 = ap1` |
| 23 | 5 | `ep2 = e + 2` | `e + 2 = ep2` |
| 24 | 5 | `eap1 = e * ap1` | `e * ap1 = eap1` |
| 25 | 5 | `eap12 = eap1 * eap1` | `eap1 * eap1 = eap12` |
| 26 | 5 | `eep2 = e * ep2` | `e * ep2 = eep2` |
| 27 | 5 | `oprod = eep2 * eap12` | `eep2 * eap12 = oprod` |
| 28 | 5 | `rhs5 = oprod + 1` | `oprod + 1 = rhs5` |
| 29 | 5 | `lhs5 = o * o` | `o * o = lhs5` |
| 30 | 6 | `a2 = a * a` | `a * a = a2` |
| 31 | 6 | `A = a2 - 1` | `A + 1 = a2` |
| 32 | 6 | `y2 = y * y` | `y * y = y2` |
| 33 | 6 | `xprod = A * y2` | `A * y2 = xprod` |
| 34 | 6 | `rhs6 = xprod + 1` | `xprod + 1 = rhs6` |
| 35 | 6 | `lhs6 = x * x` | `x * x = lhs6` |
| 36 | 7 | `ry2 = r * y2` | `r * y2 = ry2` |
| 37 | 7 | `fourry2 = 4 * ry2` | `4 * ry2 = fourry2` |
| 38 | 7 | `fourry22 = fourry2 * fourry2` | `fourry2 * fourry2 = fourry22` |
| 39 | 7 | `uprod = A * fourry22` | `A * fourry22 = uprod` |
| 40 | 7 | `rhs7 = uprod + 1` | `uprod + 1 = rhs7` |
| 41 | 7 | `u2 = u * u` | `u * u = u2` |
| 42 | 8 | `cu = c * u` | `c * u = cu` |
| 43 | 8 | `xcu = x + cu` | `x + cu = xcu` |
| 44 | 8 | `lhs8 = xcu * xcu` | `xcu * xcu = lhs8` |
| 45 | 8 | `u2a = u2 - a` | `u2a + a = u2` |
| 46 | 8 | `u2u2a = u2 * u2a` | `u2 * u2a = u2u2a` |
| 47 | 8 | `G = a + u2u2a` | `a + u2u2a = G` |
| 48 | 8 | `G2 = G * G` | `G * G = G2` |
| 49 | 8 | `G2m1 = G2 - 1` | `G2m1 + 1 = G2` |
| 50 | 8 | `dy = d * y` | `d * y = dy` |
| 51 | 8 | `fourdy = 4 * dy` | `4 * dy = fourdy` |
| 52 | 8 | `nfourdy = n + fourdy` | `n + fourdy = nfourdy` |
| 53 | 8 | `nfourdy2 = nfourdy * nfourdy` | `nfourdy * nfourdy = nfourdy2` |
| 54 | 8 | `gprod = G2m1 * nfourdy2` | `G2m1 * nfourdy2 = gprod` |
| 55 | 8 | `rhs8 = gprod + 1` | `gprod + 1 = rhs8` |
| 56 | 9 | `l2 = l * l` | `l * l = l2` |
| 57 | 9 | `mprod = A * l2` | `A * l2 = mprod` |
| 58 | 9 | `rhs9 = mprod + 1` | `mprod + 1 = rhs9` |
| 59 | 9 | `lhs9 = m * m` | `m * m = lhs9` |
| 60 | 10 | `am1 = a - 1` | `am1 + 1 = a` |
| 61 | 10 | `iam1 = i * am1` | `i * am1 = iam1` |
| 62 | 10 | `rhs10 = k + iam1` | `k + iam1 = rhs10` |
| 63 | 11 | `nl = n + l` | `n + l = nl` |
| 64 | 11 | `rhs11 = nl + v` | `nl + v = rhs11` |
| 65 | 12 | `an = a - np1` | `an + np1 = a` |
| 66 | 12 | `an2 = an * an` | `an * an = an2` |
| 67 | 12 | `Dn = A - an2` | `Dn + an2 = A` |
| 68 | 12 | `bDn = b * Dn` | `b * Dn = bDn` |
| 69 | 12 | `lan = l * an` | `l * an = lan` |
| 70 | 12 | `pla = p + lan` | `p + lan = pla` |
| 71 | 12 | `rhs12 = pla + bDn` | `pla + bDn = rhs12` |
| 72 | 13 | `ap = a - p` | `ap + p = a` |
| 73 | 13 | `app = ap - 1` | `app + 1 = ap` |
| 74 | 13 | `app2 = app * app` | `app * app = app2` |
| 75 | 13 | `Dpp = A - app2` | `Dpp + app2 = A` |
| 76 | 13 | `sDpp = s * Dpp` | `s * Dpp = sDpp` |
| 77 | 13 | `yapp = y * app` | `y * app = yapp` |
| 78 | 13 | `qyapp = q + yapp` | `q + yapp = qyapp` |
| 79 | 13 | `rhs13 = qyapp + sDpp` | `qyapp + sDpp = rhs13` |
| 80 | 14 | `ap2 = ap * ap` | `ap * ap = ap2` |
| 81 | 14 | `Dp = A - ap2` | `Dp + ap2 = A` |
| 82 | 14 | `tDp = t * Dp` | `t * Dp = tDp` |
| 83 | 14 | `pl = p * l` | `p * l = pl` |
| 84 | 14 | `plap = pl * ap` | `pl * ap = plap` |
| 85 | 14 | `zplap = z + plap` | `z + plap = zplap` |
| 86 | 14 | `rhs14 = zplap + tDp` | `zplap + tDp = rhs14` |
| 87 | 14 | `lhs14 = p * m` | `p * m = lhs14` |

## Final comparisons

These are equality tests, with no additional arithmetic:

`q = rhs1`, `z = rhs2`, `lhs3 = rhs3`, `e = rhs4`, `lhs5 = rhs5`, `lhs6 = rhs6`, `u2 = rhs7`, `lhs8 = rhs8`, `lhs9 = rhs9`, `l = rhs10`, `y = rhs11`, `m = rhs12`, `x = rhs13`, `lhs14 = rhs14`, `candidate = kp1`

Reproduce with `python jones1976_verify_87_operations.py`. The argument from satisfiability to primality is Theorem 2.12; this script verifies its arithmetic realization, not the complete number-theoretic proof of that theorem.
