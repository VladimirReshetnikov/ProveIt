# Compact odd-parity calibration

This changes only three source registers in the independently reviewed scaled split construction:

- G_plus = D2 U_c^2 + D1 U_c + D0 + B^2161.
- L = B^2279.
- n_hat = eta * epsilon * B^1201, where eta=2^(8 kappa-10) and kappa=2134940.

The source, coefficient tuple, sparse targets, mask, CRT ratio formulas, coprime spectator, and final raw norm remain unchanged. In the literal ratio formulas use U=n_hat^2 w^2 and Y=n_hat^2 s. The JSON register named N contains n_hat, which may be negative. In the proof only, instantiate the positive Jones parameter by N=abs(n_hat). No absolute value occurs in the polynomial.

## Positivity before recovering any sign

The prior square completion now yields

G_plus > (1/4) B^1929 U_c^2 + B^2161 - 4 A_*^2 B^2125 - 2 A_* B^1719
       > (1/4) B^1929 U_c^2 + (1/2) B^2161.

Indeed the normalized losses are 4 A_*^2/B^36 and 2 A_*/B^442, each less than 1/4 because B=8192 A_* b^2 and b>=2. Thus

S_c > (1/2) N0 B^1929 U_c^2 + U_c + N0 B^2161 - ell > 0

for every integer U_c=ell+g, using t U_c^2+U_c>=0 for t>=1 and ell<N0. T_c>0 remains unchanged. Hence R>L^2.

N=abs(n_hat) is positive because epsilon!=0. Moreover

N^2 = 2^-21 a^16 b B^2402 < a^15 B^2403 < B^2418 < B^4558 = L^2.

For c=b B^116, N>=c follows from eta B^1085>=2 abs(epsilon). This inequality is immediate from eta>=1 and B>=2 abs(epsilon). Also N>=B^1201>=8. Consequently R>=N>=8 and b,c<=N. These are statements about the positive proof-side N, never about signed n_hat.

## No extra block needed

For 0<g<c the same estimate gives 2 abs(G)<B^2162/256 and Targets<B^2162/256. Since B>256,

J_c = 2G + 2 B^2161 + Targets < B^2162/64.

It is positive by the unconditional lower bound. Therefore

S_c < B^2279/32,   T_c < B^2279/64,

where the second bound uses Targets<B^2130/(B-1) and the 32-exponent gap to B^2162. Thus S_c+T_c<L. The added coefficient1 remains above every target (2161>2129) and is covered by the same bound 994 A_* b^2<B/8. The sparse carry proof is unchanged.

## The threshold is a square on exactly the required base class

The Jones soundness theorem first proves b=2^k. Since b=2 epsilon^2 with epsilon a nonzero integer, k is necessarily odd and epsilon^2=2^(k-1). Write nu=kappa+2k. With L=B^2279,

log2 L+s2(T_c)+1 = 2418 nu-31k-21
                         = 2418 kappa+4805k-21
                         = 2(8 kappa-10+1201 nu)+(k-1)
                         = log2(n_hat^2).

Thus the central-binomial divisibility is exactly the same no-carry test, now with N^2=n_hat^2. There is no need to assert the identity for even k, which cannot occur. In the completeness direction choose epsilon=2^r>0 and b=2^(1+2r); these admissible bases are cofinal. The canonical omega is still a square, and the same c,b<=N estimate proves Delta>0.

All subsequent zero-branch, sign-bootstrap, CRT and rational-root arguments are unchanged. This proves the compact polynomial's equivalence to the same source and to a finite ZFC refutation.

## Exact metric

The emitted `generated/signed_coprime_compact_split_crt.json` has 13 unrestricted integer variables and 518 binary operations (326 multiplication, 169 addition, 23 subtraction). Its exact degree is 11,543,632. The top term is A0norm^2; its diagonal leading coefficient is 630137 * a^2885464 * eta^960 modulo 1000003, which is nonzero. The normal and optimized Python checks verify literal replay, bound tests, all 89 source records, and the odd-k calibration.
