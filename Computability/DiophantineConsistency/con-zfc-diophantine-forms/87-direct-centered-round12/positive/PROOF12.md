# Materialized incoming twelve-positive ordinary norm

This is not claimed as a new theorem by this package. It materializes the existing manuscript `docs/incoming/report.zip`, supplied as report.tex alone at repository main9a33342a03d19cf5b061b2083c6b5d3f27f752ed. The complete mathematical argument is retained in `interfaces/incoming_report.tex`, Section "A twelve-positive-variable polynomial of degree70". The incoming manuscript refers to a JSON graph absent from its ZIP; `p12_degree70.json` supplies a literal graph and independently reproduces all claimed metrics: 100 operations, residual degrees15,13,42, exact product degree70. The unchanged complete compact44 tuple is bound by native/ACTIVE_BINDING.json.

Relative to round11's degree78 circuit, replace d=Delta c^4 by d=c^4 and replace rho by Q=Delta(f^2-1) in the two norm-coefficient slots. No other register changes. The norm is

N=[d h(n)+(1-Q)Q]^2-d [2(1-Q)(n+V)]^2 Q,
h(z)=(1-Q)z^2+2(1-Q)Vz+V^2-1.

On N=0, i*= [d h(n)+(1-Q)Q]/[2d(1-Q)(n+V)] satisfies d i*^2=Q and h(n-i*)=0. The first two carrier residuals independently yield c>2R and V>1, so the denominator is nonzero. Adjacent Pell saturation makes y*=V+n-i* integral, hence i* integral. Thus (i c^2)^2=Delta(f^2-1), the ordinary strong equation. The earlier adaptive congruence q^4|(k-R-1) and Pell recurrence imply first index m1>=(R+1)/2>=24 before strong-rank recovery, hence c>(a+2)Delta^2. This licenses the inherited ordinary rank lemma. It is essential to lift to the ordinary source kernel, not to divide i byDelta and falsely assume an integral normalized multiplier.

Completeness starts from normalized canonical source witnesses and replaces i byDelta i, preserving Q and the auxiliary norm. With u=y-V>0, choose n=i+u and t=f-1. The identity N|_{Q=d i^2}=d^2 h(n-i)h(n+i) proves the merger. All three residuals are squares modulo4, so the final unit product vanishes exactly when all residuals vanish.

The manuscript's leading forms and coefficient certificate are independently retained: q0=6beta j,k0=eta+zeta,R0=q0^3(q0-F), Bt0=(K0q0+X)(q0-F-alpha)-q0F,
[A0]15=-2q0^8k0^2XY^2 Bt0,
[A1]13=8q0^2k0X^2Y^4(q0^2Ygamma+R0),
[N]42=4k0^8X^4Y^12t^8R0^2n^2.
The coefficient at j^18 F^2 eta^11 X^8 Y^19 t^8 n^2 gamma alpha is64(6beta)^18>0. Thus the degree is exactly70 for the actual tuple. The new executable tests verify graph topology and liveness, literal norm transcription, cancellation-sensitive degree on exact modular lines, and the actual coefficient files; they do not constitute a new kernel certificate.
