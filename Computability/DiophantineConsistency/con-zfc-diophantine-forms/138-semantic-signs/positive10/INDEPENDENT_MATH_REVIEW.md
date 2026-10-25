# Independent review of the free-T compact bV transport

This review concerns the new compact branch developed in parallel, not the natural quartics in this folder. Its assumptions are the inherited main-rank folding, first Pell norm, q-cube normalization Y=q^3*s, q>=32, and the doubled product-square kernel. The following new steps were independently checked algebraically.

1. To exclude p=3, write v=X*mu^2*Y^2 and D=(X+1)^2-2XY. If the first Pell index is at least three, kY>32v^2Y>4A^2-1. At first index two, k=8v+4 and eta=4mu^2Y^2D+8muY(X+1)+3-4Y. If D>=2X then eta>k. If D<=0, the integral identity D=1+X(X+2-2Y) gives D<=1-X and X+1<2Y; hence eta<=-4mu^2Y^2(X-1)+16muY^2+3-4Y<0. Thus 0<D<2X, implying X+2-2Y in {0,1}, contrary to q dividing both X and Y. The main odd rank is at least five.

2. Let b=cT-R and V=f^2*b-c, with f^2>2c and Q=Delta(f^2-1). If b=0, then |V|=c>1 but c<4Q-3. This contradicts the adjacent-Pell odd-index spectrum: |V| is 1 or at least 4Q-3. Thus b is nonzero and sign(V)=sign(b).

3. Auxiliary index three would give V=+/- (4Q-3). Reducing modulo f^2 yields divisibility of either c-(4Delta+3) or c+(4Delta+3) by f^2. The newly proved main rank at least five makes the first positive; both are strictly less than f^2, since U>=c^2. Therefore auxiliary index is at least five and |V|>8Q^2.

4. From V=f^2*b-c and c<f^2, |b|>|V|/f^2-1>4Delta^2(f^2-1)-1=4Delta^3I^2-1>4g. Hence L=bV=|b||V|>0 and gy<(3/2)g|V|<3L/8. Also b-e=cT-k+1>0, so rho=e/mu^2<b/mu^2<=|b|/mu^2<L/2. These inequalities give a strict negative upper bound for the positive carrier input if B<=-1. The transport therefore enforces B>=0 without requiring b initially positive.

5. Completeness uses the old positive T'=T_old+alpha as the new free positive T. No seed-period or old auxiliary pair is copied incompatibly.

No flaw was found in these new steps. This scoped review assumes the inherited normalized fold, canonical completeness, fixed-coefficient binding and adjacent-Pell rational-integrality interfaces; it does not claim to recompile an end-to-end proof assistant development or verify the final circuit bytes. It is an independent AI-assisted review within this workflow.

## Additional check of the two V² transport endpoints

After reading the current compact `PROOF.md`, Sections 4-7, I also checked the unnormalized 83/436 and normalized 80/750 sign-free V² transports. The direct b=0 argument is especially economical: Q>c² makes the integral y² lie strictly between c² and c²+1. For b nonzero, f²>c+1 gives sign(V)=sign(b), |b|<|V|, and the displayed a²-g² identity gives g<a. The inequality f²-c>3a then yields gy<V²/2. Together with the one-sided rho<|V|/mu² and Wt<-V² when B<=-1, this forces the positive carrier input n to be negative. No sign of e or b is assumed in advance. The normalized carrier has one fewer positive summand, so the same upper bound remains valid. The mathematical scope remains conditional on the specifically retained main-folding, later signed-index, source reconstruction and coefficient calibration interfaces.
