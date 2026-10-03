# Cancellation of the compacted and DFA ratio defects

Date: 2026-10-02. **Conclusion: the conjecture is correct, conditional only on the general signed all-orders theorem currently under independent audit.** The calculation below is a rigorous corollary of that theorem and the approved relaxed formal recursion; it does not supply a substitute proof of the signed analytic transfer.

Fix k≥3, q=k−1, d=3q. With the exact source and DFA exceptional-seed conventions of `general-signed-all-orders.md`, put

u_n=C_n/R_n,  v_n=B_n/(2^(n−1)R_n),

and denote their positive limits by u∞,v∞. Then

log(u_n/u∞)−2log(v_n/v∞)
 = −q^(k−1)/k^k · n^(−q) + O_k(n^(−q−1/3)).

In particular the coefficient is −4/27 for k=3 and −27/256 for k=4. Every preceding fractional power vanishes, not only the leading individual defect. This can safely be incorporated as a conditional corollary now, and unconditionally once the signed all-orders theorem is approved.

## 1. Formal orders and the first individual profile change

Use precisely the common scalar/profile gauge of the cited proofs: ε=i^(−1/3), x=ε(j+1), Φ_X=Σ ε^m φ_m^X, σ_X=k+O(ε²), and φ_m=A_m f+B_m f′ with A_m(0)=B_m(0)=0. Let Φ_0,σ_0 denote the relaxed solution. All valuations in this section refer to formal ε-series whose coefficients are polynomial combinations of f,f′.

Write the exact equation as

T(ε)Φ_X − σ_X Φ_X − β_X Q_X S(ε)Φ_X = 0,

where Q_X=Π_(l=1)^k σ_X(ετ_l)^−1, S includes the delay-time dilation τ_(k+1) and the shift x−ε, and T is the two-term relaxed transfer. These are the k inverse scalar factors after division by H_(i−1), not k+1 factors.

The delay starts at order d. Triangular uniqueness of the relaxed recursion therefore gives

δσ_X:=σ_X−σ_0=O(ε^d),  δΦ_X:=Φ_X−Φ_0=O(ε^(d−2)).

At order d, the delay forcing is a scalar multiple of f. It is absorbed entirely by δσ_d: the polynomial inverse and the stated gauge give δφ_(d−2)=0. Consequently

δΦ_X=O(ε^(d−1)),  δQ_X=O(ε^d).                 (1)

The argument uses the exact gauge; an arbitrary amplitude convention could obscure these valuations.

## 2. No nonlinear feedback can reach the requested order

Subtract the relaxed equation and retain through order d+3. The only nonlinear perturbation products have valuations at least

δσ_X δΦ_X: 2d−1,
β_X Q_0 SδΦ_X: 2d−1,
β_X δQ_X SΦ_0: 2d.

Because d≥6, 2d−1>d+3 and 2d>d+3. Shift and dilation preserve these lower bounds. Thus the response equation is genuinely linear, modulo O(ε^(d+4)); this is an exact order argument, not a linear-response assumption.

Define ΔΦ=Φ_C−2Φ_B+Φ_0 and Δσ=σ_C−2σ_B+σ_0. The exact coefficient identity on the Airy window is

β_C−2β_B = −q^(2k)/(X)_k
 = −q^k k^k ε^(d+3) + O(ε^(d+5)).

Since Q_0(0)=k^(−k) and SΦ_0=f+O(ε), the combined equation becomes

TΔΦ−σ_0ΔΦ−ΔσΦ_0 + q^k ε^(d+3)f = O(ε^(d+4)).   (2)

At every stage below d+3 the unique gauged solution is zero. At stage d+3 the new profile has index d+1, and (2) gives

k L_q Δφ_(d+1) − Δσ_(d+3)f + q^k f = 0.

Again pure-f forcing is absorbed entirely into the scalar. Therefore

Δσ=q^k ε^(d+3)+O(ε^(d+4)),
ΔΦ=O(ε^(d+2)).                                        (3)

In particular all combined profile coefficients through index d+1 vanish.

## 3. Scalar logarithms, accumulated normalization, and endpoints

Taylor expansion of log σ_X around σ_0 has a nonlinear remainder beginning at ε^(2d), beyond d+3. Thus (3) implies

log σ_C−2log σ_B+log σ_0
 = (q^k/k) ε^(d+3)+O(ε^(d+4)).                         (4)

All three scalar products are normalized with the same leading factor and leading constant one:

H_X(i)=G(i) exp[Σ_(r≥1) h_r^X i^(−r/3)].

A term h_r i^(−r/3) contributes −(r/3)h_r ε^(r+3) to its scalar log step. The matching map is linear in the h_r and triangular, so (4) proves

h_r^C−2h_r^B+h_r^0=0 for r<d,
h_d^C−2h_d^B+h_d^0=−q^k/(kq)=−q^(k−1)/k.             (5)

This also checks that no integration constant was inserted: the leading constants of the H_X are exactly one, while the actual model-dependent amplitudes are precisely removed by u∞ and v∞.

At the diagonal endpoint x=ε, every profile vanishes at x=0 and f′(0)≠0. Hence δΦ_X(ε,ε)/Φ_0(ε,ε)=O(ε^(d−1)), without losing a power. Equation (3) gives ΔΦ(ε,ε)/Φ_0(ε,ε)=O(ε^(d+2)). Taking logarithms introduces only quadratic errors O(ε^(2d−2)), also beyond ε^d. Thus the endpoint profiles contribute no term through ε^d to the combined logarithm. Cutoffs are identically one there.

The common factorial transform, the relaxed growth factor, and Stirling contributions cancel exactly. The exceptional DFA factor of two changes only its amplitude and disappears on division by v∞. Finally i=kn; (5) becomes

−q^(k−1)/k · (kn)^(−q)=−q^(k−1)/k^k · n^(−q).

The signed all-orders theorem permits truncation beyond this order with the same positive amplitudes, giving the displayed O(n^(−q−1/3)) remainder and hence the requested little-o assertion.

## 4. Reproducible symbolic check

Run `python check_cancellation.py` in this directory. It retains λ symbolically and computes the exact polynomial-Airy response recursion for k=3,4 through orders d,…,d+3, using two independent response parameters: t multiplies 2β_B and r multiplies the negative extra delay. The specializations (t,r)=(1,1),(1/2,0),(0,0) are compacted, DFA, and relaxed. It asserts both f and f′ residual equations at every stage, all combined profile vanishings, the combined scalar coefficient, and the strict nonlinear valuation inequalities. `relaxed_low_stages.py` is a reproducible copy of the relaxed low-order recursion needed to supply profiles through index 3 and scalars through index 4. The output is in `check-output.txt`.

Dependencies read: `/workspace/shared/fixed-arity-airy-research/all-orders-proof.md` and `/workspace/shared/fixed-arity-airy-research/signed-extensions/general-signed-all-orders.md`. No ongoing main report was edited.
