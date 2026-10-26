# Independent internal review of the signed-horizon arithmetic

Reviewed `agent_alternative/pooled/PROOF.md` (the signed horizon, growth,
four-base pooling interface, cofinality, and restoration argument), together
with the incoming Pell Growth 210 report's literal power-request list and
its affine-radix and growth proofs. This is a separate AI-assisted internal
mathematical review, not outside human peer review or a kernel verification.

No gap was found in the new arithmetic composition. The following points
were checked explicitly.

1. **Signs are established in a valid order.** For every integer horizon
   parameter z, `t=2+4z` is nonzero with |t|>=2 and |t+1|>=1. The growth row
   alone gives nonzero even F and |F|>=2^19|t|, without invoking positive-base
   Pell classification. Thus B eta=C+F+1 has odd right side, B and eta are
   nonzero, and D=2(C+F+1) has absolute value at least two. The D request gives
   x>=0. The terminal beta coefficient has absolute value at least |F|-1>1,
   so x=0 is impossible. Only now, with |q|>=2, does the retained q-power
   request with nominal exponent t establish t>=0 and hence t>=2.
2. **The requested exponent really is t.** The source210 report explicitly
   lists base-q requests at t, y+1, and x. The new proof does not silently
   use a t+1 request or infer t's sign from a unit base. The y+1 request and
   |y|>=|F| then force y>0. The initial beta endpoint excludes x=1. Once
   |q+1|>=3, its F+t request forces F>0, and its CRT-index requests force
   the representatives nonnegative and C>0. The affine base D is now positive.
3. **The lower horizon bound two is sufficient.** For positive t the
   unchanged Pell index-divisibility argument gives n>=2^19 t and hence
   F>=L^t with L=8^(2^19-1)t^(2^19). The source comparison ratio
   8^(t-1)/t is at least one already at t=1. The label constructors need only
   their fixed leaves 0 and 1 to lie below t. Their bound
   E(m,m)+1<=8(m+1)^2 is valid for all m>=0.
4. **The factorial/range condition is not lost.** L>=t^2 implies
   F>=t^(2t)>=(t!)^2>=lcm(1,...,t)^2. This replaces the former t>=16
   shortcut without any unproved growth estimate. The new minimum F exceeds
   2^32 by a wide margin. Together with x>=2+(t+1)y and y>=F, the displayed
   inequality 2+t+x+y+F<2x follows from (t-1)y>t. Thus the retained local
   polynomial bound has the needed numerical hypothesis.
5. **The common frame has the needed size before sign recovery.** Its actual
   atoms include F. Since |F|>=2^20, its positive square identity already
   gives W>=258. Deleting the obsolete exact-growth request does not require
   the independent standalone Pell pair to be added to this frame.
6. **Cofinality and binomial parity are constructive.** The progression
   t=2 modulo 2^23 is cofinal, is contained in t=2+4z, and has bit 20 zero.
   With n0=2^19 t, the recurrence modulo 4t and the exact doubling valuation
   give y0/(2^19 t) odd. For a0=1 modulo 4, the addition identity shows
   Y_(s+2^r)-Y_s=2^r modulo 2^(r+1), because v2(Y_(2^r))=r and
   v2(X_(2^r)-1)>=2r+2. This proves the residue permutation inductively.
   Selecting an odd residue class of s gives F=2^20 modulo 2^ell. Since
   t<2^ell and t's bit 20 vanishes, there are no binary carries in F+t;
   the binomial is odd. Positive lifts of s are cofinal and make F arbitrarily
   large without changing its required low bits.
7. **Prime support is the correct beta condition.** Choosing the odd beta
   multiplier divisible by every odd prime at most t makes y divisible by
   every prime at most t, since F is even. A common prime divisor of
   1+iy and 1+jy would then have to divide i-j, contradicting its not dividing
   y. Full divisibility by t! is neither used nor claimed.
8. **Pooling respects zero-base and unit-base cases.** B,D are already
   nonzero when their oriented block is applied. After its D request,
   q and q+1 are nonzero and have the same sign, including q=1 at the
   initially possible x=0 branch. The unweighted q/q+1 block is therefore
   legitimate. All pools are subfamilies within the previous request-count
   and error-budget bounds. The documented quotient restorations preserve
   the integer zero set once the exact power identities are known.

An additional useful consequence, consistent with the proof but stronger
than the preliminary bound it needs, is that **every** new integer zero has
v2(F)=20: t=2(1+2z) has exact valuation one and 2u+1 is odd. This is not
restricted to the cofinal completion and validates the F64/F128 saturated
coordinate changes in the quartic branch.

The inherited C222/ZF/ZFC calibration and earlier unbounded Pell/pooling
lemmas remain the specified proof boundary. This review did not rebuild those
historical formal developments or rerun the producer's exhaustive finite
coefficient checks.
