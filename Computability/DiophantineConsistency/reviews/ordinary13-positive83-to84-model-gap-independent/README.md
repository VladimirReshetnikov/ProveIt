# Independent source and math review: positive 83→84 gap

This review covers `research/ordinary13-positive83-to84-model-gap-audit/`.
The author's receipt reproduces. The independent checker pins the selected
graphs and relevant source interfaces, compares the complete 83/84 row delta,
checks 350 finite graph substitutions and bounded conditional Pell balances,
and records scoped counterexamples. Run `python3 -I -S -B check.py | cmp -
receipt.json` from this directory. These tests do not prove a model map or
elaborate the cited Lean source.

The 83 graph takes positive w at coordinate 6 and defines `X=q*w`; the 84
graph takes positive X there. The latter adds precisely `E*q` to the main
shift, where `E=X*Y` and `U=Y*q²`. At `X=q*w`, commutativity gives
`E*q=U*w`; consequently the 84 shift `U*gamma_old+E*q` equals the 83 shift
`U*gamma_prime` when `gamma_prime=gamma_old+w`. All other graph rows have the
same named operations and ports. This is an exact ring identity, but the
finite evaluations and row comparison do not themselves construct positive
natural witnesses or check the proposed Lean casts.

For 84→83, if the **actual 84 zero** supplies natural `q>0`, `X>0` and
`q∣X`, the quotient `w` exists and is positive, and
`gamma_prime=gamma_old+w` is positive. One conditional route to q∣X uses
same-graph `X=Exp.exp R`, `q∣3X`, and the represented compact Mersenne form
`q=(Exp.exp d−1)*J+1` with `d≥4`. The cited
`ArithmeticAdaptiveMersenne2011.cancel_three` source has those exact inputs
after rewriting X. The arithmetic control `q=3, X=8` shows why power-of-two
and q∣3X alone are insufficient; it is not a graph zero and does not satisfy
the required compact Mersenne form with natural J and d≥4. No actual-84
proof of these facts is supplied by the audit.

For 83→84, X is already `q*w`, but the needed old gamma is the natural
`gamma_prime−w`. Its strict positivity requires `w<gamma_prime`; separate
positivity of gamma_prime and w does not suffice. The cited
`ModifiedCarrierGammaDraft.gamma_gt_from_modified_balance` is a conditional
fact-level route. It requires the **same** natural Pell coordinate pair
`c=ycoord R a`, `d=xcoord R a`, `a=XY+Y`, `H=4a+3`, `R≥3`, the exact
no-extra-term oriented balance, `k=R+1+U*W`, `U,Y>0`, `q≥1` and `X=q*w`.
It derives `w≤X≤a`; recurrence growth gives
`c≥(2a+3)²>a+Ha≥X+Hw`, while the Pell norm gives `d>(a+1)c`.
Assuming `gamma_prime≤w` then contradicts the subtraction-free balance
`d+H*W=X+a*c+H*gamma_prime`. The U cancellation and all these source
interfaces are unelaborated. No separate projection-quotient growth bound is
needed by this particular fact theorem once its displayed inputs hold.

The R≥3 requirement must not silently disappear: the finite fact-level
control `a=X=w=4`, `R=2`, `W=0`, `gamma_prime=1` satisfies the direct
carrier balance and violates `w<gamma_prime`. This is **not** claimed to be
an actual 83 graph zero; in particular it does not establish the graph-shaped
relations. Likewise the scalar `gamma_prime=1,w=2` is only a domain control.

The actual 83 graph still needs a coherent derivation of its first/main
norms, exact index, same oriented main root/coordinates, k decomposition,
rank and port bounds before that fact theorem can be applied. The proposed
eta-natural 85 early-index client addresses a no-extra-term carrier but uses
another first carrier; the audit correctly leaves the 83→81→85 bridge or a
direct 83 binding as an explicit gap. The residue-90 graph wrapper has an
extra `X*Y*q` and cannot simply replace the actual 83 graph. All source,
provider/axiom, selected-port/PDF and iPRA endpoint obligations remain open.
No mathematical mismatch was found in the inspected conditional cuts.
