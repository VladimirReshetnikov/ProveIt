# Correction to inherited Q45 transport prose

The actual fourteenth residual (zero-based index13) in BOTH quartic45.json and quartic50_source.json is

-F*K0 - F*w - F + J*K0*beta + J*beta*w - J*beta*z - K0*alpha + K0 - alpha*w + w.

With q=beta*J+1 and C=q-F-alpha, this equals exactly

(K0+w)C - F - z(q-1).

The Q45 proof's section4 formula with (z-1)(q-1) is therefore a prose offset error. Its claimed formula differs from the literal residual by q-1. This review checks the identity by symbolic expansion and confirms the two source rows are byte-for-byte equal; hashes and receipt appear in TRANSPORT_CORRECTION.json.

The corrected final restoration conclusion is z>0, not z>1. Once its preceding signed recovery gives X=2^R and R>3q, one has w=X/q>q>F. Since K0>=0 and C>=1, (K0+w)C>F. The correct transport identity gives z(q-1)>0, hence z>0 because q>1. This is exactly the original positivity guard needed for transfer to Q50. No stronger lower bound is needed.

The new Q42 common-sign orientation proof does not use the z transport equation before recovering eta,zeta positivity. It then transfers all literal arithmetic rows unchanged to Q45, with u_old=2u. Accordingly the new reduction is unaffected, provided the inherited Q45 restoration is read with this correction. No source archive or inherited proof was silently modified.
