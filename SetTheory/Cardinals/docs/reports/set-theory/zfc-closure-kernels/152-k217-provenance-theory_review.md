# Independent mathematical review of the incoming dominated-rho8 construction

Reviewed on 2026-10-20 America/Los_Angeles by the formalism research agent.

## Positive calibration result

The incoming `K218_Dominated_Rho8_2026-10-20.zip` contains a sound ordinary finite-proof reduction from unrestricted rho8 to its restriction U <= A. I read the full argument, the compact proof checker, and the command compiler, and freshly ran the compact checker on the frozen unrestricted-row certificate. The run accepted 3,728 proof nodes, 5,160 shared terms, 1,260 restricted leaves, one truth leaf, 55 substituted MP steps, 410 substitution steps, and 2,002 ordinary MP steps. This is an execution of the incoming checker plus independent mathematical source review; it is not a new proof-assistant check or a separately authored checker.

At every restricted axiom leaf, U is zero or a literal implication subterm of A, at depth at most four. For native I(a,b)=4P(a,b), P(a,b)>=a,b, so the code inequality holds under every assignment of natural numbers to schema metavariables. The zero equation I(0,0)=0 is explicitly normalized. All subsequent substitutions are instantiations of already proved universally quantified numeric statements; they do not assume an object-language substitution rule. Canonical variable renaming in the substituted-MP rule is legitimate because each node represents a universal schema. The ordinary induction on the certificate therefore proves all unrestricted instances, including assignments to aliased or junk codes.

The source calibration matches the advertised wire order [c+3,z,y,x] and parameters U=d+z, A=U+x, B=h+y, C=c. The first Q uses the incoming cache before adding y. The compiler's reset and selection blocks have consistent stack counts: AX pushes ten entries; restricted rho8 occupies position eight, the generalized cache position nine, and the saved top position ten. The strongest block contract permits arbitrary underlying stack and early halt, so the cofinal padding argument does not need incoming theoremhood for completeness. Soundness requires theoremhood only of the initially accessible formula data.

No defect was found in this logical calibration. Literal binary runtime and startup are separate obligations and were not rerun by this review.

## Additional seed theorem: inherited arbitrary tails for the dominated source

The protected-tail schedule argument in `k217-protected-tail-seed/proof.md` transfers without alteration to the dominated common-input source. Both schedulers consume two Cantor fields for MP/DROP/NIP and four for AX. Both conservatively change explicit theorem-prefix length by 0,+1,-1,+10 respectively. The common-input order of the local AX reads does not affect the suffix pointer. Dominated AX soundness follows from U<=A and the accepted finite theorem.

Thus from a complete command root with N=0 or N=1, L=0, current formula and cache provable, arbitrary additive counter D, and any natural stack W, halting is equivalent to native/ZFC refutability. The run never inspects W: all popped entries were pushed after startup. This theorem is conditional on correct binary execution of that source and a complete represented root frame.

There is also a uniform extension to every candidate cutoff. Let b(n) be the conservative complete stack balance of candidate word W(n), and B(k)=sum_{n=0}^k b(n), with B(-1)=0. From a root cutoff N and L=0, put at least B(N-1) known theorem entries above an arbitrary stack tail. Every subsequent command prefix has conservative relative balance at least -B(N-1), because prefixing it by the omitted words W(0),...,W(N-1) produces a global prefix covered by the existing nonnegative-prefix theorem. Before a NIP, the reserve has at least one explicit entry, since the balance after that NIP is nonnegative. Consequently no NIP reaches the arbitrary tail. Soundness and the existing cofinal completeness compiler establish the same equivalence. Conceptual leading zeros are allowed despite P(0,0)=0 because unpair(P(a,b))=(a,b) remains exact.

This extension enlarges the permissible startup seed set. It does not imply that an arbitrary table or malformed bootstrap reaches such a frame, and it makes no state-saving claim by itself.
