# Independent review of the two-truth protected-tail argument

I independently checked the mathematical induction for the current K215 command order210 and its command-specific field arities. This is distinct from the earlier MP/DROP/NIP protected-tail result, which cannot be transported merely by changing command names.

For P(a,b)=(a+b)(a+b+1)/2+b and f(n)=second(unpair(n)), candidate n=P(t,y) has conservative first-command balance and suffix pointer:

| t | Command | Balance | Suffix r |
|---|---|---:|---|
|0|NIP|-1|y|
|1|DROP|1|y|
|2|MP|0|f(y)|
|at least3|AX|10|f(f(y))|

A positive suffix executes W(r-1). Set b(n)=balance(W(n)), m(n)=minimum prefix balance including the empty prefix, and B(n)=sum(b(i),i=0..n). Every candidate has at most n+1 commands, and each command decreases the balance by at most one. Thus m(r-1)>=-r. This elementary bound is needed at the variable-length tail of each word, not merely at whole-candidate boundaries.

The independent finite computation reproduced all666 candidates0..665. The minimum global command-prefix balance is exactly-3, min B(n) for6<=n<=665 is7, and B(665)=5762. Since T(36)=666, this is the complete base through Cantor diagonal35.

Use inclusive prefix sums. With g(0)=0 and g(r)=b(r-1) for r>0, G(t)=sum(g(r),r=0..t)=B(t-1), with G(0)=0. The lower bound p is [0,-1,0,-2,-2,-2,-2] on0..6, and7 thereafter. For H(t)=sum(g(f(y)),y=0..t), diagonal decomposition t=T(d)+e gives H(t)>=q(t)=sum(p(j),j<d)+p(e). I independently verified min q=-11 on0..44 and sum of all negative q values on that interval=-224. For d>=9 the complete sum is at least5 and p(e)>=-2, so q(t)>=3 for t>=45.

A second diagonal decomposition gives sum(g(f(f(y))),0<=y<k)>=-224-11=-235. Consequently the first k AX words have balance A(k)>=10k-235. Direct finite evaluation for k=0..25 verifies A(k)>=0 and A(k)+10+m(f(f(k))-1)>=0, interpreting an empty suffix minimum as0. For k>=26, the second bound is at least9k+10-235>=0. Thus every within-AX prefix is nonnegative relative to the start of its diagonal.

On diagonal s the final three words are MP at y=s-2, DROP at y=s-1 and NIP at y=s. Their worst cumulative loss, including within-word prefixes, is at most (s-2)+(s-2)+(s+1)=3s-3. The DROP estimate includes its own +1. Since the AX portion has s-2 words, all final-tail prefixes remain at least10(s-2)-235-(3s-3)=7s-252>=0 when s>=36. Every new diagonal therefore starts and stays at least as high as its initial global balance, maintaining B>=7. All arguments of g used on a diagonal are already below its first candidate, so this is a well-founded induction.

W(0) consists of one NIP and has balance-1. Omitting W(0), as a root with N=1 does, raises every subsequent prefix sum by one. Therefore the global conservative balance from candidate1 is at least-2. For W=5, unpairing yields exactly5=P(0,P(0,1)): two theorem-valued truth entries above the arbitrary tail1. Every NIP pop consumes a member of the theorem-valued prefix; the tail1 is never read. Successful MP can only add a further truth entry, strengthening the bound. NIP may halt before its counted pop, but then its previously established cache theorem is1, so the implication from halt to a refutation remains valid.

This establishes the ordinary source-level soundness argument for initial registers [1,0,5,0,0,0,0,0,0]. Completeness uses the inherited arbitrary-retained-tail strong proof compiler and cofinal successful-code family, as explicitly re-established for the command-local field reader. It needs no theoremhood premise for the unreachable retained tail. I did not independently rerun the binary6176-case proof or complete startup; those are separate premises supplied by the machine agent. This note is an ordinary mathematical review with a complete finite induction base, not a proof-assistant kernel result.
