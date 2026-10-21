# Independent review: zero-spare CB1 scheduler with DROP/NIP/MP order

The new source is the accepted `commands120` source with exactly one additional CB1 primitive at ordinal 9. The complete primitive sequence and source control-flow graph are otherwise transported by the ordinal map j(i)=i for i<9 and j(i)=i+1 for i>=9, except the zero branch of ordinal 7 now reaches the added CB1. The CB1 returns to ordinal 0. `audit_cb120.py` checks these statements on every primitive and every edge, using a separately implemented interval-based control-flow resolver.

## Refill contract

At the source root, let N=R0 be the next counter, L=R8 the residual, and assume scratch X=R6=0. The first primitive decrements L. If L>0, the code reader receives L-1 and N is unchanged. If L=0, the two unary loops move N into L and X, then restore N as its old value plus 1 and clear X. The added CB1 restarts the root. Therefore an old counter n>0 causes the reader to receive n-1 and leaves counter n+1. Counter n=0 makes one additional refill and reads 0 with counter 2. In particular the actual seed N=1,L=0 launches raw candidates 0,1,2,... in order.

The command bodies are unchanged. Their tags/field counts are DROP=0/one, NIP=1/one, MP=2/two, AX>=3/three. Every positive residual is decremented before the next command.

## Zero protected-credit theorem

Write P for Cantor pairing, f for its right projection, and T_s=s(s+1)/2. Define W(n) as the syntactically parsed word of raw candidate n. Let R(0) be empty and R(r)=W(r-1) for r>0. If unpair(n)=(a,y), then

    W(n)=DROP;R(y)           if a=0,
    W(n)=NIP;R(y)            if a=1,
    W(n)=MP;R(f(y))          if a=2,
    W(n)=AX;R(f(f(y)))       if a>=3.

Assign conservative balances DROP=+1, NIP=-1, MP=0, AX=+10. Successful MP pushes an additional theorem zero; ignoring it is conservative. Let b(n) be the word balance, m(n) its minimum prefix balance, and B(k)=sum_{n<k} b(n). Put g(0)=0 and g(r)=b(r-1) for r>0.

The assertion is that the infinite concatenation W(0);W(1);... has no negative command-prefix balance. The initial six words are

    DROP, NIP, DROP DROP, MP, NIP DROP, DROP NIP.

Their cumulative command-prefix minimum is zero and their ending balance is 2.

Assume all preceding diagonals have been handled, and consider diagonal s>=3. Its first s-2 candidates begin with AX, then one begins with MP, then NIP, then DROP. By strict descent W(n) has at most n+1 commands; every prefix of R(r) loses at most r units of credit.

Every prefix of g has nonnegative sum because sum_{r<k}g(r)=B(k-1) for k>=1. Pullback by f preserves this property: f enumerates successive blocks [0],[0,1],[0,1,2],..., so a pullback prefix sum is a sum of old prefix sums. Applying this twice, the first k AX candidates of the diagonal have total balance at least 10k.

Inside AX candidate y, the prior balance is at least 10y, its first AX adds 10, and its continuation loses at most f(f(y))<=y. Thus every such command prefix is nonnegative. After the AX portion the relative balance is at least 10(s-2).

* The MP candidate loses at most f(s-2)<=s-2, leaving at least 9(s-2).
* The NIP candidate first loses one and its continuation loses at most s-1, leaving at least 8s-18.
* The DROP candidate first gains one and its continuation loses at most s, leaving at least 7s-17, which is positive for s>=3.

These estimates apply to every prefix of each final candidate, not only the endpoint. Hence each diagonal s>=3 is prefix-safe relative to its start. This also proves B(k)>=0 at every candidate boundary and closes the induction. No finite cutoff or average-case argument is used.

## Unsafe-tail protection from the actual seed

The exact physical seed has logical registers [1,0,5,0,0,0,0,0,0]. Thus top, cache and offset are zero, while the numerical stack is the opaque tail 5. Start with zero explicitly protected theorem heads above that tail.

DROP pushes a theorem top, AX pushes ten theorem heads, and MP never decreases the explicit protected length. Immediately before any NIP, the prefix-credit theorem guarantees at least one explicit head: the count after its decrement remains nonnegative. NIP therefore never pops from tail 5. Its falsity test, as well as every later top/cache value, is theorem-valued. Every halt consequently yields a native refutation. The argument permits arbitrary junk in tail 5 and does not decode it as a theorem stack.

The exact identity unpair(P(x,v))=(x,v) justifies the protected wrapper even for zero heads and zero-tail aliases. Logical wrapper length is not inferred from the numerical code's magnitude.

Conversely, the inherited strong compiler works with arbitrary incoming top and numerical stack after a resetting AX. Since this scheduler visits all raw candidate codes, its cofinal refutation encodings are reached unless a prior semantic halt already occurred. The accepted command-language calibration therefore transfers to this scheduler from the stated seed.

**Review conclusion:** the new refill contract, zero-credit induction, arbitrary-tail safety, and completeness transfer are valid. Their application to the binary table still uses the separate fresh arbitrary-value primitive-runtime proof and exact blank-frame check. This review does not certify that runtime checker or a new proof-assistant endpoint.

## Stronger tag-lowering proof: independent audit

The subsequent `formalism_work/tag_lowering_credit.md` provides a stronger and simpler proof, which I independently reviewed and accept. It assigns **zero credit to both AX and MP** and nevertheless proves every command prefix has at least as many DROP occurrences as NIP occurrences.

For each NIP occurrence at position j in the complete raw-candidate word W(n), replace that one command with DROP and re-encode the entire word as m. Both commands have one field, so their replacement preserves every command boundary and the same position j. Locally,

    P(1,r)-P(0,r)=r+1>0.

Every enclosing pairing and successor is strictly increasing, so m<n. The encoding's two inverse identities include raw zero: rho([DROP])=0, while a nonempty continuation containing that command is stored as 1, so no final command disappears. Zero-valued MP/AX payloads also cause no ambiguity because their arities are fixed by the selector.

The image occurrence (m,j) uniquely recovers its source by raising that DROP tag back to NIP and re-encoding. This is an injection from NIP occurrences to DROP occurrences in earlier completed candidates. If an actual NIP is reached, none of those earlier candidates has halted, so all image DROP occurrences have actually occurred. The argument therefore applies to actual execution prefixes as well as the infinite syntactic word.

This proves protected-tail safety without counting any AX-produced or successful-MP-produced head. The zero-initial-credit conclusion holds for every natural opaque tail J from the same N=1, L=0, T=H=0 seed. The stronger tag-lowering proof is the recommended main exposition; the diagonal proof above remains an independent, more quantitative route for the existing ten-head AX interface.
