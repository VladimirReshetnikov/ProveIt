# Protected credit for the corrected scratch-biased scheduler

**Scope:** this proves the abstract scheduler specified by the historical short-transfer README, conditional on a corrected outer return to the actual scheduler root. The originally delivered `scratch-biased` table does not implement these equations: its inserted return goes to the selector instead. This result must not be applied to that uncorrected table.

## 1. Syntactic recurrence and a pointwise bound

Use the finite words W(n) and ending bits e(n) from `seven_shift_synchronizer.md`. Put w(n)=the number of S commands in W(n), and let ell(n) be its total number of commands. With f the right Cantor projection, define h(0)=0 and h(r)=w(r) for r>0. On the Cantor diagonal n=T_s+y, 0<=y<=s, the selector is s-y, so

    w(T_s+y)=h(f(f(y)))       (0<=y<=s-2, AX),
    w(T_s+s-1)=h(f(s-1))     (MP),
    w(T_s+s)=1+w(s-1)        (S, s>0).

The exceptional w(0)=1.

For every n, f(n)<=n/2: P(a,b)>=P(0,b)=b(b+3)/2>=2b for b>=1, while b=0 is immediate. Every nonempty continuation r in W(n) therefore satisfies r<=(n-2)/2. For S this follows from r=f(n)-1; for MP from r=f(f(n))<=n/4, with the n<4 cases terminal; for AX from r=f^3(n)<=n/8 and n>=3. Induction gives

    w(n)<=ell(n)<=floor(log_2(n+2)).                 (1)

Indeed 2(r+2)<=n+2 at every nonterminal step.

## 2. The global S-count theorem

**Theorem:** for every N>=0,

    sum_{0<=n<N} w(n) <= N.                         (2)

The finite base for all N<=T_1024=524800 is checked by the included standard-library integer program. Its recurrence uses strict previous indices; it checks every prefix, not only the endpoint. The final sum is 210396 and max w(n)=5. This is a finite component of the proof, independently reproducible; the induction below covers every larger natural N.

We use a prefix-majorization lemma. If sequences a,b satisfy sum_{i<k}a(i)<=sum_{i<k}b(i) for every k, then their pullbacks by f satisfy the same inequalities. This follows because f(0),f(1),... consists of the consecutive blocks [0],[0,1],[0,1,2],.... Every initial segment is a concatenation of whole blocks and one initial block. The lemma iterates to f^2.

Suppose (2) holds through T_s, with s>=1024. As w(0)=1, every needed prefix of h is bounded by the corresponding prefix of u, where u(0)=0 and u(r)=1 for r>0:

    sum_{r<k}h(r)<=k-1=sum_{r<k}u(r)  (k>=1).

Only k<=s is needed, hence all these inequalities precede the current diagonal. Put

    Z_2(k)=#{0<=y<k : f(f(y))=0}.

The pullback lemma implies, for the first k AX candidates of the current diagonal,

    sum_{y<k} h(f(f(y))) <= k-Z_2(k).                (3)

This proves (2) at every prefix wholly inside the AX part. To add the last MP and S candidates it suffices that

    w(s-1)+h(f(s-1)) <= Z_2(s-1)+1.                (4)

Indeed the AX part has length s-1 and credit Z_2(s-1); MP contributes h(f(s-1)), and S contributes 1+w(s-1). Their total is at most the diagonal length s+1. The same inequality also suffices for the prefix ending immediately after MP.

To prove (4), choose m>=10 with 2^m<=s<2^(m+1). By (1),

    w(s-1)<=m+1,
    h(f(s-1))<=m,

because f(s-1)+2<2^(m+1). Every triangular number has right projection zero, and therefore also second right projection zero. Consequently

    Z_2(s-1) >= floor(sqrt(s-1))
             >= 2^floor(m/2)-1
             >= 2m.

The last inequality holds at m=10 and m=11 and propagates separately along both parities by doubling the exponential term. Thus the left side of (4) is at most 2m+1 and the right side is at least 2m+1. This closes the induction, including every partial diagonal.

## 3. Any every-other-or-denser sampling has enough eventual credit

Assign conservative command balances AX=+10, MP=0, S=-1. The actual successful MP's extra truth push is ignored, so actual explicit safe-head count is at least its conservative count.

For a launched candidate n in the actual schedule beginning at candidate 1, let V be the set of completed launched candidates before n. Every gap is 1 or 2, so |V|>=floor((n-1)/2). There are at most two non-AX first commands on each Cantor diagonal, hence at most 2(sqrt(2n)+1) among all candidates below n. Therefore V contains at least

    floor((n-1)/2)-2(sqrt(2n)+1)

candidates whose first command is AX. Count only those positive AX contributions, but count all S commands in every candidate below n. By (2), the balance before n is at least

    10 floor((n-1)/2)-20(sqrt(2n)+1)-n
    >=4n-20sqrt(2n)-30.                            (5)

Any command prefix inside W(n) can lose at most ell(n) further credit. By (1), its balance is therefore at least

    4n-20sqrt(2n)-30-floor(log_2(n+2)).              (6)

For n>=128, sqrt(2n)<=n/8 and log_2(n+2)<=n/2; (6) is at least n-30>0. This estimates every command prefix, not just completed candidates, and does not assume fairness or a particular pattern of skipped candidates.

For the actual initial bias b_*=1, direct exact calculation of the launched candidates below 128, their balances and their minimum prefix balances gives minimum 0. The included checker records these data. Together with (6), this proves that the entire syntactic schedule beginning at candidate 1 and bias 1 has nonnegative conservative balance at every command boundary.

## 4. Application to the physical partial-AX seed, if the return is corrected

The matched startup enters the inherited AX macro from the logical seed with next candidate N=1, empty residual, top/cache/offset zero, and arbitrary numerical stack tail 3. At the end of that AX, its ten generated heads are numerical theorems, its top/cache are theorems, and the corrected extra CI6 creates parser bias 1. The theorem just proved says that none of those ten initial explicit theorem heads is ever needed to cover a negative conservative balance. At least ten safe heads remain above the opaque tail at all command boundaries.

A shift can therefore only remove an explicitly represented theorem head. MP and AX preserve theorem-valued top/cache; a halt tests the theorem-valued cache for code 1. Every halt yields a native refutation. No theoremhood or decodability is required of the buried tail 3.

As in the inherited credit proofs, explicit list length is a logical witness, not the size of its numerical encoding. The zero alias P(0,0)=0 causes no problem because unpair(P(x,v))=(x,v) holds exactly. A zero head may be counted in the wrapper even when pushing it above a zero tail leaves the integer unchanged.

Combining this soundness result with the seven-shift cofinal compiler establishes the abstract corrected source's equivalence to native refutability. A complete 215-state result additionally requires a corrected concrete table, arbitrary-value primitive runtime, and exact blank startup. The uncorrected delivered scratch-biased table is excluded.
