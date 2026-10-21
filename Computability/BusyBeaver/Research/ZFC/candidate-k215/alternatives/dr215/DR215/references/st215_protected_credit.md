# Protected arbitrary tails for the new three-command scheduler

Date: 2026-10-21. Independent all-natural proof for tags S=0, MP=1, AX>=2, with one/two/three fields respectively. This is a new proof; the old four-command protected-tail theorem is not assumed.

## Result relevant to the actual bootstrap

At a complete command root with next candidate N=1, empty proof pointer, theorem-valued top/cache, and at least two explicitly represented theorem heads above any fixed arbitrary stack tail, the new scheduler never exposes that tail. This holds for either S or composite S'=oldDROP;oldNIP;oldNIP.

Consequently the proposed initial AX, which leaves ten theorem heads above numerical tail4 with N=1 and proof pointer0, is sufficient. At least eight protected theorem heads remain at every future command boundary under the conservative count, unless the machine has already halted soundly. The buried falsity codes in tail4 are never loaded into top or cache.

The exact AX-prefix match and whole-tape runtime are separate premises. The exact receipt `evidence/ax_bootstrap_match.json` records the174-primitive source match from AX entry ordinal25 and registers (N,T,W,A,D,H,X,Y,L)=(1,0,4,0,0,0,0,0,0), to ordinal55 and (1,11,2,0,0,0,0,0,0). This proof does not infer that match from the credit computation or replace its binary verification.

## 1. Exact syntactic schedule and conservative balance

Let P be Cantor pairing, f(n) its right projection, and T_s=s(s+1)/2. Thus

    unpair(T_s+y)=(s-y,y),  0<=y<=s,

and f(n)<=n. Define W(n) to be the finite command word parsed from freshly fetched candidate n, disregarding possible semantic halts. Let R(0) be the empty word and R(r)=W(r-1) for r>0. This accounts for the decrement before every subsequent command, but not before the first command of a new candidate.

If unpair(n)=(a,y), the exact recurrences are

    W(n) = S;R(y)              if a=0,
    W(n) = MP;R(f(y))          if a=1,
    W(n) = AX;R(f(f(y)))       if a>=2.

Payload values are irrelevant to the conservative balance but are still read: one field total for S, two for MP, three for AX. In particular, the AX suffix here is f^2(y), not the f^3(y) of the older four-field AX scheduler.

Assign balances S=-1, MP=0, AX=+10. Successful MP may push a further theorem zero; ignoring that extra push only weakens the safety bound. Both S and S' have net balance-1 on a nonhalting execution.

Write b(n) for the balance of W(n), m(n) for its minimum prefix balance including the empty prefix, and

    B(k)=sum_{0<=n<k} b(n).

Put g(0)=0 and g(r)=b(r-1) for r>0.

Each W(n) has at most n+1 commands. Indeed it has one initial command followed, if its residual r is positive, by W(r-1), where r<=n. Induction gives length<=1+r<=n+1. Therefore R(r) has at most r commands and every prefix of R(r) has balance at least-r, since every individual command has balance at least-1. All these words and balances are well-defined by strict descent in candidate index.

## 2. Prefix-pullback lemma

If a sequence q(0),q(1),... has nonnegative initial partial sums, then q(f(0)),q(f(1)),... also has nonnegative initial partial sums.

Proof: the values of f in increasing input order are the concatenation

    [0], [0,1], [0,1,2], ... .

An initial segment is a concatenation of complete such blocks followed by one initial partial block. Each corresponding q-sum is nonnegative. Applying the argument twice proves the same assertion for q(f(f(y))). Only the finite partial sums actually used are needed.

The crucial shift for the new tags is to use

    q(r)=g(r)+1,

not g itself. For every k>=1,

    sum_{0<=r<k} q(r)=1+B(k-1)+(k-1).

Thus the hypothesis B(j)+j>=0 supplies the needed nonnegative q-prefix sums. The unshifted B(j)>=0 premise would be false for these new tags.

## 3. Every diagonal s>=2 is prefix-safe

We prove jointly by induction on the Cantor diagonal that:

1. B(k)+k>=0 for every completed candidate prefix k;
2. B(T_s)>=-3 at each completed diagonal boundary;
3. for every s>=2, concatenating W(T_s),...,W(T_(s+1)-1) has nonnegative balance at every command prefix, relative to the start of that diagonal.

The exceptional candidates are exactly

    W(0)=[S],         b(0)=-1;
    W(1)=[MP],        b(1)=0;
    W(2)=[S,S],       b(2)=-2.

Hence B(0),B(1),B(2),B(3) are0,-1,-1,-3, and B(k)+k is nonnegative through k=3. This establishes the induction base before diagonal s=2.

Fix s>=2. Along its diagonal, positions y=0,...,s-2 begin with AX, position y=s-1 begins with MP, and position y=s begins with S.

For the first k AX candidates, 0<=k<=s-1, their total balance is

    10k + sum_{0<=y<k} g(f(f(y))) >= 9k.

The inequality follows from the pullback lemma for q=g+1. It uses only previously established B(j)+j inequalities: all required arguments are at most s-2, strictly less than T_s. There is no circular dependence on the current diagonal.

Before AX candidate y, the relative balance is therefore at least9y. Its initial AX contributes10. Its continuation R(f(f(y))) loses at most f(f(y))<=y at any prefix. Thus all prefixes after that AX have relative balance at least

    9y+10-y=8y+10>0.

The candidate's empty prefix has balance at least9y>=0. So every prefix of the initial AX portion is safe, and after all s-1 AX candidates the balance is at least9(s-1).

The next, MP candidate has continuation R(f(s-1)); it loses at most s-1 and its initial MP costs0. Throughout that candidate and at its end, the balance is at least

    9(s-1)-(s-1)=8(s-1).

The last, S candidate initially costs1 and then has continuation R(s), losing at most s further units. Its prefixes, and hence its final balance, are bounded below by

    8(s-1)-1-s=7s-9>0    for s>=2.

This proves diagonal prefix-safety and nonnegative final balance. Since B(T_s)>=-3 by induction, every candidate boundary inside or at the end of this diagonal has B(k)>=-3. Such k>=3, so B(k)+k>=0. The next triangular boundary also has B>=-3. All induction assertions follow.

This proof concerns every natural candidate and every command prefix, including the final S candidate's recursively parsed suffix. It is not an empirical average or an inference from a finite search.

## 4. A finite exact conservative credit at any cutoff

Given N, choose s with T_s<=N<T_(s+1), and define

    E(N)=max(3,T_(s+1)).

Let d(N) be minus the minimum prefix balance, including the empty prefix, of the finite word

    W(N); W(N+1); ...; W(E(N)-1).

Every later whole diagonal has index at least2 and nonnegative relative prefix balance by Section3. Therefore d(N) is exactly the conservative credit required for the entire infinite syntactic schedule starting at N. It is computable by a finite recurrence, and is not a truncation heuristic.

For a nonempty initial proof pointer p>0, first execute R(p)=W(p-1). If its balance/minimum are b,m, sufficient and exact conservative credit is

    max(0,-m,d(N)-b).

The actual machine may need less credit because successful MP adds a zero; the statement is exact for the conservative assigned balances.

In particular, E(1)=3 and W(1);W(2)=[MP,S,S], so

    d(1)=2.

Other initial values are d(0)=3, d(2)=2, d(3)=0, d(4)=d(5)=1, d(6)=d(7)=0, d(8)=4, and d(9)=3. Every triangular cutoff T_s with s>=2 has d(T_s)=0.

## 5. Protected-tail soundness

Represent the current stack as a finite list of explicit theorem heads above a fixed arbitrary tail J. No theoremhood or numerical decoding restriction is imposed on J. Assume current top/cache are theorems and the initial explicit list has length at least the required credit.

Track its length using the conservative balance. AX prepends ten theorems: eight axiom rows, a generalization of theorem-valued incoming cache, and saved theorem-valued top. Failed MP changes no heads; successful MP adds theorem0. S removes exactly one head. Immediately before an S, the conservative length is at least1, because its post-S conservative length remains nonnegative. Thus S always removes an explicit theorem head rather than a head from J. Its top/cache transfers preserve theoremhood.

For S', the internal DROP temporarily pushes a theorem top, the first old NIP removes that temporary head, and the second old NIP removes the explicit head guaranteed above. The extra guard tests theorem-valued top, so every halt still certifies theorem1. The same boundary credit is sufficient despite S' having two internal pops.

The protected length counts an explicitly maintained finite wrapper list, not the size of the numerical encoding. This distinction handles every zero alias: although P(0,0)=0, the exact identity unpair(P(x,v))=(x,v) holds for all natural x,v. An explicitly represented zero above a zero tail can therefore be pushed and later removed in the invariant even when the encoded integer is unchanged. No injective encoding of list length is assumed. The same observation justifies ignoring or counting a successful MP zero push on a numerically zero stack.

Hence the arbitrary tail is never exposed at any command boundary or loaded into top/cache. Halt implies a native refutation. If a semantic halt occurs before the syntactic schedule completes, the argument applies to its finite prefix; ignoring halts while defining W does not assume nonhalting.

Conversely, the already independently reviewed strong compiler succeeds from every top/stack pair after an initial AX resets counter/cache. Its cofinal successful candidates are unchanged. Protected-tail inputs therefore also satisfy the same native-refutation equivalence, without a theoremhood assumption on J.

## 6. Application to the matched partial AX bootstrap

The synthetic complete AX begins at (t,w,d,h)=(0,4,0,0), with private label c=0 and increments x=y=0. Its output is

    top=0, counter=0, cache=0,
    stack=[R1(0,0,0),...,R7(0,0,0),L(0,0,0,0),Q_0 0,0;4].

All ten displayed heads are native theorems. The gate is0 because c=A=B=0. The scheduler still has next candidate N=1 and empty proof pointer. The arbitrary numerical suffix4 does contain falsity heads, since4=P(1,1) and1=P(1,0), but Section5 does not use them.

By the all-natural AX contract, its remaining computation from the exact ordinal55 prefix terminates and reaches that protected root. Section4 requires only2 heads there; the actual10 leave a permanent conservative margin of8. Therefore a complete literal run to the matched ordinal55 frame, plus the verified whole-tape primitive simulation and AX contract, suffices. One need not literally simulate the astronomically large generated formula codes to the later root.

The source-prefix match must include the complete register store, exact ordinal, scratch/address frame, and scheduler fields. A plausible partial tape or register coincidence would not be enough. This audit establishes the new credit bridge; it does not substitute for those separately verified physical premises.

## 7. Independent finite corroboration

Owned script `check_transfer_credit.py` imports only the Python standard library and does not execute received repository code. It checks the exact new recurrence for500,000 candidates, compares1,000 explicit command words, and verifies997 complete diagonals. It reports global minimum command-prefix balance-3 and d(1)=2 in `TRANSFER_CREDIT_CHECK.json`.

Those finite results corroborate the equations and indexing. Sections1-5, not the finite bound, prove the unbounded theorem.
