# Stack safety for the constant-bias composite-transfer scheduler

This is an all-natural abstract scheduler theorem. Its application to any binary table requires separate exact source binding, universal runtime verification and startup identification. In particular, a source count or finite simulation is not a machine calibration.

## 1. Abstract parser and balances

Let P(a,b)=(a+b)(a+b+1)/2+b and let f be its right inverse projection. The constant bias is1 after every command. The scheduler's predecessor operation and the biased first read cancel, so a positive residual L is decoded by directly unpairing L. At an empty residual, the old counter N is decoded without a predecessor and the counter advances by2. We consider initial candidate1, hence the actual candidate sequence1,3,5,... . The stronger auxiliary result below also permits arbitrary gaps1 or2 starting at1.

Let W(n) be the complete syntactic word of candidate n, ignoring intentional halts. The command tags are S=0, MP=1 and AX(c)=c+2; MP consumes one extra field and AX consumes two. Exact decoding gives:

- W(P(0,y)) is S, followed by W(y) if y>0.
- W(P(1,y)) is MP, followed by W(f(y)) if f(y)>0.
- W(P(a,y)), a>=2, is AX, followed by W(f(f(y))) if positive.

These recurrences terminate because f(n)<n for n>0. The first differs from the earlier feedback-bias theorem: it uses y, not y-1.

Assign balances S=-1, MP=0 and AX=+10. These are conservative for the work-tuple machine: successful MP actually pushes an additional zero; AX adds ten theorem heads above the old stack; composite S removes one head and has the additional permitted top-falsity guard. An earlier intended halt is harmless for the nonhalting-prefix safety argument.

## 2. Universal counting theorem

Let s(n) be the number of S commands in W(n), and put

    A(N)=sum_{n<N}s(n),
    g(0)=0,  g(n)=s(n) for n>0.

Then A(N)<=N for every natural N.

Proof is by strong induction on N. A(0)=0 and s(0)=1. Write T_j=j(j+1)/2. If a nonnegative function u has u(0)=0 and every relevant positive prefix sum is at most L-1, then

    sum_{y<L}u(f(y)) <= L-r(L),

where r(L) is the least r with T_r>=L. Indeed f enumerates the consecutive blocks (0), (0,1), (0,1,2), ... . Each nonempty full or partial block saves at least one against its length. For L=0 the sum is zero.

The inductive bound gives sum_{j<L}g(j)=A(L)-1<=L-1 for L>0. Therefore the pullback bound applies to g and also to g composed with f. Write H(L)=sum_{y<L}g(f(y)) and H2(L)=sum_{y<L}g(f(f(y))); both are at most L-r(L).

At the triangular boundary T_q, q>=2, exact decomposition by root command gives

    A(T_q) = q + G(q) + H(q-1) + sum_{l=1}^{q-2}H2(l),

where G(q)=sum_{j<q}g(j)=A(q)-1. Since q<T_q for q>=2, strong induction gives G(q)<=q-1. Hence

    A(T_q) <= T_q-D_q,
    D_q=sum_{l=1}^{q-1}r(l)-(q-1)>=0.

This is the crucial adjusted boundary term: the constant-bias S contribution is q+G(q), not q+A(q-1). It has the same upper bound2q-1. The boundary q=1 is checked directly, avoiding circular use of A(1).

For a general N, write N=T_q+k with0<=k<=q. If k<=q-1, the extra diagonal prefix contains only AX-root candidates; its cost is H2(k)<=k, proving A(N)<=N. If k=q, the extra prefix consists of q-1 AX roots and one MP root. Its cost is

    H2(q-1)+g(f(q-1)) <= q-1.

For the last inequality, induction implies g(m)<=m for m>0 because g(m) is one term of A(m+1)-s(0)<=m; it holds for m=0 as well. Also f(q-1)<=r(q-1). The q=1 partial case N=2 is direct. All prefix lengths and pointwise indices used in the induction are strictly below N. This proves the counting theorem.

## 3. Uniform resource bound for gaps1 or2

Consider any candidate sequence beginning at1 with consecutive gaps1 or2. Before its candidate n, at least floor((n-1)/2) earlier candidates have completed. Among all indices at most n, at most2q+1 have first command other than AX, where q=floor((sqrt(8n+1)-1)/2)<=sqrt(2n). Therefore earlier root AX commands alone supply at least

    10(floor((n-1)/2)-2q-1)

credits. At every internal position of candidate n, the accumulated S cost across the selected candidates is at most A(n+1)<=n+1. Ignoring every inner AX and every successful-MP push gives the prefix balance lower bound

    10 floor((n-1)/2)-20q-10-(n+1)
       >= 4n-20sqrt(2n)-21.

The right side is positive for n>=64. It is positive at64 and has positive derivative thereafter. The remaining finite domain is covered exactly by a dynamic program over candidates1 through63: for each n, minimize its entering balance over preceding endpoints n-1 and n-2 and then examine every command prefix of W(n). The minimum is-3, attained along candidates[1,2,4,5] inside candidate5.

Consequently three initial theorem heads above an arbitrary opaque stack tail suffice for every such gap-one-or-two sequence, provided the initial top and cache are theorem codes.

## 4. Sharper theorem for the actual odd schedule

For the particular sequence1,3,5,..., the same analytic bound covers every candidate n>=64. Exact evaluation of all command prefixes of the odd candidates1 through63 gives minimum balance0, with final balance254. Thus the cumulative conservative balance is nonnegative at every command boundary of the entire odd schedule.

Equivalently, the odd schedule never needs to pop below its initial opaque tail: before each S, at least one head generated earlier by an AX is available, except for any separately supplied initial safe heads. Successful-MP pushes only improve this bound. A hypothetical first underflow would lower the conservative balance below zero, contradicting the theorem.

## 5. Application to the proposed startup over tail2

The intended startup identification is a partial AX begun at

    (N,T,W,A,D,H,X,Y,L)=(1,0,2,0,0,0,0,0,0).

Do not call stack2 entirely safe:2=P(0,1), and1=P(1,0), so its second decoded head is the refutation code1. Instead, completion of the initial AX supplies ten explicitly tracked theorem heads above this opaque numerical tail. Its incoming top and cache are theorem0, its numerical parameters satisfy the usual AX restrictions, and it resets d=h=0.

The odd-schedule theorem proves that all ten initial heads remain available as a permanent lower margin. Even the stronger arbitrary-gap auxiliary theorem would leave at least seven. Thus no decoded head of opaque tail2 can be exposed during a nonhalting actual computation, and all top/cache halting tests concern genuine theorem codes. This is a soundness argument, not an assumption that the unsafe tail happens not to be reached in a finite run.

The composite implementation S=DROP;NIP;NIP first pushes a theorem top and then pops twice. Its minimum internal wrapper depth occurs at its final depth, one below entry. Therefore the atomic balance-1 also bounds the entire composite execution; neither its top guard nor its cache guard sees an opaque head. AX adds safe heads without consuming the tail, and successful MP adds an extra safe zero.

The wrapper length is a proof invariant attached to an explicit list of theorem heads; it is not asserted to be a uniquely decodable numeric stack length. This matters because P(0,0)=0.

## 6. Exact verification artifacts

The owned checker check_constant_bias_credit.py produces:

- DENSITY_CREDIT_BASE.json: exact finite minimization over all gap1/2 schedules through63, minimum-3.
- ODD_SCHEDULE_BASE.json: exact odd-schedule finite base, minimum0 and exit254.
- COUNTING_BOUND_CORROBORATION.json: independent recurrence checks on200,000 candidates, not used as an extrapolation of the infinite theorem.

The all-natural induction and analytic bound above justify reducing the resource theorem to this finite domain. A binary table is calibrated only after its literal source, physical runtime, startup bridge and inherited logical equivalence are checked separately.
