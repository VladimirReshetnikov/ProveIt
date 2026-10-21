# Adjacent universally successful candidates for the intended biased scheduler

This is a separate conditional theorem. It does NOT calibrate the rejected literal table in this packet. It applies to an enumerator whose real command contracts and scheduler implement the equations below.

Write P(a,b)=(a+b)(a+b+1)/2+b and let f be its second inverse projection. The intended commands are S with fields [0], MP(x) with fields [1,x], and AX(c;x,y) with fields [c+2,y,x]. The scratch bias after S is 0 and after MP or AX is 1. At a positive residual r, the scheduler first reads r-1+b, where b is the incoming bias. A freshly fetched candidate is read without bias.

Let W(n) denote the fresh-candidate word. If unpair(n)=(a,y), its continuation is:

- a=0: S, followed by W(y-1) when y>0;
- a=1: MP, followed by W(f(y)) when f(y)>0;
- a>=2: AX, followed by W(f(f(y))) when that residual is positive.

Each recursive argument is smaller than n. This includes the nontrivial MP and AX cases because their positive selector makes y<n. Thus every finite candidate word drains unless it halts first.

Suppose r>0 is a fresh encoding of a command word V that halts from every natural work tuple. Such a word can be obtained from the inherited arbitrary-tail strong compiler by prepending an AX reset to a refutation suffix, provided the stateful wire compiler really implements these equations. The premise is universal over top, stack, counter and cache; theoremhood is not required.

For any integer v>=1, set

u=P(1,r), y=P(v,u), n=P(2,y).

Three exact Cantor identities give

n+1=P(1,y+1), y+1=P(v-1,u+1), u+1=P(0,r+1).

Therefore the fresh candidate n executes AX(0;1,v), followed by W(r). The adjacent fresh candidate n+1 executes MP(v-1), followed by W(u+1), which executes S and then W(r). Both candidates halt from every work tuple: any earlier halt already suffices, and otherwise the common universally halting suffix is reached. No equality of initial stores is assumed.

Since n grows without bound as v grows, successful adjacent pairs occur above every cutoff. Any increasing candidate sequence with jumps 1 or 2 must meet at least one member of each sufficiently late adjacent pair. It cannot jump over both consecutive numbers. Consequently the intended stateful scheduler is refutationally complete once the strong compiler, literal parser correspondence, and an actual-run soundness invariant are separately established.

For reference, a stateful wire compiler for a finite word k::K is E_b(k::K)=1-b+F(fields(k),E_bit(k)(K)), with E_b(empty)=0 and F the right-nested field packing. The only possible zero collapse of a nonempty word is E_1([S])=0. A refutation ending with a sufficiently long transfer suffix, such as the inherited H=AX;S^11, avoids that terminal one-S degeneracy. The fresh encoding omits the first outer 1-b. These encoding and soundness premises must be bound to any repaired literal source before using this lemma for a Turing-machine claim.

verify.py independently checks all three identities and exact first-command continuations for 3,000 small parameter pairs. The algebra above, not that finite check, establishes the unbounded result.
