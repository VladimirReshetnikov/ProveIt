# Root review of the nonnegative polynomial reachability boundary

PASS for the exact finite quotient, path lifting and uniform decidability
obstruction at the stated finite-instance interface. This excludes one
specific proposed universal-history simplification; it does not give a
global operation lower bound or invalidate the signed current substrates.

Let K exceed every threshold and let M be a common multiple of all test
moduli. Root checked that pi(n)=(min(n,K),n mod M) preserves both addition
and multiplication on N. The only nontrivial saturated-product case has
one positive factor at least K, which forces both products to saturate.
If either factor is zero both products are zero. This handles resets
without a monotonic-growth assumption. Polynomial evaluation and updates
therefore commute with pi by induction on their expressions.

The image has exactly K+M elements: K distinct unsaturated integers and
M saturated residue classes. Every threshold atom is determined because
its threshold is strictly below K; every modular atom is determined
because its modulus divides M. Boolean negations and combinations do
not weaken this exact predicate preservation.

For any reachable abstract edge sequence, start from the actual given
integer vector. At each step its image is the recorded abstract state;
the exact guard is true, and the concrete successor maps to the abstract
successor. Thus every reachable abstract path lifts, including paths
after merged states or resets. Acceptance is exact in both directions.
There are |Q|(K+M)^d abstract configurations, so finite graph search
decides acceptance. A shortest accepting path has at most that number
minus one edges. The author's extra control flag correctly handles a
nonempty-path requirement.

Even when all finite instance data are computed from program and input,
a total computable compiler followed by this finite search terminates.
It cannot faithfully represent a nonrecursive language. No efficiency
claim is needed. The proof does not apply to existentially guessed
unbounded initial data or thresholds subject to external constraints.

Root checked the numbered boundaries directly. Positive guarded decrement
and division fail the cap identity at the displayed pairs. The more
general K,K+M decrement sequence is legal for K-1 steps and ends at1
and M+1, with different caps. The two saturated coordinate pairs can
disagree on equality. Also (X-Y)^2 has coefficient-2 on XY even though
its values are nonnegative. These distinguish coefficientwise positivity
from positivity on a domain. The powers-of-two input example correctly
refutes an additional semilinearity/ultimate-periodicity inference when
the threshold varies with input.

The previous Boolean nonnegative-matrix mortality argument is the
K=M=1 special case, explicitly credited. The positive Markov-mask lift
really retains signed Fourier-coordinate actions and a duration scale:
at r=1,M=[-1] its mask1-(2/3)cos(4*pi*x) is positive but its coordinate
action is multiplication by-1/3. The counter example retains decrement;
the group certificates retain signed polynomial equations and variable
relations. None satisfies the new restricted coefficient/test interface.

Root read the full final author note and metadata, the full Markov mask
and positive-guard notes, group Gram lines180--235, group tail-quotient
lines1--115 and unsquared-product lines1--90. These corroborate the
specific context claims; no whole ancestral compiler audit is asserted.
The companion verifies all six author dependency/span bindings, which
does not enlarge root's mathematical reading coverage.

No scientific program or sample sweep was run. No supplied, frozen,
archived or predecessor helper was imported or executed; no source array
was evaluated or propagated. This is a self-contained proof review with
metadata-only authentication. No additional correction was required.

Frozen author proof SHA256:
`a758a4f4e023831176dc1cf9dd2f957ea366a7e8231276317f6114a5b0731237`.
Frozen author metadata SHA256:
`eeba9cfd19adc13a4ca09c8afe67d2a7644972c59e176bfa1bf6376cae3399ce`.
