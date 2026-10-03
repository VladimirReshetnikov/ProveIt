# Independent bounded review of the joint strong/auxiliary census

**PASS, no requested correction.** This review targets the frozen [scout source](complete86_joint_strong_auxiliary_scout.py), [receipt](complete86_joint_strong_auxiliary_scout.json), and [proof note](complete86_joint_strong_auxiliary_scout.md). It independently reconstructs all twelve saved best complete circuits and their paid chart identities. It also reads the entire census implementation and checks its finite coverage combinatorics. It does **not** independently regenerate all292,320 costed schedules or their58,113 distinct local DAGs; those are authenticated author results, whose exact replay passed separately. This boundary is included in the machine-readable review receipt.

The reviewed pins are:

- Source: `24728e3c3bd4f3b24a929ad816b9a4b4110678923ca50499dcf02c96eb6ac61f`.
- Receipt: `dc2d26d1f88144bf92fe5e867c78669531a5f117075ab691d98486f60254e810`.
- Note: `1501ac846c4d617d37df8db144ae0388b4826c69355c0da3f18f3bafc475f9c6`.

The [independent helper](review_complete86_joint_strong_auxiliary_scout.py) authenticates all three plus the complete86 parent source/receipt/note before parsing any source descriptors. It imports none of the author's functions. The [review receipt](review_complete86_joint_strong_auxiliary_scout.json) is portable and records its own helper hash.

## Mathematical identity and paid interface

Use A for the actual discriminant, c for the actual computed `R10a`, and put

    t=i*c², Q=A*t², H=A*t, K=A*Q=H²,
    Ns=f²−Q, Na=K*(V²−y²)+y².

The target is the product NsNa. The six chart targets expand to exactly that polynomial after substitution of the actual source ports. In particular `shared_H=i*Ac2`, where the retained main norm already computes `Ac2=A*c²`. Its one multiplication is present whenever used; no chart treats H as a newly free supplied coordinate. The helper verifies each chart independently over the six formal indeterminates A,i,c,f,V,y, then expands the actual paid complete-circuit cones at those six cuts. This is an unconditional integer-coefficient polynomial identity; no unit sign, rank, positivity or vanishing premise is used.

The six other factors—first norm, main norm, input norm, packed index, transport and coupled linear factor—have identical complete expression DAGs, modulo commutation of addition/multiplication, in each saved circuit. At these six verified cuts and the proved joint-factor cut, the full final output is precisely the same eight-factor product minus1. The final subtraction and every product remain charged. The review proves this for all twelve complete saved circuits, separately from testing their outputs numerically.

It follows that the parent ordinary-input relation, all19 positive coordinates, positive-zero fibers, sign/rank conditions and exact degree179 are unchanged. No new coordinate projection or fresh universality hypothesis is introduced. Exact degree179 is inherited by full polynomial equality; this review does not redo the parent's degree certificate.

## Complete arithmetic and finite search scope

Every saved row is a binary addition, subtraction or multiplication, including squares and multiplications by nonunit constants. Independent topological checks find exactly the parent's complete free-coordinate set:19 witnesses, ordinary input x, and six fixed compiler numerals. Independent liveness traversals recount all1,040 gates across the twelve saved sources. Applying the same constant-folding/zero-one/CSE rules independently leaves the baseline at86 and each saved representative's count unchanged.

|Chart|Monomial mode|Deterministic binomial mode|
|---|---:|---:|
|QK|87=49M+38A|86=48M+38A|
|QA|87=49M+38A|86=48M+38A|
|T2A|88=50M+38A|87=49M+38A|
|tH|87=49M+38A|86=48M+38A|
|Raw tH, separate powers|87=49M+38A|86=48M+38A|
|Raw tH, joint squares|87=49M+38A|86=48M+38A|

The coverage claim is precisely six charts, two deterministic factoring modes, all203 set partitions of six signed terms and120 shared orders of five variables. The independent helper enumerates the203 partitions using restricted-growth words, checks every saved representative's partition/order membership, verifies all histogram totals and minima against the actual saved sources, and obtains6*2*203*120=292,320. The inspected source loops iterate exactly that Cartesian product. Distinct-source counts are summed **within** the twelve chart/mode groups;58,113 is not a claim of globally distinct circuits.

The grammar's limitations are accurately stated in the author note: fixed descending term order; canonical block order and fixed block accumulation; one common Horner order per schedule; fixed binary powering; recursive common-monomial extraction; and optionally the first sorted exact primitive unit-coefficient binomial divisor with a nonconstant quotient. It does not explore every divisor, block bracketing, addition chain, algebraic intermediate or coordinate change. The joint-square rule is also limited to the declared all-even monomials. The scope therefore supports a bounded negative result, not a general cross-factor lower bound.

The full author histogram and ordered-census hash are authenticated and checked for internal consistency here, but their complete per-choice costs are not independently re-enumerated. This review's exact polynomial proofs and gate recounts apply to all twelve saved minima. The author's source itself checks exact local polynomials, six unchanged factor DAGs and full finalizers for every distinct schedule; that code and the complete companion explanation were read.

## Reproduction and evidence

Use a Python environment with SymPy:

    /path/to/research-venv/bin/python review_complete86_joint_strong_auxiliary_scout.py \
      --source /path/to/complete86_joint_strong_auxiliary_scout.py \
      --receipt /path/to/complete86_joint_strong_auxiliary_scout.json \
      --note /path/to/complete86_joint_strong_auxiliary_scout.md \
      --root /path/to/native-stream-queue \
      --expect /path/to/review_complete86_joint_strong_auxiliary_scout.json

The independent receipt records six paid chart substitutions;12 generic local identities;12 actual paid joint-polynomial identities;72 unchanged-factor DAG identities;12 complete final-output cut proofs;144 signed output checks, including48 rational tuples;1,040 independently recounted live gates; and independent203-partition/120-order combinatorics. Numerical samples are supplemental; the coefficient and DAG identities supply the proof. No gigantic universal zero is materialized, no original author suite is rerun, and no repository file is changed.
