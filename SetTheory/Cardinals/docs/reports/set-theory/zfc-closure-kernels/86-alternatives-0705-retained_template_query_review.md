# Independent review: 133-state retained template query

Date: 2026-10-18. Table hash:
`1d0107b3f718a1c2d6fa260e442d568af20f7cd2915dab4db1087cf15184ba4f`.

## Verdict and contract

The exact reverse-copier/mirrored-selector/mirrored-oracle composition is correct.
Its 133 working states comprise 18 copier operational states, one reject,
102 oracle states and 12 selector states; there are 266 rows and return 133.

The source consists of four rule bits for a template rule3..11 followed by a
genuine complete leaf path p of that template. Write d=length(p), n=d+4.
Use the reverse-copy frame with frontier at c, gap>=n+2, five-one sentinel,
biased branch fields, and the final-one marker specified in its reviewed
contract. For the advertised forced-zero emitter guards, additionally require
cells c-1,c-2,c-3 to be zero. Other exterior cells may be arbitrary.

On return, the entire source is restored. Its raw reversed n-bit copy occupies
c..c+n-1 and frontier1 is at c+n, except that the oracle overwrites the path
copy and the three cells immediately to its left: starting at c+d-1 and moving
left, it writes the d expected tag bits and three-bit leaf code. The four copied
rule bits remain unchanged. All other cells are preserved. The final head is
c-4. The input path therefore remains available in the restored unary source;
it is not reconstructed from the potentially ambiguous overwritten output.

## Universal composition proof

The reverse-copy theorem gives exactly the raw reversed n bits, restored source,
frontier and exit head c+n-1. Redirecting its return to the selector involves
no extra movement: the four left-moving selector steps preserve and read the
four rule bits in their original root-first order. They select the appropriate
one of nine template roots and leave the head at c+d-1.

The reflected oracle's tree induction now reads the complete d-bit root-to-leaf
path. Reflecting every move from R to L changes no state logic, write bit, leaf
choice or tag-bit comparison. The following three emitter inputs are precisely
c-1,c-2,c-3, which are untouched before this point. It emits the stated word
and returns at c-4. This proves termination and the complete tape effect.
No callback chooses a root or a path while the literal composed table runs.

## Packing guards

The reverse component preserves forced-one IDs1,2,5,9 and forced-zero IDs0,13,
by its universal proof. The shifted oracle emitter IDs110..120 read only the
three reserved zero cells. At selector state123 (prefix1), the next bit is zero
because allowed rules8..11 all start10. At state124 (prefix00) and state128
(prefix001), only allowed rule3 is possible, so each next bit is one. These
finite rule cases are exhaustive independently of source lengths and exterior
tape. They justify the reviewed conservative guard map:

- forced one: 1,2,5,9,124,128;
- forced zero: 0,13,110..120,123;
- both symbols conservatively at every other state, including unreachable
  prefix000 state127 and reject18.

These selector guards require the template-only rule range3..11. They cannot
be transferred unchanged to a caller that also invokes this component on
truth/MP/GEN opcodes0..2 or malformed selectors. The emitter guards likewise
require the three zero cells at call time; ordinary correctness without those
guards would still permit arbitrary old bits there before overwriting them.

`retained_template_query_133_guards_reviewed.json` binds these proofs to exact
state IDs and table hash. `audit_retained_template_query.py` independently
constructs all frames and enumerates template leaves, then checks 1,368 complete
tapes at translated origins and several gap sizes. All reviewed guards hold
in these runs, with maximum length5,348. The checks supplement the composition
proof rather than replace it.

The component still requires prepared source construction, initial marking,
next-path generation, workspace reuse, routing from query output to native
edge calls, terminal ID comparison, complete proof validation, fair rejection
and blank startup. No total consistency-search machine follows from this table
or a packed library of its ports. No producer artifact was modified.
