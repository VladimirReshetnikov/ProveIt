# Independent review of the odometer initializers

Reviewed 2026-10-17 against the packaged construction in `code/initializer/`,
with the ProveIt backend pinned to
`61e77836565f63582561f54745f633d50efd9c7d`. This review concerns
`odometer_initializer.py`, `integrate_odometer.py`,
`share_odometer_exit.py`, `exact_state_quotient.py`, and the eight selected
literal controls in `machines/initializer/`, described by
`data/initializer/final_controls_summary.json`. It is an ordinary
mathematical and source review, not a Lean kernel check.

## Result

I found no incorrect transition, count, endpoint, or quotient claim in the
eight selected controls. The single-sentinel zero variant uses 32 private
states before sharing at n=9, reaches its frame in 269,328 steps, and uses
31 private states / 269,348 steps after sharing the existing return path.
The seed-two variant uses 33 before sharing and 32 afterwards, and reaches
its final frame in 269,349 steps with sharing. The smallest selected totals
are respectively 299 and 300 working binary states after the additional
one-state exact quotient.

These numbers concern the supplied complete control tables and their
declared initial register vectors. They do not by themselves prove a new
Con(ZFC) equivalence or a new Busy Beaver record. The source DAG's logical
endpoint and the remaining compiler metatheory retain their existing
status. In particular, the two initial vectors must not be identified
without the source program's entry-condition argument.

## 1. Whole-tape invariant

Write n for the counter width and N=2^n-1. The machine has a two-way infinite
binary tape, initially zero everywhere, and starts at coordinate 0. The
writer visits fresh cells monotonically to the left. If it prints W cells,
its last cell is m0=-(W-1). Immediately after the last write, the tape read
from left to right is

    1 0 11 (01)^n 11

for the original register-clock version; an unchanged register payload
follows for the auxiliary version. For the zero-only refinement the tape
ends instead in a single terminal bit:

    1 0 11 (01)^n 1.

These are notation for finite tape words, not a diagram of control flow.
The initial isolated 1 is the movable marker at m0. The fixed left sentinel
is the adjacent pair at m0+2,m0+3. Counter separator i is at m0+4+2i and
counter bit i at m0+5+2i, for 0<=i<n. Bits are little-endian. Initially they
are all one, so the counter has value N. Three transitions after the last
write enter `dec_sep` at the low separator m0+4.

At this header, after j successful decrements (0<=j<=N), all of the following
hold simultaneously:

* The head is m0+4 in `dec_sep`.
* The counter has value N-j; its separators are all zero.
* The movable marker is the sole one strictly left of the sentinel, at
  m0-j. Every other cell strictly left of m0+2 is zero.
* Both left sentinel bits, the terminal bit(s), and any auxiliary payload
  are unchanged.
* No cell outside the explicitly described finite support is one.

For a positive counter v=N-j, `dec_bit` changes each trailing zero to one,
passes its separator, then changes the first one to zero and turns left.
This subtracts one. `back_scan`/`back_test` can encounter no adjacent ones
within the counter because all separators are zero. They therefore detect
the fixed left sentinel and enter `find_marker` at m0+1. The scan reaches
the unique marker, erases it, and writes the next marker one cell farther
left. `seek_sentinel` passes only zeros until the first sentinel bit, and
`skip_sentinel` reads the second sentinel bit. The header is restored.

This proves the invariant by induction. It also proves that each newly
written marker cell was zero and that every cell to the left of the marker
stays zero. The latter fact is essential for sharing the eventual return
path; it is stronger than merely recognizing the visible output prefix.

When v=0, the same decrement walk changes all n bits to one, then enters
`dec_sep` on the first terminal one. This is the unique underflow branch.
There is no additional marker shift. The counter's one bits can now serve
as zero-valued unary register blocks.

## 2. Borrowed transition guards

The code reuses transitions on symbols excluded by phase invariants, not
states assumed to be unreachable without proof.

During the initial monotone print, each visited tape cell is fresh and
zero. The subsequent odometer always reaches `skip_sentinel` on the second
left-sentinel one. Its read-zero transition is therefore free for the
writer. In auxiliary cleanup, `clean_bit` reads counter bits restored to
one, followed by a sentinel one; its read-zero transition is also free for
the writer. In the original zero register cleanup, `erase_right` reads the
second terminal one. The seed-two route never executes that cleanup row.

The seed-two modifications affect only read-one rows of selected `seed`
states. None is read during the monotone writer. Their new uses are fully
determined by the all-one counter produced by underflow. Rows used on
intervening separators remain their original read-zero writer rows.

For the single-sentinel refinement, the old first writer cell is removed
by starting at `erase_right`; its old next state `seed2` is replaced with
`skip_sentinel`, whose read-zero row absorbs the identical `seed2` writer
action. The runtime read-one row of `skip_sentinel` remains unchanged.
This deletes one state and one seed cell. The new underflow row erases the
only right terminal and turns directly left into `finish_scan`.

## 3. Cleanup and exact endpoints

### Auxiliary counter

Underflow takes 2n+1 transitions. Starting at the last counter bit,
`clean_bit`/`clean_sep` erase all counter bits and separators, then both left
sentinel bits. The second right terminal remains as the delimiter before
the separately printed register payload. `exit_scan` reaches the marker
and exits one cell to its right. The gap contains exactly 2^n+2n+3 zeros.

If R is the payload length, R=sum(initial)+18, then W=R+2n+6,
m0=-R-2n-5, and the final head is -R-2n-3-2^n. There is no residual counter
garbage anywhere else on the tape.

### Original zero register clock

After underflow erases the first terminal bit, `erase_right` erases the
second. `finish_scan` starts on the erased first terminal and scans left.
Every surviving counter one is isolated by a zero, so the first adjacent
pair it detects is the left sentinel. It erases the left bit of that pair
and keeps the right bit as register delimiter. There are exactly n zero
register blocks to its right. For n>9 the extra n-9 blocks are the explicitly
declared spare zero registers.

Here W=2n+6 and m0=-2n-5. The final marker is m0-N, the delimiter is m0+3,
and the final head is m0-N+1=-2^n-2n-3. The gap has N+2=2^n+1 zeros.

### Seed-two register clock

The physical register order is `(2,4,3,7,6,8,0,1,5)`. Thus zero-based
physical block 6 is logical register 0, `nextproof`.

After erasing the first terminal bit, this route turns left and preserves
the second terminal bit. Put k=n-7, which is at least two. The borrowed
seed walk visits the k rightmost counter bits and k-1 intervening
separators. It then writes one on the separator of physical block 7,
at m0+18. The one bits of old blocks 6 and 7, together with this new one,
form `0111`, the unary value two in physical block 6. Later blocks shift
down by one; the retained terminal bit becomes the last zero register
block. Exactly n blocks remain, with value two only in physical block 6.

The critical last borrowed read-one row moves left from the old block 6
bit (m0+17) into `finish_scan` at that block's separator (m0+16). Cleanup
therefore starts strictly to the left of the newly formed run `111`. It
cannot mistake that run for the left sentinel. A version that instead
scanned through `111` from the right would be incorrect.

The head, marker, delimiter, and gap equal those of the original zero
variant. The support additionally contains m0+18 and m0+2n+5. No other
positions change. For n=9 the final head is -533 and the one positions are

    -534,-20,-18,-16,-14,-12,-10,-8,-6,-5,-4,-2,0.

### Single-sentinel zero register clock

This has W=2n+5 and m0=-2n-4. Underflow erases its only terminal one and
enters `finish_scan` immediately on the final counter bit. The same
left-sentinel cleanup leaves n zero blocks. The gap is again 2^n+1, but
the entire final frame is translated one cell right relative to the
original zero variant. Its head is -2^n-2n-2. Translation does not alter
the runtime semantics of this two-way infinite-tape machine.

For n=9 the head is -532 and the one positions are

    -533,-19,-17,-15,-13,-11,-9,-7,-5,-3,-1.

## 4. Exact time formulas

At the j-th positive decrement, let t be the number of trailing zero bits
of v=N-j, equivalently t=nu_2(v). The subtract phase takes 2t+2 transitions;
the return to `find_marker` takes 2t+3; the marker move and rightward
sentinel return take 2j+7. The total is therefore 4t+2j+12.

Since sum_{v=1}^N nu_2(v)=N-n, summing all N positive decrements gives

    N^2+15N-4n = 4^n+13*2^n-14-4n.

Including W seed writes and the three transitions to the first header,
the time through the last successful decrement is

    W+4^n+13*2^n-11-4n.

The underflow-and-cleanup tail is 4n+N+5 for the auxiliary and seed-two
versions; it is 4n+N+7 for the original zero register version. For the
single-sentinel zero version it is again 4n+N+5. In the seed-two tail,
the borrowed walk takes 2k+1=2n-13 transitions and the remaining left
cleanup takes 15, explaining why it is two steps shorter than the original
zero cleanup despite producing two more one cells.

The resulting standalone times agree exactly with the code:

| Version | Standalone time |
| --- | ---: |
| Auxiliary | 4^n+14*2^n+2n+17+sum(initial) |
| Original zero register clock | 4^n+14*2^n+2n+1 |
| Seed-two register clock | 4^n+14*2^n+2n-1 |
| Single-sentinel zero | 4^n+14*2^n+2n-2 |

The 12 non-seed control states plus 2n+3 seed states give the original
register-clock count 2n+15. Deleting `seed2` in the single-sentinel version
gives 2n+14. Sharing the return removes one further private state in either
version; it does not remove or alter a runtime state.

## 5. Shared return: one private state saved, exactly 20 steps added

The replacement uses existing runtime rows, which the script checks by
their exact actions:

* `e:2` scans left through zeros; on one it moves left to `e:4`.
* The nine zero rows at `e:4,e:6,e:9,e:13,e:19,e:29,e:41,e:58,e:74`
  move left, ending in `e:84`.
* `e:84` scans right through zeros; on one it moves right into `d:0`.

The original `exit_scan` and `e:2` therefore act identically until they read
the final marker at m. All cells strictly left of m are zero by the full
invariant. The shared path moves left ten times (one marker transition and
nine chain transitions), then right over ten zeros, and finally right from
the same marker into `d:0`. It takes 21 transitions from the marker where
the old exit took one. The difference is exactly 20; tape and final head
are unchanged.

The code verifies that no runtime transition enters the removed private
state and that every runtime row, including its named target, is exactly
preserved. Thus the prior runtime checks transfer at the same gap. This
is a precise reuse argument, not a fresh claim that 8,391 cases constitute
a kernel proof. Absolute frame translation in the single-sentinel case
does not affect those relative tape contracts.

## 6. Exact quotient and independent finite verification

For source table delta, quotient delta', working counts n,m, and map h,
the required equations are

    h(0)=0, h(n)=m, h[{0,...,n-1}]={0,...,m-1},
    delta'(h(q),b)=(w,d,h(r)) whenever delta(q,b)=(w,d,r).

The first line preserves the distinguished start and distinguishes halt
from every working state. The row equation gives identical writes and
head movements on every tape. Induction on time gives identical tapes and
heads and mapped control states at every step. Because no working state
maps to halt, halting occurs at exactly the same step in both machines.
This argument is valid for arbitrary starting tapes and source control
states, with their mapped target state; it is stronger than a blank-run
comparison.

The implementation's partition refinement uses exact writes, directions,
and destination blocks and keeps halt distinguished. Its convergence
produces the stated row equations. Any broader semantic equivalence of
states is outside its scope. The supplied map is the certificate, so the
claim does not depend on trusting the minimizer to be optimal.

The separate `code/reviews/verify_initializer_rows.py` imports none of the
constructor, quotient, or simulator implementations. It parses the eight
selected raw and quotient files directly; checks complete binary tables,
start/working/halt conditions, declared counts and table hashes; verifies
all 4,912 source row equations; and reconstructs the nontrivial classes.
Every selected table merges exactly `b:1` and `e:5`. Independently derived
closed-form marker/head/support/time formulas above agree with all eight
saved endpoint records and their full-support hashes. No runtime or
affine simulation was repeated.

Results are in `data/reviews/initializer_independent_row_results.json`. The checked
counts are:

| Source DAG label | Single-sentinel zero: raw/shared then quotient | Seed-two: raw/shared then quotient |
| --- | ---: | ---: |
| original219 | 317 -> 316 | 318 -> 317 |
| rebracket207 | 305 -> 304 | 306 -> 305 |
| rebracket206 | 304 -> 303 | 305 -> 304 |
| decoder202 | 300 -> 299 | 301 -> 300 |

At n=9 the shared private-state counts are respectively 31 and 32; the
one-state quotient saving is a distinct merge within the existing runtime.
The decoder202 accounting is consequently 269+31-1=299 for zero and
269+32-1=300 for seed two. The input DAG's 202 nodes are not themselves
binary machine states.

## 7. Report review and scope

I also reviewed report sections 01--04 and the logical argument of section 05. The support theorem's full
symmetric-group factorization, least-support argument, parameter handling,
quotient interpretation bound, and Foundation-free Kuratowski injection
are correct. The class quotient formulation avoids choosing proper-class
quotient representatives. The no-bi-interpretability corollary is properly
qualified and does not assert a consistency separation.

The BU/AU derivation correctly distinguishes raw deductive equivalence
from the earlier interpretation-based consistency calibration. The final
report should continue to distinguish these ordinary mathematical proofs,
literal table checks, inherited runtime evidence, and the outstanding
end-to-end logical endpoint. No stronger status follows from this review.


The full transitive-container proof in section 02 has no hidden second
schema parameter. The two branches of G are disjoint; its local bounds
need not be amalgamated. In its nonsingleton transitivity case, the exact
O-singleton of y is a subset of x by outgoing agreement, and both closure
steps use nonempty active inputs. For raw Union, the auxiliary container v
is only a witness used to prove the bound; it does not occur in the schema
matrix whose sole parameter is P.

Section 04's four time formulas, phase counts, physical block-six edit,
shared return, final 299/300 counts, and the distinction between zero and
seed-two inputs match this independent derivation. A wording issue was
reported to the lead author: the constructor specifies the reused rows,
while their symbol guards are justified by the phase invariant; the
constructor does not itself perform a universal reachability proof.

For section 05, instantiating J(c,a,b) gives rho7 and rho5 by projection,
and J(a,b,c) gives rho3. Conversely rho7(b,c,a), rho5(b,c,a), rho3(a,b,c)
are precisely the three common-antecedent factors. The relative-falsity
qualification is necessary and correctly retained. This review did not
independently repeat the fusion program's search or compilation checks.

To rerun the independent literal row and endpoint-record checks from any
working directory, invoke the packaged script. Its default package root
is resolved from its own path. `--root` can select a copied package and
`--output` can save the complete JSON result; otherwise output is stdout
only. It refuses Python's assertion-disabling `-O` mode. The checker has
no dependency on the repository checkout or any network source.
