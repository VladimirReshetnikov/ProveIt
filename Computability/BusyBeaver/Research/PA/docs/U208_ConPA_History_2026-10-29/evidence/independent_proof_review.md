# Independent proof of the U208 reduction

Let A be the exact Plain U209 native table, with SHA-256
`891455876f2684b2bd2a9118092715590028fbdb227aa7055030536714d8b7a4`.
Let C be the proposed U208 native table, with SHA-256
`36b58fea7a184b1050914170e8f5240c8a13da218dbbfa7e1985cd73d516e5c7`.
Both have initial native state 0 and halt 254. Put rho(211)=172 and fix every
other state, including 0 and 254.

The construction deletes both rows of 211, redirects targets through rho,
and changes only the keeper's read-zero row to

    172 0 0 L 214.

The original relevant rows are

| State | Read 0 | Read 1 |
|---:|---|---|
| 172 | 0 L 67 | 1 R 184 |
| 211 | 0 R 157 | 1 R 184 |
| 163 | 0 L 211 | 1 R 211 |
| 214 | 0 R 163 | 1 R 216 |
| 216 | 0 R 157 | 1 R 116 |
| 116 | 0 R 172 | 1 R 194 |
| 157 | 0 L 67 | 1 L 148 |

## Guard lemma, for A only

Consider any run of A beginning in state 0 on any binary tape. The initial head
coordinate is arbitrary. At an occurrence of state 172, the two bits immediately
to the left of the head are 10. At an occurrence of state 211 reading zero, the
bit immediately to the left is one.

For the first assertion, the complete incoming inventories are

    In(172) = {116/0 -> 0 R 172},
    In(116) = {216/1 -> 1 R 116}.

Neither target state is initial. If the current head is at h, the two preceding
steps wrote zero at h-1 and one at h-2. The second step did not change h-2.
This proves the first assertion without any hypothesis on the initial tape.

For the second assertion, the only incoming rows to 211 are 163/1 and 163/0.
If the last step used 163/1, it wrote one at h-1 and moved right, proving the
claim immediately.

Suppose the last step used 163/0. It was at h+1, wrote zero there, and moved left
to h. The complete incoming rows to 163 are

    132/1 -> 1 R 163,
    199/1 -> 1 R 163,
    214/0 -> 0 R 163.

The first two possibilities would have written one at h, contradicting the
assumption that 211 currently reads zero. Hence the predecessor was 214/0.
The only incoming row to 214 is 204/1 -> 1 R 214, so one more step back shows
that h-1 contains one. These three states are not initial, so the needed prior
steps always exist. Again no canonical source/tape-frame assumption is used.

The independent script verifies the complete incoming inventories indirectly by
enumerating every possible suffix history of the indicated length, including
early histories ending at initial state 0. It checks all assignments to cells
read or written by each suffix. Since the suffixes never read any other cell,
this is an exhaustive finite proof over arbitrary unread tape exteriors.

## Four macro identities

Write the head position at the beginning of a macro as zero.

For old 211 reading zero, the guard gives tape[-1]=1. Its old one-step result
is state 157 at head 1, with unchanged tape. The new path is

    172@0 -> 214@-1 -> 216@0 -> 157@1.

It has three steps and preserves every read bit. Only cells -1 and 0 are read.

For old 172 reading zero, the guard gives tape[-2..0]=100. Its old one-step
result is state 67 at head -1, with unchanged tape. The new path is

    172@0 -> 214@-1 -> 163@0 -> 172@-1
          -> 214@-2 -> 216@-1 -> 157@0 -> 67@-1.

It has seven steps, preserves every read bit, and reads only cells -2,-1,0.
The second visit to 172 is part of this fixed finite macro; it is not a new
unproved recursive call.

For either old state on read one, the common row is 1 R 184, unchanged in C.
No tag assumption is needed. This gives the remaining two one-step cases.

None of the paths visits halt internally. All tape cells, not only the local
window, agree at macro endpoints because the exterior is untouched.

For the remaining 414 old rows, the candidate preserves the write and direction
and replaces the successor by its rho image. This was independently checked
for every literal row.

## Simulation and equivalence on every common initial tape

Relate an A configuration to a C configuration by equality of the full tape and
head coordinate and by applying rho to the control state. Initial state 0 is
fixed, so the initial configurations are related on every common tape.

Induct over any finite A run. At an ordinary row use its one-step identity.
At old 172 or 211 use the applicable macro, justified by the guard lemma on the
A run. Each macro ends in a related configuration, takes positive time, and has
no internal halt. Hence every finite A run has the corresponding C trace.

If A halts, its finite trace gives a halting C trace. Conversely, if C halts
after t steps, A must halt within t of its own steps: otherwise simulate t+1
nonhalting A steps, obtaining a nonhalting C trace of at least t+1 steps, in
contradiction with determinism and the supposed halt at t. This argument uses
only finite induction; no appeal to existence of an actual infinite run is
required in the internal PA proof.

Thus, for every common binary initial tape and head coordinate in state 0,

    Halt(C) iff Halt(A).

For arithmetic formalization it suffices to code the relevant finite tape
segments or finite-support initial tapes; in particular the blank instance is
PA-formalizable. The external mathematical all-tape statement also permits
arbitrary bi-infinite binary tapes, including noncomputable ones, because all
proof steps are finite and local. One should not claim that PA quantifies over
all such tapes as second-order objects.

If N_172,0 and N_211,0 count the corresponding old visits in an aligned finite
prefix, the exact time equation is

    T_C = T_A + 6 N_172,0 + 2 N_211,0.

In particular `T_A <= T_C <= 7 T_A`. This time statement applies directly to
the supplied Plain U209 parent, since no source-address change precedes the
fold. It does not claim a speedup.

The proof requires no source/calculus/theory correctness premise. To obtain the
consistency endpoint, compose this local theorem with the retained conventional
U209 calibration. The result remains an ordinary PA-formalizable mathematical
argument with executable certificates, not a newly checked Lean/Rocq/MM0 endpoint.

## Independent finite facts

The checker verifies exact quotient construction, unchanged source bytes, exact
native/dense bijection, totality, 208 working states, 416 binary rows, and graph
reachability of every working state. The dense candidate hash is
`926d15c43daebdafd099723f265b073c25bf21a15e4c5593e669ccac6f70f8d0`.
The source hash remains
`cddbed7f20e7a8b085b7ca0e76811d07b021522375643b5d1134eec0d2d23164`.
