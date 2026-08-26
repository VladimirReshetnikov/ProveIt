# Multi-agent coordination protocol (v2, lightweight)

Whether this protocol is in effect is stated by exactly one file:
[`STATUS.md`](STATUS.md).  While STATUS says `state: OFF`, nothing in this
file binds anyone.  When the user flips it to `state: ON`, the campaign rules
below apply to `Analysis/FabiusFunction`.  Durable engineering policy
(documentation and LaTeX rules, Lean build guidance, invariants) lives in
[`../../AGENTS.md`](../../AGENTS.md) and applies at all times regardless of
this switch.

Design goals, in priority order: **(1)** throughput of correct mathematics;
**(2)** evidence where it pays for itself; **(3)** deleting a rule must be as
easy as adding one.  The v1 framework (2026-08 campaign) held quality but
spent several lines of bookkeeping per line of content, ran grant queues with
multi-step ceremonies, and stranded fully audited work behind leases.  v2
keeps v1's two proven inventions — rebuild-don't-resolve for binary
artifacts, and exact-source-unit integration — at a fraction of the ceremony.
v1 is archived in [`../COLLABORATION.md`](../COLLABORATION.md),
[`../MULTI_AGENT_COORDINATION_PROPOSAL.md`](../MULTI_AGENT_COORDINATION_PROPOSAL.md),
and the git history of `docs/registry/`.

## Self-limits

- This file stays under **300 lines** and **15 numbered rules**.  At either
  cap, adding requires deleting first.
- Every numbered rule carries a one-line cost note — what failure it
  prevents, what it charges.  A rule whose cost note cannot be written
  honestly is deleted.
- All numbered rules are **campaign rules**: they expire automatically when
  STATUS flips OFF.  Re-enabling treats this file as a proposal — the user
  and coordinator strike anything that did not pay for itself last campaign
  before flipping ON.  Nothing is grandfathered.

## Bookkeeping lives on the board branch, never on `main`

The board branch is an **orphan branch** `coordination/<campaign>` sharing no
history with `main`, holding only:

- `board.md` — the entire live state (rule 3);
- `status/<branch-with-slashes-as-dashes>.md` — one small file per worker
  (rule 4).

Create it at enable time from any worktree:

```sh
git worktree add --detach ../fabius-board
cd ../fabius-board
git switch --orphan coordination/<campaign>
# write board.md, mkdir status/, commit, then:
git push -u origin coordination/<campaign>
```

Read it without a checkout:

```sh
git fetch origin coordination/<campaign> && git show FETCH_HEAD:board.md
```

Write through a small worktree like the one above; on a rejected push,
`git pull --rebase` and retry — writers own disjoint files, so conflicts are
rare and trivial.  `main` receives only content, protocol revisions, and the
two STATUS flips per campaign.

## Campaign rules

1. **`main` advances continuously through one integrator.**  The coordinator
   — or a worker the user has authorized directly — integrates finished
   units into `main` as they appear; nobody else pushes `main`; never
   force-push.
   *Prevents:* divergent mains, clobbered history.  *Costs:* an integrator
   round-trip per unit, bounded by rule 8.

2. **Lean work is claim-free and optimistic.**  No advertisement, no lease,
   no permission.  Before starting something large, skim `board.md`'s
   in-flight list and add one line for your effort — awareness, not a grant.
   When two branches land overlapping results, the **first landed wins**; the
   other rebases or drops.
   *Prevents:* v1's claim/grant queues and waiting.  *Costs:* an occasional
   discarded duplicate — which v1 paid anyway, plus the queue.

3. **The board is current-state only, at most 150 lines.**  `board.md` holds
   the owner table, the in-flight list, pending integration requests, and
   notes on suspended rules — overwritten in place, never appended.  History
   is the board branch's git log.  At the cap the coordinator prunes before
   adding.
   *Prevents:* the 3,700-line board.  *Costs:* occasionally consulting
   git log for the past.

4. **Worker status is one overwritten file, at most 25 lines.**  Fields:
   branch, base SHA, doing, done-awaiting-integration (commit SHAs),
   blocked-on, and a `Verified:` / `Not yet compiled:` line.  Update at
   milestones and handoffs, not on a timer.
   *Prevents:* thousand-line append-only registries.  *Costs:* thinner
   narrative — commit messages and git history carry it.

5. **Each canonical document has one standing owner for the whole
   campaign.**  The owner (named in STATUS.md) is the only editor of that
   document and its PDF; everyone else hands content to the owner as a
   branch, a patch, or a board note.  Ownership moves only by a STATUS.md
   edit — never per tranche.
   *Prevents:* document convoys and per-tranche lease ping-pong.  *Costs:*
   the owner can bottleneck — bounded by rule 8 and transferable at will.

6. **Small fixes take the fast path.**  A document change of ≤20 source
   lines introducing no new formula or label, or a pure comment/docstring
   Lean change, goes straight to the owner/integrator and lands after one
   review — no board round-trip, no status update.
   *Prevents:* three-sentence repairs costing multi-step grant cycles (v1's
   worst case).  *Costs:* a rare fast-path collision — first landed wins.

7. **The build mutex is a lock file, not a social token.**  One `lean`/`lake`
   process per machine, enforced mechanically: create `.fabius-build.lock` at
   the repository root (first line: PID; then branch and module) before
   building, delete it after.  A lock whose PID is dead is stale — delete it
   and proceed.  The board is not involved.

   ```sh
   if [ -f .fabius-build.lock ] && kill -0 "$(head -1 .fabius-build.lock)" 2>/dev/null
   then echo busy
   else printf '%s\n%s\n%s\n' "$$" "$(git branch --show-current)" "$MODULE" > .fabius-build.lock
   fi
   ```

   *Prevents:* the double-`lean` OOM this machine is prone to, without v1's
   token queue.  *Costs:* effectively none.

8. **Integration latency is capped at 2 hours.**  A unit marked
   done-awaiting-integration must be integrated, rejected with a stated
   reason, or explicitly deferred by the user within 2 hours of the
   integrator's next active session.  Status files carry the wait-start
   time.  A breach is an overhead event under rule 10.
   *Prevents:* audited work dying in queues — v1 stranded a fully reviewed
   tranche indefinitely.  *Costs:* the integrator interrupts other work at
   most every 2 hours.

9. **Evidence is a commit SHA plus a stated verification result.**  Say what
   was compiled or not compiled; reserve full-content hashes, blob ids, and
   byte counts for pinning binary artifacts and for disputes.
   *Prevents:* v1's hash ceremony from creeping back.  *Costs:* a thinner
   forensic trail for sources — git history compensates.

10. **Overhead is measured, and a miss forces a deletion.**  At campaign end
    — or whenever the user or any two workers ask — the coordinator posts on
    the board:

    - *bookkeeping ratio*: lines ever committed to the board branch versus
      content lines landed on `main`
      (`git log --numstat --format= <ref> | awk '{a+=$1} END{print a}'`,
      excluding `*.pdf`); target **below 1:4**;
    - *latency*: count of units that waited more than 2 hours (target
      **zero**);
    - *round-trips*: units needing more than two board interactions to land
      (target **rare**).

    If any target is missed, the coordinator must delete or relax at least
    one campaign rule before any new rule may be added.
    *Prevents:* silent creep back to v1 overhead.  *Costs:* about fifteen
    minutes per assessment.

11. **Anyone may propose deleting a rule; the coordinator may delete one
    unilaterally.**  A deletion or suspension takes effect when noted on the
    board with a one-line reason — notification, not consensus.  The user
    may add, delete, or override anything at any time.  A rule suspended for
    a week without being missed is struck from this file at the next STATUS
    flip.
    *Prevents:* monotone accretion — deletion is cheaper than addition by
    design.  *Costs:* a premature deletion, restorable by one revert.

12. **Merge conflicts in generated binaries are never resolved.**  Merge and
    settle the `.tex`, then the document owner rebuilds the `.pdf` from the
    merged source (three-pass procedure and log gates as in `AGENTS.md`);
    never select either side's binary.
    *Prevents:* corrupted or source-mismatched canonical PDFs.  *Costs:*
    minutes of rebuild per conflict.

## Enabling (on the user's request)

1. Pick a campaign id and coordinator; assign document owners (one agent may
   hold several documents).
2. Edit [`STATUS.md`](STATUS.md): `state: ON`, campaign, coordinator,
   board-branch, document-owners, date.
3. Create and push the orphan board branch with a seeded `board.md` (see
   above).
4. Workers read this file once and work under rules 1–12.

## Disabling (on the user's request)

1. Integrate or explicitly abandon everything in flight (rule 8 applies to
   the closeout).
2. Run the rule-10 assessment; strike rules that did not pay for themselves.
3. Edit [`STATUS.md`](STATUS.md): `state: OFF`, date, one-line retrospective
   in the history table.
4. Delete the board branch (`git push origin :coordination/<campaign>`),
   optionally tagging its tip first.
