# Independent review of the current14 source frontier

The recorded 13-drift / 207-node conclusion is reproduced **on the
historical source graph**, with the qualifications below. This review did
not run Lean or authenticate any object provider.

An independent breadth-first traversal of the pinned manifest found
1,000 reachable project modules and 106 directly referenced external
modules. The latter all have `Foundation`, `Mathlib`, `Lean`, or `Init`
roots; this does not authenticate their package sources or dynamic
dependencies. Hashing the current reachable workspace sources found the
same 13 changed modules and no missing files as the recorded result. A
reverse-edge breadth-first traversal produced exactly the recorded
207-module set, including the target. The 13 changed files' leading
ordinary `import` headers match their historical records.

The manifest hash matches both the retained freezer observation and
`preparation.json`; the preparation hash matches the pair state, which
is in turn linked from the outer observation. The two retained builder
states cite the same manifest and preparation and report 16 completed
additions. The temporary retained `strict-plan.json` matches the manifest
hash pointer, has exactly the same 1,000 ancestor modules, and agrees on
all their source hashes and declared imports. Its external import set
is also the same 106 modules. These checks verify the stated hash links;
they inherit the historical replay's package, dynamic-load and
between-observation provenance limits.

The import scan in `audit.py` is a line regex, not a Lean parser. It can
miss nonmatching import forms and misread lines inside block comments.
For example, an unchanged source,
`BusyBeaver.ZFC.ArithmeticControlFile`, contains a prose line beginning
`import closures)` inside a block comment. It is not scanned for import
drift because its source hash matches the manifest. An earlier source
comment described the scan as conservative for unfamiliar syntax; the
current comment correctly states the limitation. The leading headers of
the 13 observed changed files were checked separately here, but this is
not a general parser or a guarantee about future source changes. Missing
or newly imported modules require a fresh source graph.

## Scoped review of the recorded seed-object scan

The later `scan_seed_objects.py` reads the pinned historical author seed
hashes and searches five explicitly listed local provider roots for each
of the 793 ancestors outside the 207-node closure. It compares `.olean`
bytes by SHA-256 and records the **first** matching path. The saved result
partitions those 793 modules into 489 recorded matches and 304 without a
recorded match in those five roots. The 304 are not a claim of global
absence. Matching `.olean` bytes do not authenticate transitive imports,
dynamic loads, package ancestry or a safe rebuild seed.

The independent [`review_seed_scan.py`](review_seed_scan.py) verified
the partition, uniqueness, path/module mapping, listed-provider scope,
and seed-hash availability without repeating the full scan. It also
rehashed one recorded match from each of the two providers represented in
the result; both matched their historical author seed hashes. The other
487 recorded matches and all 304 nonmatches were **not** independently
rehash-verified here. First-match ordering explains why 470 recorded paths
are from the first provider and 19 from the fourth; this does not mean
the other roots contain no matching objects. The scan is observational
and has no provider snapshot or protection against concurrent changes.

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current14-source-frontier-independent/review_seed_scan.py
```

The captured output is [`seed-review-result.json`](seed-review-result.json).
SHA-256 hashes:

```text
8728350bcba64ca8359dce65ad96b017be3ad4141a63e9df38d7c123d4ef5acb  review_seed_scan.py
7be1b718e3b0da590b17a896e2f533fa806a8321c7ebec563fbace9e8ef8f059  seed-review-result.json
```

## Reproduction

At the review run's workspace HEAD `3e7b0777af1b68188405b0798815bfdd257134bd`,
the following read-only command exited 0; its captured output is
[`result.json`](result.json):

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current14-source-frontier-independent/review.py
```

The command reads the retained
`/tmp/ipra-current14-historical-paired-run-01/strict-plan.json`, whose
presence is temporary, and invokes the reviewed source audit read-only.
It compares graph sets using an independently built reverse-edge map.
The rerun's workspace HEAD naturally differs from the original recorded
HEAD; the compared module sets and source hashes agree.

```text
6680e5e1fe9da9088a5deec57d94ff6a2f31249b5a708ee795976c11d5e850de  review.py
629c0e55ce2c1be66f173ed178ff67f0b0e8b7ad500bfed392fbc09c89d38d12  result.json
```

This supports a source-directed rebuild plan, not reuse of any particular
objects, success of a current Lean replay, formal PDF semantics, or the
end-to-end iPRA goal.
