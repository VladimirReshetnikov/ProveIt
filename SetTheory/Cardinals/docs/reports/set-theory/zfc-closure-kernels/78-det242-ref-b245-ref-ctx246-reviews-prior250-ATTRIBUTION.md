# Attribution and frozen dependency provenance

This is a minimal, unchanged runtime subset of
`docs/incoming/zfc-prefix250-audit-20261017.zip`, extracted as
`zfc-prefix250-report`, from the user-supplied ProveIt repository snapshot
`e0b512a63e2c1ca6a1698fa437b8568f1643ff6b`:

<https://github.com/VladimirReshetnikov/ProveIt/tree/e0b512a63e2c1ca6a1698fa437b8568f1643ff6b/docs/incoming>

The inherited builder itself pins its baseline to ProveIt commit
`80e26b89e905bf3e5dfc322befdc1c6eaf25a109`. Its embedded hashes authenticate
the two source inputs and the reconstructed 250-state machine. The four
Python modules and two source inputs below are copied byte for byte. The
two original license notices are retained without extending their scope.

## Credits and license boundary

Mira-Cult designed the original machine and compact calculus. Jeff
Ketchersid (`jeff87654`) supplied the upstream verification and symbolic
rules. Andrew James Wade supplied the public compiler framework. The
public 253-state reduction is credited to mira-emmy; the physical register
permutation and source27 strict affine checker are credited to ProveIt.
The prefix-carry construction and its induction checker come from the
previously supplied prefix250 research and independent-audit packages.
These credits retain the attribution in their `sources/prior/provenance.json`
and `sources/research/upstream-attribution.md`; those larger provenance
bundles are not runtime dependencies of this subset.

The upstream benchmark was imported by ProveIt from
`jeff87654/busy-beaver` commit
`297ab8df7e5de329605c3875b4934643b371a5e3`. That upstream tree declares no
repository-wide license. The inherited ProveIt attribution explicitly
excludes unchanged upstream work from ProveIt's blanket MIT-0 grant.
This subset does not relicense that work. `LICENSE.ProveIt` applies to
ProveIt-authored material within its original scope;
`LICENSE.Wade` retains the separately scoped public-backend notice.
No public-backend modules or vendored proof libraries are bundled here.

The new `../audit246.py` specializes these inherited checkers to the
246-state transition table. Its independent work consists of applying
the two context-dependent folds, checking the new table and complete
bootstrap, and rerunning the existing symbolic proof templates and full
guarded instruction traversal. The dependency checker is inherited;
this is not an independent implementation of its symbolic proof rules.

## Byte hashes

The entries below refer to paths relative to this directory.

| File | SHA-256 |
| --- | --- |
| `code/rebuild_machines.py` | `4acfcd3f36cb5dcace50a3c56c8fcf2103931e257c95f894ba0fa3e80b81b2aa` |
| `code/affine_engine.py` | `8c029463048fb544608dec93b6bba772ab21250377b8fbb2763cbab4f1ee35e7` |
| `code/check_macro_inductions.py` | `3484c0be3aaf34bd3677c0cc727eaba8655efd358f9338192a88be0d9c89ad8d` |
| `code/check_instructions.py` | `fe532e4f7c2e6e104a42cd09793f7e4b1637fc3ebd0c7919b21b634fccde14b2` |
| `sources/baseline252_old.tm` | `939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713` |
| `sources/Prog254.v` | `1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746` |
| `licenses/LICENSE.ProveIt` | `460d4fb6f45fd89278ba881d4b70e8bd1b7df223ee907e758342c2f9989f789d` |
| `licenses/LICENSE.Wade` | `c1dffee77db98625debe39b47538e1d2f3b7956cbc7bcd6ed9363701b2177cfa` |
