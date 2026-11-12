# Independent review: Carrier65 external source frontier

The [source-frontier audit](../../research/current14-carrier65-external-frontier-source-audit/README.md) reproduces in this retained environment and accurately states the bounded observation. The independently reconstructed seed set has 138 recorded names from the 529-stage plan and all 1,000 base producers; these include 55 names directly seen in the completed prefix and are not asserted to be the next stage's complete dependency set.

The independent checker separately reconstructs the 39 recorded base seeds, their 172 reachable base records, the 106 distinct external names recorded across the whole base, and the union with the plan's 99 names. It rehashes each of the 138 observed selected object candidates and recorded package paths, checks the saved source hashes and the presence or absence of the 14 inspected package suffixes, and compares 407 Foundation seed artifact observations to the pinned receipt. The 407 includes the 37 `.olean` files; it is not 407 additional companions.

A separately implemented nested-comment-aware header reader re-parses all 777 observed files, checks their source hashes and initial import records, and independently reconstructs the 639 first-generation names, 3,157 explicit edges, 764-name unexpanded boundary, 464 `meta import` edges and 13 `import all` edges to 12 distinct targets. It checks that each observed `import all` target has a currently present `.olean.private` candidate, and rehashes the recorded candidate artifacts. The parser accepts only the simple initial header forms actually encountered and is not a general Lean parser.

Both inspections use the same retained plan, state and Foundation receipt, so agreement does not independently authenticate their historical producers. Non-atomic reads and cached hashes cannot rule out intervening mutation. Current source headers and matching artifact hashes do not prove which source produced a compiled object, Lean's actual resolution or import modes, transitive implicit/compiled imports, companion selection, package/toolchain compatibility, or dynamic runtime inputs. The 764 names are unexpanded, not necessarily missing. No Lean process was run, and this review is not a safe-reuse or proof-closure certificate.

The original audit also reproduced using its documented command. To reproduce the independent check from the repository root while the retained paths remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current14-carrier65-external-frontier-source-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/current14-carrier65-external-frontier-source-independent/result.json
```
