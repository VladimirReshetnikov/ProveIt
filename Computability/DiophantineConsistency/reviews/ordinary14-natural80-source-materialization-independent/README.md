# Independent review: natural-80 source materialization blueprint

The [materialization blueprint](../../research/ordinary14-natural80-source-materialization-plan/README.md)
accurately maps the pinned 189-stage lexical plan to hypothetical source and
output names within the documented scope. Both its receipt and the independent
check below reproduce. No directory or Lean source root is created or reserved.

The independent checker rehashes all 189 current selected source files against
the pinned ordered plan, verifies the 5 qualified and 184 inert-draft stage
kinds, and reconstructs each source and object destination by joining module
name components. It compares the resulting rows and input byte lengths with
the blueprint. It also independently enumerates the plan's 13 historical
output suffixes, finding 2,457 distinct hypothetical output names and no
collision with the 189 hypothetical source names. The current selected source
files total 597,347 bytes, excluding all outputs, provider artifacts,
temporary files and filesystem overhead. This is not a build-space estimate.

These checks use the same pinned plan as the blueprint and inspect only the
selected source files and hypothetical names. They do not check path safety in
an actual future directory tree, ensure no parent component is a symlink,
select or reserve a root, copy or protect inputs, check alternate providers or
companions, resolve actual Lean imports, reserve resources or establish
elaboration, axiom closure, iPRA derivability or physical-file binding. The
blueprint's explicit unreserved placeholder and these limitations are correct.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-source-materialization-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-source-materialization-independent/result.json
```
