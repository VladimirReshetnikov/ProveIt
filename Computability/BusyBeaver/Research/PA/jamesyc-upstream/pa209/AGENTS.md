# Maintaining PA209

Read the [paper](paper/pa209.tex), [theorem statements](docs/result.md), and
[reproduction instructions](docs/reproduction.md) before changing the package.

- Preserve the machine bytes, theorem statements, and explicit assumptions.
- Keep the literal PA209 endpoint in the default build and the endpoint
  declarations in the axiom audit.
- Run `bash scripts/check.sh` for packaging changes. For changes to proofs,
  imports, or dependencies, build the affected targets and run the axiom audit.
- Keep source identities and license notices accurate. Preserve original validation data verbatim.
- Retain the required support libraries under their original names. Publish
  only the PA209 paper, proof, machine data, and their reproduction materials.
- Keep build caches, private files, and experiments outside the publication tree.
- Push, release, or change repository visibility only on the user's instruction.
