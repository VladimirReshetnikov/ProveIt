# Generator replay detail

In the temporary replay copy described in `ERRATUM.md`, remove the copied `SharingSeed32Sextic.lean` output before invoking `generate.py`: the generator intentionally asserts that its destination is absent. Compare the regenerated file and generator output with the frozen originals. Do not remove the frozen output.
