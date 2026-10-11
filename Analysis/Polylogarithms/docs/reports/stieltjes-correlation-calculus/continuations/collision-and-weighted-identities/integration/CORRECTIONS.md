# Proposed canonical corrections

`canonical_corrections.patch` contains two narrow corrections to one canonical file. Both issues were already flagged in the earlier **ProveIt Twisted Stieltjes Harmonic Laurent** continuation, `sections/06_audit.tex`, §§6.1–6.2, and its `integration/INTEGRATION.md`. They are confirmed against the present pinned source here; they are not presented as newly discovered errors.

## Pinned source

- Commit: `445f754610e1377939235794de84ed9075fc09f5`.
- File: `Analysis/Polylogarithms/docs/manuscript/chapters/03-algebraic.tex`.
- [Permanent source URL](https://github.com/VladimirReshetnikov/ProveIt/blob/445f754610e1377939235794de84ed9075fc09f5/Analysis/Polylogarithms/docs/manuscript/chapters/03-algebraic.tex).
- Original file SHA-256: `374f4b7afdb7e84e81d6aca978ff8bf2217aed01aafbe6d21654109ec8930dcc`.

## Exact corrections

### 1. Real logarithm in `cleo:eq:lintanh`

The formula for real `|lambda|<1`, with `theta=arcsin(lambda)`, changes only its logarithm:

```tex
\theta\,\ln\tan\tfrac\theta2
```

becomes

```tex
\theta\,\ln\left|\tan\tfrac\theta2\right|
```

The surrounding sentence now states the real parameter range, and the product at `theta=0` is assigned its continuous value zero. The label `cleo:eq:lintanh`, the Clausen terms, and the existing macros are retained.

For negative real `lambda`, `tan(theta/2)<0`; a principal complex logarithm introduces the spurious term `i*pi*theta`. At `lambda=-1/2`, that term is exactly `-i*pi^2/6`, whereas the integral is real. The corrected formula follows by differentiating both sides with respect to `theta`: each derivative is `theta/sin(theta)`, and both sides tend to zero at the origin.

### 2. Unsupported description of the `(1,1)` diagonal

The exact phrase

```tex
The simplest non-elementary diagonal is the $(1,1)$ case
```

becomes

```tex
The $(1,1)$ diagonal has the Legendre--chi representation
```

The integral and its value `\pi\,\chitwo(3-2\sqrt2)` are preserved verbatim. The original wording supplied neither a specified comparison algebra nor a nonreduction theorem, so the replacement states the proved representation without an unsupported classification.

## Application check

The patch passed `git apply --check` against a temporary copy of the pinned source. Applying it to that copy succeeded, and the resulting file was byte-identical to the intended corrected text. Its SHA-256 is:

```text
c1627553ab0331e567a52dbca080a7f4de79e161ea62f11045e40cc8d6a83fef
```

Only `03-algebraic.tex` changes. The pinned baseline was rehashed after the check and remains unchanged. The patch is proposed and unapplied to the repository. From the repository root, the review command is:

```bash
git apply --check path/to/canonical_corrections.patch
```

No new theorem sections are inserted into the canonical chapter by this patch.
