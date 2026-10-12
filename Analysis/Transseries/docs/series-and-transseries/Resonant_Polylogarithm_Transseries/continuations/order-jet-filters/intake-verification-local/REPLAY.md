# Independent local replay

12 October 2026. Exit code 0, six default groups, 165 exact assertions and
46 numerical assertions at 70 working digits. Python 3.13.5, mpmath 1.3.0,
SymPy 1.14.0; actual group records retain versions and working precision.

The delivered package was copied to an independent temporary directory
outside the repository. From its root the unmodified command was:

```
uv run --no-project --with-requirements requirements.txt python code/verify.py --output-dir replay
```

The entire new replay directory and captured stdout/stderr are retained
here. The parallel intake's separate run in ../intake-verification is
preserved, as is the unchanged delivered data directory. These are finite
exact algebra and non-interval floating-point diagnostics. They do not
establish the general analytic theorems or Lean formalization.
