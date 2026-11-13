#!/usr/bin/env python3
"""Check a proposed compact controller-unit residue, using the retained recipe.

This is finite external evidence, not a Lean proof or a file-binding proof.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import sys

if not __debug__:
    raise RuntimeError("Run without Python optimization")

HERE = Path(__file__).resolve()
ROOT = next(p for p in HERE.parents if (p / "Computability").is_dir())
RECIPE = ROOT / "Computability/DiophantineConsistency/candidates/free-j-polarized-positive/source/positive/coefficients/recipe/build_coefficients.py"
spec = spec_from_file_location("compact44_recipe", RECIPE)
if spec is None or spec.loader is None:
    raise RuntimeError("Cannot load compact recipe")
recipe = module_from_spec(spec)
spec.loader.exec_module(recipe)
data = recipe.recipe()

d, p = 590069, 581197
assert d == 67 * 8807 and recipe.D_BITS == d and recipe.PAD_PRIME == p
L = d * p
rho = pow(2, 67, L)
B = pow(2, d, L)
dc = sum(c * pow(rho, e, L) for e, c in data["dc"].items()) % L
dr = pow(rho, 42, L)
k = (dc + B * dr) % L
rho1063 = pow(rho, 1063, L)
gamma = rho1063 * (B * B - 1) * (1 + B * (k + B)) % L
assert (L, B, dc, dr, k, rho1063, gamma) == (
    342946332593, 290226301192, 313772214412, 158651740298,
    284898815895, 298529384010, 306697999258,
)
assert pow(B, p, L) == B
assert B * B % L == 201792753151
assert pow(gamma, p - 1, L) == 1
print("PASS: recipe-derived compact controller residues and proposed exponents")
print("Scope: finite Python calculation; no Lean theorem or retained-byte binding")
