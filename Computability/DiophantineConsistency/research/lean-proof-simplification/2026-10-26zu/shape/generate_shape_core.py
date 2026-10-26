#!/usr/bin/env python3
"""Generate a standard-library checker from hash-pinned source declarations.

Usage: python3 generate_shape_core.py --repo /path/to/ProveIt
All source declaration bodies are preserved. Only Mathlib notation Type*, ℕ,
and ℤ is normalized to Type _, Nat, and Int. The original splitSize is placed
inside namespace Legacy to coexist with the proposed definition.
"""
from pathlib import Path
import argparse
import hashlib
import json


EXPECTED = {
    "repo:Representation.lean": "1b1a20d42422b0fffe2fb25ad4423c4914a0fcd1a0ccafcd1abdfcf863da92b7",
    "repo:NaturalExpression.lean": "a202ec90e91f2ed35e0aa00394ea94a47d29b32a64704dd7f3ec2c7155c30250",
    "repo:QuarticCompiler.lean": "803f6a07d83b82b7cfe821d2208bddd66a0225658754da335e1144b9eb9210fa",
    "repo:RepresentationSize.lean": "650eb39d03f0e04724d8dcf42e6a4fe655032bbba10ffd88f004ee9cceda6375",
    "repo:ExpressionSize.lean": "6a85f999f600f774092d93e0dc997ea1c2495d6a3a36ed989ea38ea4800b1144",
    "shape:ExpressionSize.original.lean": "6a85f999f600f774092d93e0dc997ea1c2495d6a3a36ed989ea38ea4800b1144",
    "shape:ExpressionSize.lean": "311f4d2db74f131435ae1d4463767162598f9861c535de337b69c76de8bd3546",
    "shape:SplitShape.lean": "4f24346505eca32940529d859f8dc1f0d706abe99e00ca4f1abbf1a2cad7f1fb",
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def normalize(text):
    return text.replace("ℕ", "Nat").replace("ℤ", "Int").replace("Type*", "Type _")


def between(text, start, end):
    a = text.index(start)
    b = text.index(end, a)
    return text[a:b].rstrip() + "\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--shape-dir", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    source_dir = args.repo / "Computability/DiophantineConsistency/Lean/DiophantineConsistency"
    texts = {}
    manifest = {"baseline_commit": "9d9d1123b39927d30363f1dcd53c23f0575c30ee", "files": [], "snippets": []}
    for key, expected in EXPECTED.items():
        kind, name = key.split(":", 1)
        path = (source_dir if kind == "repo" else args.shape_dir) / name
        data = path.read_bytes()
        actual = sha(data)
        if actual != expected:
            raise SystemExit(f"Source hash mismatch: {key}: expected {expected}, got {actual}")
        texts[key] = data.decode("utf-8")
        manifest["files"].append({"key": key, "sha256": actual})

    chunks = ["import Lean.Elab.Tactic.Omega\n\n/-! Generated from exact pinned declarations; see ShapeCore.manifest.json. -/\n"]

    def add(label, body):
        chunks.append(f"\n/- Extracted: {label}. -/\n" + normalize(body))
        manifest["snippets"].append({"label": label, "original_sha256": sha(body.encode()), "normalized_sha256": sha(normalize(body).encode())})

    chunks.append("\nnamespace DiophantineConsistency\n")
    add("Representation.Expr", between(texts["repo:Representation.lean"], "inductive Expr", "namespace Expr"))
    natural = texts["repo:NaturalExpression.lean"]
    add("NaturalExpression.NatExpr", between(natural, "inductive NatExpr", "namespace NatExpr"))
    chunks.append("\nnamespace NatExpr\nvariable {σ : Type _}\n")
    add("NaturalExpression.NatExpr instances", between(natural, "instance (n : ℕ)", "/-- The natural expression evaluator"))
    chunks.append("\nend NatExpr\nnamespace Expr\nvariable {σ : Type _}\n")
    add("NaturalExpression.Expr.splitNatural", between(natural, "def splitNatural", "/-- The difference of the supplied"))
    chunks.append("\nend Expr\nnamespace QuarticCompiler.Gates\nvariable {σ : Type _}\n")
    add("QuarticCompiler.Gates.count", between(texts["repo:QuarticCompiler.lean"], "def count :", "/-- The finite indexing"))
    chunks.append("\nend QuarticCompiler.Gates\nnamespace NatExpr\n")
    size = texts["repo:RepresentationSize.lean"]
    nat_size = size[size.index("namespace NatExpr"):]
    add("RepresentationSize.NatExpr.depth", between(nat_size, "def depth", "/-- A depth bound"))
    chunks.append("\nend NatExpr\nnamespace ExpressionSize\n")
    old = texts["shape:ExpressionSize.original.lean"]
    add("ExpressionSize.SplitSize and operations", between(old, "structure SplitSize", "/-- Structural size interpretation"))
    chunks.append("\nnamespace Legacy\n")
    add("original ExpressionSize.splitSize (namespace-isolated)", between(old, "def splitSize", "theorem splitSize_correct"))
    chunks.append("\nend Legacy\n")
    candidate = texts["shape:ExpressionSize.lean"]
    add("candidate ExpressionSize.halfSize and splitSize", between(candidate, "def halfSize", "theorem splitSize_correct"))
    add("candidate ExpressionSize.splitSize_correct", between(candidate, "theorem splitSize_correct", "@[simp] theorem splitSize_rename"))
    chunks.append("\nend ExpressionSize\nend DiophantineConsistency\n")
    shape = texts["shape:SplitShape.lean"]
    add("candidate SplitShape declarations and proofs", shape[shape.index("namespace DiophantineConsistency"):])

    chunks.append(r'''
namespace DiophantineConsistency

namespace NatExpr

theorem shapeFold_count {σ : Type _} (e : NatExpr σ) :
    shapeFold (1 : Nat) (fun a b => 1 + (a + b))
      (fun a b => 1 + (a + b)) e = QuarticCompiler.Gates.count e := by
  induction e <;> simp_all [shapeFold, QuarticCompiler.Gates.count]

theorem shapeFold_depth {σ : Type _} (e : NatExpr σ) :
    shapeFold (0 : Nat) (fun a b => 1 + max a b)
      (fun a b => 1 + max a b) e = depth e := by
  induction e <;> simp_all [shapeFold, depth]

end NatExpr

namespace Expr

theorem splitNatural_count_eq {σ : Type _} (e : Expr σ) :
    QuarticCompiler.Gates.count e.splitNatural.1 =
      QuarticCompiler.Gates.count e.splitNatural.2 := by
  simpa only [NatExpr.shapeFold_count] using
    splitNatural_shapeFold_eq (1 : Nat) (fun a b => 1 + (a + b))
      (fun a b => 1 + (a + b)) e

theorem splitNatural_depth_eq {σ : Type _} (e : Expr σ) :
    NatExpr.depth e.splitNatural.1 = NatExpr.depth e.splitNatural.2 := by
  simpa only [NatExpr.shapeFold_depth] using
    splitNatural_shapeFold_eq (0 : Nat) (fun a b => 1 + max a b)
      (fun a b => 1 + max a b) e

end Expr

namespace ExpressionSize

theorem legacy_splitSize_diagonal {σ : Type _} (e : Expr σ) :
    Legacy.splitSize e = ⟨halfSize e, halfSize e⟩ := by
  induction e with
  | constant a => rfl
  | var i => rfl
  | add p q hp hq =>
    simp only [Legacy.splitSize, hp, hq, SplitSize.add, halfSize]
  | sub p q hp hq =>
    simp only [Legacy.splitSize, hp, hq, SplitSize.sub, halfSize]
  | mul p q hp hq =>
    simp only [Legacy.splitSize, hp, hq, SplitSize.mul, halfSize]
    congr 1 <;> omega

theorem splitSize_eq_legacy {σ : Type _} (e : Expr σ) :
    splitSize e = Legacy.splitSize e :=
  (legacy_splitSize_diagonal e).symm

theorem splitSize_positive_eq_negative {σ : Type _} (e : Expr σ) :
    (splitSize e).positive = (splitSize e).negative := rfl

end ExpressionSize

example : QuarticCompiler.Gates.count
    (Expr.mul (Expr.var ()) (Expr.var ())).splitNatural.1 = 7 := rfl
example : QuarticCompiler.Gates.count
    (Expr.mul (Expr.var ()) (Expr.var ())).splitNatural.2 = 7 := rfl

-- A raw-shape theorem cannot alone identify separately simplified trees.
-- These are only the indicated normal-form shapes; the actual simplify
-- implementation has not been extracted or asserted to produce them here.
example : QuarticCompiler.Gates.count
      (NatExpr.mul (NatExpr.var ()) (NatExpr.var ())) !=
    QuarticCompiler.Gates.count (NatExpr.constant (σ := Unit) 0) := by decide

#print axioms Expr.splitNatural_count_eq
#print axioms Expr.splitNatural_depth_eq
#print axioms ExpressionSize.splitSize_correct
#print axioms ExpressionSize.legacy_splitSize_diagonal
#print axioms ExpressionSize.splitSize_eq_legacy
#print axioms ExpressionSize.splitSize_positive_eq_negative

end DiophantineConsistency
''')
    output = args.output or (args.shape_dir / "ShapeCore.lean")
    data = "\n".join(chunks)
    output.write_text(data)
    manifest["output_sha256"] = sha(data.encode())
    manifest["scope"] = "Exact extracted declaration checker, not a full repository integration build."
    output.with_suffix(".manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Generated {output}; SHA-256 {manifest['output_sha256']}")


if __name__ == "__main__":
    main()
