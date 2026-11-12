"""Reproduce the certificate checks, source sizes, and source identity check."""
import ast
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def executable_tree(path):
    tree = ast.parse(path.read_text())
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        tree.body.pop(0)
    return ast.dump(tree, include_attributes=False)


def main():
    printed = ROOT / "code/checker.py"
    documented = ROOT / "implementation/code/all_starts_checker.py"
    if executable_tree(printed) != executable_tree(documented):
        raise SystemExit("The printed and documented checker bodies differ")
    subprocess.run([sys.executable, str(ROOT / "implementation/verify.py")],
                   cwd=ROOT, check=True)
    print("Printed and documented checker executable ASTs are identical.")


if __name__ == "__main__":
    main()
