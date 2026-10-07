"""Generate a deterministic text patch against the exact pinned fast/ snapshot."""
from __future__ import annotations

import difflib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "Topology/UnknotRecognition/fast/"


def sources(root):
    return {p.relative_to(root).as_posix(): p for p in root.rglob("*")
            if p.is_file() and "__pycache__" not in p.parts
            and p.suffix not in (".pyc", ".pyo")}


def main():
    old = sources(ROOT / "reference" / "fast")
    new = sources(ROOT / "fast")
    output = []
    changed = []
    for name in sorted(old.keys() | new.keys()):
        before = old[name].read_text() if name in old else ""
        after = new[name].read_text() if name in new else ""
        if before == after:
            continue
        changed.append(name)
        path = PREFIX + name
        output.append(f"diff --git a/{path} b/{path}\n")
        if name not in old:
            output.append("new file mode 100644\n")
        elif name not in new:
            output.append("deleted file mode 100644\n")
        diff = difflib.unified_diff(
            before.splitlines(keepends=True), after.splitlines(keepends=True),
            fromfile="a/" + path if name in old else "/dev/null",
            tofile="b/" + path if name in new else "/dev/null",
        )
        for line in diff:
            if line.endswith("\n"):
                output.append(line)
            else:
                output.extend((line + "\n", "\\ No newline at end of file\n"))
    (ROOT / "integration.patch").write_text("".join(output))
    print(f"Wrote integration.patch: {len(changed)} changed or added files")
    for name in changed:
        print(name)


if __name__ == "__main__":
    main()
