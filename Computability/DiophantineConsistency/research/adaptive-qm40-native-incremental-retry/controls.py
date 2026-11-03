#!/usr/bin/env python3
"""Exercise retry guards on isolated temporary files, without launching Lean."""
import importlib.util
import json
from pathlib import Path
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("qm40_retry", HERE / "replay.py")
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load retry")
retry = importlib.util.module_from_spec(spec)
spec.loader.exec_module(retry)


def rejected(f):
    try:
        f()
    except RuntimeError:
        return True
    return False


with tempfile.TemporaryDirectory(prefix="qm40-guard-control-") as tmp:
    root = Path(tmp)
    target1, target2 = root / "target1", root / "target2"
    target1.write_bytes(b"same")
    target2.write_bytes(b"same")
    obj = root / "sample.olean"
    obj.symlink_to(target1)
    guard = retry.slots(root / "sample")
    retry.check(guard)
    companion = root / "sample.ilean"
    companion.write_bytes(b"new")
    companion_detected = rejected(lambda: retry.check(guard))
    companion.unlink()
    obj.unlink()
    obj.symlink_to(target2)
    link_detected = rejected(lambda: retry.check(guard))
    obj.unlink()
    obj.symlink_to(target1)
    target1.write_bytes(b"changed")
    contents_detected = rejected(lambda: retry.check(guard))
    if not (companion_detected and link_detected and contents_detected):
        raise RuntimeError("a guard mutation was not detected")
    print(json.dumps({"status": "PASS_NO_LEAN_GUARD_CONTROLS",
                      "new_companion_detected": companion_detected,
                      "same_bytes_different_link_detected": link_detected,
                      "target_content_change_detected": contents_detected}, sort_keys=True))
