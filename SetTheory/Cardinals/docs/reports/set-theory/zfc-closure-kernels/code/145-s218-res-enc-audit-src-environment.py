"""Pinned dependencies extracted by the packet's verification/replay.py."""
from pathlib import Path
import hashlib
import os
import sys

PACKET = Path(__file__).resolve().parents[4]
value = os.environ.get("PROVEIT_K221_PORTABLE")
if not value:
    raise SystemExit("Set PROVEIT_K221_PORTABLE to the extracted K221 portable directory; see ../README.md")
P = Path(value).resolve()
expected = "4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f"
if hashlib.sha256((P / "source_language.py").read_bytes()).hexdigest() != expected:
    raise SystemExit("Pinned source_language.py hash mismatch")
sys.path.insert(0, str(P))
import source_language as s
BASE_SOURCE = P.parent.parent / "K219_Construction_2026-10-20/machine/sites219.json"
BASE_TABLE = BASE_SOURCE.with_name("k219.native.tm")
if not BASE_SOURCE.is_file():
    raise SystemExit("Expected the sibling K219 directory extracted by verification/replay.py")
if not __debug__:
    raise SystemExit("Run Python without -O or PYTHONOPTIMIZE")
