#!/usr/bin/env python3
"""Read-only hashes for the guarded bridge and its reported direct inputs."""
import hashlib
import json
import pathlib
import subprocess

HERE = pathlib.Path(__file__).resolve().parent
ROOT = pathlib.Path(subprocess.check_output(["git", "-C", str(HERE), "rev-parse", "--show-toplevel"], text=True).strip())
SOURCE = ROOT / "Computability/DiophantineConsistency/research/ordinary12-absorb88-guarded-normalization-draft"
PROBE = ROOT / "Computability/DiophantineConsistency/research/ordinary12-absorb88-probe/observations/conditional-attempt01/result.json"
paths = [pathlib.Path("/tmp"), pathlib.Path("/tmp/absorb89-chain-gpc9zymd/lib")]
paths += [pathlib.Path(p) for p in json.loads(PROBE.read_text())["lean_path"].split(":")]
expected = {
    "Absorb88GuardedNormalization": "e567a603c9050a2f723df136e72b7a710ccf4f8e06769da85ce42745b8a5700f",
    "Absorb88NormalizationRing": "e9864486b2ed0ed7478b6367405458df92c80f5cb36da9976202ef75058a2bc7",
    "Absorb88MainRoot": "f5c725deeddd1fcad2faf31a607e34307547ac9f7c4d4de9c2f61552617eab40",
    "Absorb88Conditional": "eb29868c7558f0c5de32b47f5ef926a62890d0dda0be034881dbf1a13100ddb2",
    "Absorb88First": "1332d8aa708a4f9163451dac1a6e844f3da2623b62d27e4ea952de242d2359fd",
}
sources = {
    "Absorb88GuardedNormalization.lean": "28872ab12399f555f13c6fced5cb14273594643eb4396a9b12dd8882a7773db6",
    "Absorb88NormalizationRing.lean": "a10346f288052cc0081dfd7da3bac872026a334c7471ac0776019c41795b2ce7",
}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
objects = {}
for name, wanted in expected.items():
    path = next((p / (name+".olean") for p in paths if (p / (name+".olean")).is_file()), None)
    assert path is not None and sha(path) == wanted
    objects[name] = {"path": str(path), "sha256": wanted}
for name, wanted in sources.items():
    assert sha(SOURCE / name) == wanted
print(json.dumps({"status": "REPORTED_DIGESTS_MATCH_ONLY", "sources": sources, "objects": objects,
    "scope": "Read-only source review and direct object hashes; no Lean replay or transitive provider authentication."}, indent=2, sort_keys=True))
