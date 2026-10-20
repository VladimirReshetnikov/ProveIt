"""Register the 225 variant in a fresh copy of Source 123's K226F extension: build.py choices and
the manifest. Already applied to `rocq-extension/` here (rerunning it there fails its first assertion)."""
import hashlib, json, os
from pathlib import Path

EXT = str(Path(__file__).resolve().parent / "rocq-extension")
sha = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()

b = os.path.join(EXT, "build.py")
s = open(b, encoding="utf-8").read()
old = 'parser.add_argument("--states", type=int, choices=(226, 227, 229), default=226)'
assert s.count(old) == 1
s = s.replace(old, 'parser.add_argument("--states", type=int, choices=(225, 226, 227, 229), default=225)')
s = s.replace('"""Cleanly compile and kernel-check the isolated 226/227/229-state extensions.',
              '"""Cleanly compile and kernel-check the isolated 225/226/227/229-state extensions.')
open(b, "w", encoding="utf-8", newline="\n").write(s)

m_path = os.path.join(EXT, "manifest.json")
m = json.load(open(m_path))
order = ["Prog225", "OffsetBisim230", "Cert225Offsets", "Source225", "Table230", "TM230", "Zip", "Boot230",
         "Runtime230Core", "Tape230Blocks", "Tape230Carry", "Interpreter230Sites", "Interpreter230Check",
         "Sim230", "Sim230Main", "Table225", "Dense225", "Correct225", "CorrectDense225"]
m["variants"]["225"] = {
    "namespace": "K225F", "working_states": 225, "compile_order": order, "target": "CorrectDense225",
    "expected_closed_reports": 2, "boot_steps": 409835, "deleted_sparse_labels": [79, 140, 175, 208, 229],
    "inputs": {"dense": "inputs/225/table.tm", "sparse": "inputs/225/table_k230labels.tm",
               "sites": "inputs/225/sites.json", "certificate": "inputs/225/Cert225Offsets.v"}}
m["primary_variant"] = 225
files = m["files"]
new = [f"coq/225/{n}.v" for n in order] + [f"inputs/225/{n}" for n in
       ("table.tm", "table_k230labels.tm", "sites.json", "Cert225Offsets.v")] + ["regenerate225.py"]
for rel in new + ["build.py"]:
    files[rel] = sha(os.path.join(EXT, rel.replace("/", os.sep)))
json.dump(m, open(m_path, "w", encoding="utf-8", newline="\n"), indent=1)
print("registered 225:", len(order), "proof files;", len(files), "manifest files")
