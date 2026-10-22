"""Register the 218 variant in rocq-extension/: build.py (choice 218) and the manifest (compile
order, inputs, file digests). Idempotent: rerunning refreshes the digests."""
import hashlib, json
from pathlib import Path

EXT = Path(__file__).resolve().parent / "rocq-extension"
sha = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()

b = EXT / "build.py"
s = b.read_text(encoding="utf-8")
old = 'parser.add_argument("--states", type=int, choices=(221, 225, 226, 227, 229), default=221)'
if old in s:
    s = s.replace(old, 'parser.add_argument("--states", type=int, choices=(218, 221, 225, 226, 227, 229), default=218)')
assert "choices=(218, 221" in s
s = s.replace('"""Cleanly compile and kernel-check the isolated 221/225/226/227/229-state extensions.',
              '"""Cleanly compile and kernel-check the isolated 218/221/225/226/227/229-state extensions.')
b.write_text(s, encoding="utf-8", newline="\n")

regen = json.loads((EXT / "coq/regeneration218.json").read_text(encoding="utf-8"))
calc = ["Codes222", "Thm222", "DominatedCore", "CD222", "Prop222", "G222", "L224Def", "L224Prop", "L224Meta", "L224E",
        "Interp222", "Enum222", "L1_Sound222", "L1_Comp222", "L1_222", "Seed222", "Sound222",
        "Complete222", "Dag219", "ProgLib219", "L2Root219", "Main219"]
order = calc + ["Prog218", "OffsetBisim230", "Cert218Offsets", "Source218", "Table230", "TM230", "Zip",
                "Boot230", "Runtime230Core", "Tape230Blocks", "Tape230Carry", "Interpreter230Sites",
                "Interpreter230Check", "Sim230", "Sim230Main", "Table218", "Dense218", "Correct218",
                "CorrectDense218"]
assert sorted(order) == sorted(p.stem for p in (EXT / "coq/218").glob("*.v")), "compile order vs files"
m_path = EXT / "manifest.json"
m = json.loads(m_path.read_text(encoding="utf-8"))
m["variants"]["218"] = {
    "namespace": "K218F", "working_states": 218, "compile_order": order, "target": "CorrectDense218",
    "expected_closed_reports": 2, "boot_steps": regen["boot_steps"],
    "deleted_sparse_labels": regen["deleted_sparse_labels"],
    "dense_labels": regen["dense_labels"],
    "inputs": {"dense": "inputs/218/table.tm", "sparse": "inputs/218/table_k230labels.tm",
               "sites": "inputs/218/sites.json", "certificate": "inputs/218/Cert218Offsets.v"}}
m["primary_variant"] = 218
files = m["files"]
new = [f"coq/218/{n}.v" for n in order] + [f"inputs/218/{n}" for n in
       ("table.tm", "table_k230labels.tm", "sites.json", "Cert218Offsets.v")] + ["regenerate218.py"]
for rel in new + ["build.py"]:
    files[rel] = sha(EXT / rel)
m_path.write_text(json.dumps(m, indent=1), encoding="utf-8", newline="\n")
print("registered 218:", len(order), "proof files;", len(files), "manifest files")
