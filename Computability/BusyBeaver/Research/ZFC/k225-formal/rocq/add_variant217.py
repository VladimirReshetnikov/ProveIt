"""Register the 217 variant in rocq-extension/: build.py (choice 217) and the manifest (compile
order, inputs, file digests). Idempotent: rerunning refreshes the digests."""
import hashlib, json
from pathlib import Path

EXT = Path(__file__).resolve().parent / "rocq-extension"
sha = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()

b = EXT / "build.py"
s = b.read_text(encoding="utf-8")
old = 'parser.add_argument("--states", type=int, choices=(218, 221, 225, 226, 227, 229), default=218)'
if old in s:
    s = s.replace(old, 'parser.add_argument("--states", type=int, choices=(217, 218, 221, 225, 226, 227, 229), default=217)')
assert "217, 218, 221" in s
s = s.replace('"""Cleanly compile and kernel-check the isolated 218/221/225/226/227/229-state extensions.',
              '"""Cleanly compile and kernel-check the isolated 217/218/221/225/226/227/229-state extensions.')
b.write_text(s, encoding="utf-8", newline="\n")

regen = json.loads((EXT / "coq/regeneration217.json").read_text(encoding="utf-8"))
calc = ["Codes222", "Thm222", "CD222", "Prop222", "G222", "L224Def", "L224Prop", "L224Meta", "L224E",
        "Interp222", "Sound222", "Complete222", "DomRho8", "ThmDom", "EnumDom", "L1_SoundDom",
        "L1_CompDom", "SeedDom", "DagDom", "ProgLibDom", "L2RootDom", "MainDom"]
order = calc + ["Prog217", "OffsetBisim230", "Cert217Offsets", "Source217", "Table230", "TM230", "Zip",
                "Boot230", "Runtime230Core", "Tape230Blocks", "Tape230Carry", "Interpreter230Sites",
                "Interpreter230Check", "Sim230", "Sim230Main", "Table217", "Dense217", "Correct217",
                "CorrectDense217"]
assert sorted(order) == sorted(p.stem for p in (EXT / "coq/217").glob("*.v")), "compile order vs files"
m_path = EXT / "manifest.json"
m = json.loads(m_path.read_text(encoding="utf-8"))
m["variants"]["217"] = {
    "namespace": "K217F", "working_states": 217, "compile_order": order, "target": "CorrectDense217",
    "expected_closed_reports": 2, "boot_steps": regen["boot_steps"],
    "deleted_sparse_labels": regen["deleted_sparse_labels"],
    "dense_labels": regen["dense_labels"],
    "inputs": {"dense": "inputs/217/table.tm", "sparse": "inputs/217/table_k230labels.tm",
               "sites": "inputs/217/sites.json", "certificate": "inputs/217/Cert217Offsets.v"}}
m["primary_variant"] = 217
files = m["files"]
new = [f"coq/217/{n}.v" for n in order] + [f"inputs/217/{n}" for n in
       ("table.tm", "table_k230labels.tm", "sites.json", "Cert217Offsets.v")] + ["regenerate217.py"]
for rel in new + ["build.py"]:
    files[rel] = sha(EXT / rel)
m_path.write_text(json.dumps(m, indent=1), encoding="utf-8", newline="\n")
print("registered 217:", len(order), "proof files;", len(files), "manifest files")
