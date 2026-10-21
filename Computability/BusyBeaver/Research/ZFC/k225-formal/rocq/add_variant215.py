"""Register the 217 variant in rocq-extension/: build.py (choice 217) and the manifest (compile
order, inputs, file digests). Idempotent: rerunning refreshes the digests."""
import hashlib, json
from pathlib import Path

EXT = Path(__file__).resolve().parent / "rocq-extension"
sha = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()

b = EXT / "build.py"
s = b.read_text(encoding="utf-8")
old = 'parser.add_argument("--states", type=int, choices=(217, 218, 221, 225, 226, 227, 229), default=217)'
if old in s:
    s = s.replace(old, 'parser.add_argument("--states", type=int, choices=(215, 217, 218, 221, 225, 226, 227, 229), default=215)')
assert "choices=(215, 217, 218" in s
s = s.replace('"""Cleanly compile and kernel-check the isolated 217/218/221/225/226/227/229-state extensions.',
              '"""Cleanly compile and kernel-check the isolated 215/217/218/221/225/226/227/229-state extensions.')
b.write_text(s, encoding="utf-8", newline="\n")

regen = json.loads((EXT / "coq/regeneration215.json").read_text(encoding="utf-8"))
calc = ["Codes222", "Thm222", "CD222", "Prop222", "G222", "L224Def", "L224Prop", "L224Meta", "L224E",
        "Interp222", "Sound222", "Complete222", "DomRho8", "ThmDom", "EnumPerm", "L1_SoundPerm",
        "L1_CompPerm", "SeedPerm", "Regs215", "DagPerm", "ProgLibPerm", "L2RootPerm", "MainPerm"]
order = calc + ["Prog215", "PathCodec", "BisimMirror", "NormalizedBisim", "NormalizedCert215", "Source215", "Table230", "TM230", "Zip",
                "Boot230", "Runtime230Core", "Tape230Blocks", "Tape230Carry", "Interpreter230Sites",
                "Interpreter230Check", "Sim230", "Sim230Main", "Table215", "Dense215", "Correct215",
                "CorrectDense215"]
assert sorted(order) == sorted(p.stem for p in (EXT / "coq/215").glob("*.v")), "compile order vs files"
m_path = EXT / "manifest.json"
m = json.loads(m_path.read_text(encoding="utf-8"))
m["variants"]["215"] = {
    "namespace": "K215F", "working_states": 215, "compile_order": order, "target": "CorrectDense215",
    "expected_closed_reports": 2, "boot_steps": regen["boot_steps"],
    "deleted_sparse_labels": regen["deleted_sparse_labels"],
    "dense_labels": regen["dense_labels"],
    "inputs": {"dense": "inputs/215/table.tm", "sparse": "inputs/215/table_k230labels.tm",
               "sites": "inputs/215/sites.json", "certificate": "inputs/215/NormalizedCert215.v"}}
m["primary_variant"] = 215
files = m["files"]
new = [f"coq/215/{n}.v" for n in order] + [f"inputs/215/{n}" for n in
       ("table.tm", "table_k230labels.tm", "sites.json", "NormalizedCert215.v")] + ["regenerate215.py"]
for rel in [k for k in files if k.startswith(("coq/215/", "inputs/215/")) and k not in new]:
    del files[rel]
for rel in new + ["build.py"]:
    files[rel] = sha(EXT / rel)
m_path.write_text(json.dumps(m, indent=1), encoding="utf-8", newline="\n")
print("registered 215:", len(order), "proof files;", len(files), "manifest files")
