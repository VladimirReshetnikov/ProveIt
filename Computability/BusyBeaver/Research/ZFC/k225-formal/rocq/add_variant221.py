"""Register the 221 variant in rocq-extension/: build.py (choice 221; an explicit dense-to-sparse
label list for tables whose canonical numbering is not the order-preserving compaction) and the
manifest (compile order, inputs, file digests). Idempotent: rerunning refreshes the digests."""
import hashlib, json, os
from pathlib import Path

EXT = Path(__file__).resolve().parent / "rocq-extension"
sha = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()

b = EXT / "build.py"
s = b.read_text(encoding="utf-8")
old = 'parser.add_argument("--states", type=int, choices=(225, 226, 227, 229), default=225)'
if old in s:
    s = s.replace(old, 'parser.add_argument("--states", type=int, choices=(221, 225, 226, 227, 229), default=221)')
old2 = '''    renumber = {q: i for i, q in enumerate(q for q in range(231) if q not in deleted)}
    require(dense == {(renumber[q], b): (w, d, renumber[n])'''
new2 = '''    if "dense_labels" in spec:
        labels = spec["dense_labels"]
        require(len(labels) == v + 1 and labels[v] == 230 and len(set(labels)) == v + 1
                and not set(labels) & deleted, "Bad explicit dense-to-sparse label list.")
        renumber = {q: i for i, q in enumerate(labels)}
    else:
        renumber = {q: i for i, q in enumerate(q for q in range(231) if q not in deleted)}
    require(dense == {(renumber[q], b): (w, d, renumber[n])'''
if old2 in s:
    s = s.replace(old2, new2)
assert '"dense_labels" in spec' in s and "choices=(221, 225" in s
s = s.replace('"""Cleanly compile and kernel-check the isolated 225/226/227/229-state extensions.',
              '"""Cleanly compile and kernel-check the isolated 221/225/226/227/229-state extensions.')
b.write_text(s, encoding="utf-8", newline="\n")

regen = json.loads((EXT / "coq/regeneration221.json").read_text(encoding="utf-8"))
calc = ["Codes222", "Thm222", "CD222", "Prop222", "G222", "L224Def", "L224Prop", "L224Meta", "L224E",
        "Interp222", "Enum222", "L1_Sound222", "L1_Comp222", "L1_222", "Seed222", "Sound222",
        "Complete222", "Dag222", "ProgLib222", "L2Root222", "Main222"]
order = calc + ["Prog221", "OffsetBisim230", "Cert221Offsets", "Source221", "Table230", "TM230", "Zip",
                "Boot230", "Runtime230Core", "Tape230Blocks", "Tape230Carry", "Interpreter230Sites",
                "Interpreter230Check", "Sim230", "Sim230Main", "Table221", "Dense221", "Correct221",
                "CorrectDense221"]
assert sorted(order) == sorted(p.stem for p in (EXT / "coq/221").glob("*.v")), "compile order vs files"
m_path = EXT / "manifest.json"
m = json.loads(m_path.read_text(encoding="utf-8"))
m["variants"]["221"] = {
    "namespace": "K221F", "working_states": 221, "compile_order": order, "target": "CorrectDense221",
    "expected_closed_reports": 2, "boot_steps": 409835,
    "deleted_sparse_labels": [79, 140, 175, 191, 192, 208, 219, 226, 229],
    "dense_labels": regen["dense_labels"],
    "inputs": {"dense": "inputs/221/table.tm", "sparse": "inputs/221/table_k230labels.tm",
               "sites": "inputs/221/sites.json", "certificate": "inputs/221/Cert221Offsets.v"}}
m["primary_variant"] = 221
files = m["files"]
new = [f"coq/221/{n}.v" for n in order] + [f"inputs/221/{n}" for n in
       ("table.tm", "table_k230labels.tm", "sites.json", "Cert221Offsets.v")] + ["regenerate221.py"]
for rel in new + ["build.py"]:
    files[rel] = sha(EXT / rel)
m_path.write_text(json.dumps(m, indent=1), encoding="utf-8", newline="\n")
print("registered 221:", len(order), "proof files;", len(files), "manifest files")
