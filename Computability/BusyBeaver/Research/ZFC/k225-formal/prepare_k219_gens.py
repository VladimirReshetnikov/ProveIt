"""Derive the 219's source and site generators from the 221's.

  python prepare_k219_gens.py

Writes generate_source219_lean.py (p219 = Source 140's 4,744-leaf source against dag219 read as
a path program, 467 nodes) and generate_sites219_lean.py (every leaf of p219 passes
`KSim.checkEdge tm219`) by checked substitutions in generate_source221_lean.py and
generate_sites221_lean.py.
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent


def derive(src, dst, subs):
    t = (HERE / src).read_text(encoding="utf-8")
    for a, b in subs:
        assert a in t, (src, a)
        t = t.replace(a, b)
    (HERE / dst).write_text(t, encoding="utf-8", newline="\n")
    print("wrote", dst)


derive("generate_source221_lean.py", "generate_source219_lean.py", [
    ('"Computability/BusyBeaver/Research/ZFC/candidate-k221/sites_logical.json"',
     '"Computability/BusyBeaver/Research/ZFC/candidate-k219/sites219.json"'),
    ("candidate-k221/sites_logical.json", "candidate-k219/sites219.json"),
    ("L2K.dag222_seed_iff", "L2Q.dag219_seed_iff"),
    ("Seed222", "Seed219"),
    ("dag222", "dag219"),
    ("Dag222", "Dag219"),
    ("461", "467"),
    ("closed reassociations and the AX node's chain layout", "closed reassociations, the AX node's chain layout and the equality test's layout"),
    ("the Rocq\n`Cert221Offsets.v`", "the 221's\nRocq `Cert221Offsets.v` played this role for the 221"),
    ("221", "219"),
])

derive("generate_sites221_lean.py", "generate_sites219_lean.py", [
    ('HERE.parent / "candidate-k221" / "sites_logical.json"', 'HERE.parent / "candidate-k219" / "sites219.json"'),
    ("221", "219"),
])
