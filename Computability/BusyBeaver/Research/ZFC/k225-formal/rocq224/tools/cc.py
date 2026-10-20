"""Compile K224 Rocq files one at a time against the built K230 reference.
Usage: cc.py FILE.v [FILE.v ...]   (files live in k224rocq/src; objects go to k224rocq/work, namespace K224)"""
import json, os, shutil, subprocess, sys, time
from pathlib import Path

BASE = Path(r"C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-merge-article-groups-491e11\31b37d1b-6b02-4181-babf-8c85ac50cb17\scratchpad")
REF = BASE / "rocq225" / "pkg" / "vendor" / "k230-rocq"
COQC = BASE / "rocq225" / "rocq910" / "bin" / "coqc.exe"
SRC = BASE / "k224rocq" / "src"
WORK = BASE / "k224rocq" / "work"
env = dict(os.environ, ROCQLIB=str(BASE / "rocq225" / "rocq910" / "lib" / "coq"), COQLIB=str(BASE / "rocq225" / "rocq910" / "lib" / "coq"))

rm = json.load(open(REF / "manifest.json"))
flags = []
for name, rel in rm["logical_roots"].items():
    root = rel if rel.startswith(".build/library/") else ".build/project/" + rel
    flags += ["-Q", str(REF / root), name]
flags += ["-Q", str(WORK), "K224"]
WORK.mkdir(exist_ok=True)
rc = 0
for f in sys.argv[1:]:
    src = SRC / f
    dst = WORK / src.name
    shutil.copyfile(src, dst)
    t = time.perf_counter()
    r = subprocess.run([str(COQC), *flags, str(dst)], cwd=WORK, env=env, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(f"== {f} rc={r.returncode} {time.perf_counter() - t:.1f}s")
    print(r.stdout[-6000:])
    if r.returncode:
        rc = 1
        break
sys.exit(rc)
