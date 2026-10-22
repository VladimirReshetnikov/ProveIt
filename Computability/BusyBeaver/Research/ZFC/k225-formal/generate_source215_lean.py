"""Generate BusyBeaver/ZFC/KSource215.lean: the 215's source program and dagPerm halt alike.

`p215` is the 215's rotated 4,751-leaf source (candidate-k215/sites215.json), hash-consed
as in Source 123's `source_data.program_text`. The other side is `dagPerm` itself, read as a path
program (`RMEquiv.ofDag dagPerm 487`); its well-formedness tables (heights, break and continue
bounds) are computed here and re-checked by the kernel, as in `generate_rmequiv254.py`. The
literal certificate comes from `gen_cert.py` (2,240 zero-offset entries). The
Source168 trailing-zero quotient reduces it to 1,426 entries; the decoder-parametric
normalized checker uses an explicit 512-step pointer decoder. Everything emitted
is untrusted; the kernel re-checks it in chunks. dagPerm is written by make_dagPerm.py.

Usage (from the repository root):
    python Computability/BusyBeaver/Research/ZFC/k225-formal/generate_source215_lean.py DAGPERM_NODES_JSON DAGPERM_SITES_JSON"""
import json, sys
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
sys.path.insert(0, str(HERE))
sys.setrecursionlimit(100000)
from gen_cert import load, Tree, generate  # noqa: E402
from generate_source225_lean import dag, program, literal_tree, code, chunks  # noqa: E402
from partition_source215_lean import write_partition  # noqa: E402

TARGET = REPO / "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215.lean"
SITES215 = REPO / "Computability/BusyBeaver/Research/ZFC/candidate-k215/sites215.json"


def wf_tables(nodes_json):
    d = json.load(open(nodes_json))
    nn = d["nnodes"]
    nodes = {int(k): v for k, v in d["nodes"].items()}
    kind = {"N": "node", "EInc": "inc", "EDecnz": "decnz", "EBreak": "brk", "EContinue": "cont", "EHalt": "halt"}
    nodes = {n: tuple((kind[a[0]], a[1] if a[1] is not None else 0) for a in v) for n, v in nodes.items()}

    @lru_cache(maxsize=None)
    def h(n):
        return 1 + max((h(e[1]) if e[0] == "node" else 0) for e in nodes[n])

    def b_edge(e):
        return {"node": lambda: b(e[1]), "decnz": lambda: 1, "brk": lambda: e[1]}.get(e[0], lambda: 0)()

    def c_edge(e):
        return {"node": lambda: c(e[1]), "cont": lambda: e[1]}.get(e[0], lambda: 0)()

    @lru_cache(maxsize=None)
    def b(n):
        car, cdr = nodes[n]
        return max(b_edge(car) - 1, b_edge(cdr), 0)

    @lru_cache(maxsize=None)
    def c(n):
        car, cdr = nodes[n]
        return max(c_edge(car), c_edge(cdr) - 1, 0)

    H = [h(n) for n in range(nn)]
    B = [b(n) for n in range(nn)]
    C = [c(n) for n in range(nn)]
    assert H[0] <= nn + 1 and B[0] == 0 and C[0] == 0, (H[0], B[0], C[0])
    return nn, H, B, C


def lit(xs):
    rows = [", ".join(map(str, xs[i:i + 30])) for i in range(0, len(xs), 30)]
    return "[" + ",\n  ".join(rows) + "]"


def trailing_false_quotient(entries):
    """Quotient both endpoint paths, preserving the root and both successors.

    The normalization and saturated checker originate in Source168 / batch205A.
    This producer checks the quotient of the maintained literal certificate;
    Lean independently checks the emitted normalized certificate. Path trimming
    is never applied before a consumed-path increment or break operation.
    """
    def trim(path):
        end = len(path)
        while end and not path[end - 1]:
            end -= 1
        return tuple(path[:end])

    index, representatives, old_to_new = {}, [], []
    for a, b, z, _j, _k in entries:
        assert z == 0, "the normalized certificate requires zero offsets"
        key = (trim(a), trim(b))
        if key not in index:
            index[key] = len(representatives)
            representatives.append(key)
        old_to_new.append(index[key])
    assert entries and old_to_new[0] == 0
    quotient = [None] * len(representatives)
    for i, (_a, _b, _z, j, k) in enumerate(entries):
        assert 0 <= j < len(entries) and 0 <= k < len(entries)
        q = old_to_new[i]
        a, b = representatives[q]
        row = (a, b, 0, old_to_new[j], old_to_new[k])
        assert quotient[q] is None or quotient[q] == row, "inconsistent quotient successors"
        quotient[q] = row
    assert all(row is not None for row in quotient)
    return quotient


def ordinary_tree(entries, lo, hi):
    if hi - lo == 1:
        a, b, z, j, k = entries[lo]
        assert z == 0, "K215's ordinary certificate requires zero offsets"
        return f".leaf ({code(a)}, {code(b)}, {j}, {k})"
    mid = (lo + hi) // 2
    return (f".branch {mid - lo} ({ordinary_tree(entries, lo, mid)})\n  "
            f"({ordinary_tree(entries, mid, hi)})")


def cert_block(prefix, entries, t1, t2):
    parts = chunks(entries, 4)
    out = [f"def {prefix}{i} : CTree :=\n  {ordinary_tree(entries, lo, hi)}\n"
           for i, (lo, hi) in enumerate(parts)]

    def assemble(lo, hi):
        if hi - lo == 1:
            return f"{prefix}{lo}"
        mid = (lo + hi) // 2
        size = parts[mid][0] - parts[lo][0]
        return f".branch {size} ({assemble(lo, mid)}) ({assemble(mid, hi)})"

    out.append(f"def {prefix}Cert : CTree := {assemble(0, len(parts))}\n")
    out.append(f"abbrev {prefix}F : Entry → Bool := RMNormalizedBisim.WithDecoder.entryOk decode215 {t1} {t2} {prefix}Cert\n")
    out.append(f"theorem {prefix}_start : RMNormalizedBisim.WithDecoder.branchOk decode215 {t1} {t2} {prefix}Cert [] [] 0 = true := by decide +kernel\n")
    for i in range(len(parts)):
        out.append(f"theorem {prefix}_ok{i} : allC {prefix}F {prefix}{i} = true := by decide +kernel\n")
    oks = ", ".join(f"{prefix}_ok{i}" for i in range(len(parts)))
    out.append(f"theorem {prefix}_all : allC {prefix}F {prefix}Cert = true := by\n"
               f"  unfold {prefix}Cert\n  simp only [allC, {oks}, Bool.and_self]\n")
    return "\n".join(out)


def main():
    nodes_json, dag_sites = sys.argv[1], sys.argv[2]
    nn, H, B, C = wf_tables(nodes_json)
    L1, L2 = load(SITES215), load(dag_sites)
    n1, r1 = dag(L1)
    n2, r2 = dag(L2)
    literal_entries = generate(Tree(L1), Tree(L2))
    entries = trailing_false_quotient(literal_entries)
    assert len(literal_entries) == 2240 and len(entries) == 1426
    nz = sum(1 for e in entries if e[2] != 0)
    out = f"""import BusyBeaver.ZFC.RMNormalizedBisim
import BusyBeaver.ZFC.RMEquiv
import BusyBeaver.ZFC.DagPerm

/-!
The source program of the 215-state machine and `dagPerm` halt alike, from every register file.

`p215` is the 215's rotated {len(L1):,}-leaf source (`candidate-k215/sites215.json`) as a
hash-consed DAG ({len(n1)} nodes). `pathDagPerm` is `dagPerm` read as a path program; its
well-formedness tables (root height {H[0]}) are re-checked by the kernel. The rotated source and
`dagPerm` differ by closed reassociations, the AX node's chain layout and the equality test's
layout. The {len(literal_entries)} literal checkpoint pairs from `gen_cert.py` are quotiented by
trailing-zero equivalence on both paths, leaving {len(entries)} normalized pairs. The quotient
preserves the root and both successor classes; the kernel checks all resulting obligations
in sixteen chunks. The normalized relation supplies an all-register bisimulation and its
converse. The normalization is adapted from Source168 / batch205A. Pointer decoding uses
512 fuel, preserving the original paths (some exceed the legacy 128-fuel decoder).

`p215_halts_iff` and `path_iff_iter` relate the source to `dagPerm` iterated; the program layer
(`L2Perm.dagPerm_seed_iff`) is composed with them in `KEndpoint215`, so this module depends on the program
data only.

Generated by `Computability/BusyBeaver/Research/ZFC/k225-formal/generate_source215_lean.py`.
-/

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-! ## dagPerm as a path program -/

def tH : List Nat := {lit(H)}

def tB : List Nat := {lit(B)}

def tC : List Nat := {lit(C)}

theorem wfCheck222 :
    RMEquiv.wfCheck DagPerm.dagPerm {nn} (fun n => tH.getD n 0) (fun n => tB.getD n 0)
      (fun n => tC.getD n 0) = true := by
  decide +kernel

theorem wf222 : RMEquiv.WF DagPerm.dagPerm {nn} := RMEquiv.wfCheck_sound wfCheck222

def pathDagPerm : Program := RMEquiv.ofDag DagPerm.dagPerm {nn}

theorem path_iff_iter (R : RMDag.Regs) :
    Halts pathDagPerm ⟨[], R⟩ ↔ RMDag.IterHalts DagPerm.dagPerm R :=
  RMEquiv.halts_iff_iterHalts wf222 R

/-! ## The 215's source -/

"""
    out += program("p215", n1, r1, f"The 215's source as a {len(n1)}-node DAG (root {r1}).") + "\n"
    out += "/-- The 215's decoder tree, computed from the program. -/\ndef t215 : Tree := ptree p215\n\n"
    out += "/-- dagPerm's decoder tree, computed from the program. -/\ndef tD : Tree := ptree pathDagPerm\n\n"
    out += "theorem t215_eq : ptree p215 = t215 := by rfl\n\ntheorem tD_eq : ptree pathDagPerm = tD := by rfl\n\n"
    out += "/-! ## Forward certificate (215 → dagPerm) -/\n\n"
    out += "def decode215 (n : Nat) : List Bool := decodeAux 512 n []\n\n"
    out += cert_block("fwd", entries, "t215", "tD")
    out += """
theorem fwd_start' : RMNormalizedBisim.WithDecoder.branchOk decode215 (ptree p215) (ptree pathDagPerm) fwdCert [] [] 0 = true := by
  rw [t215_eq, tD_eq]; exact fwd_start

theorem fwd_all' : allC (RMNormalizedBisim.WithDecoder.entryOk decode215 (ptree p215) (ptree pathDagPerm) fwdCert) fwdCert = true := by
  rw [t215_eq, tD_eq]; exact fwd_all


/-- **The 215's source and dagPerm halt alike**, from every register file. -/
theorem p215_halts_iff (R : Registers) : Halts p215 ⟨[], R⟩ ↔ Halts pathDagPerm ⟨[], R⟩ :=
  RMNormalizedBisim.WithDecoder.check_halts_iff decode215 fwd_start' fwd_all' R

#print axioms p215_halts_iff

end SetTheory.BusyBeaver.ZFC.KSource215
"""
    write_partition(TARGET, out)
    print(f"wrote {TARGET}: {len(literal_entries)} literal / {len(entries)} normalized entries ({nz} offset), {len(n1)} / {len(n2)} DAG nodes, "
          f"root height {H[0]}, {len(out) // 1024} KB")


if __name__ == "__main__":
    main()
