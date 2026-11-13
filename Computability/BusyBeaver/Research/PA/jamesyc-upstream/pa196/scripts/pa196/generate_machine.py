#!/usr/bin/env python3
"""Generate PA196's exact table and bounded startup proof obligations.

The Python computation is untrusted: every claimed finite trace is an equality
that Lean must prove by kernel reduction. Input table bytes are never changed.
"""
from pathlib import Path
import argparse
import hashlib

ROOT = Path(__file__).resolve().parents[2]
SHA256 = 'e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8'
TOTAL = 58154
CHUNK = 128
PER_FILE = 12

def boolean(x):
    return 'true' if x else 'false'

def bits(xs):
    return '[' + ', '.join(map(boolean, xs)) + ']'

def conf(c):
    q, l, r = c
    return f'⟨{q},{bits(l)},{bits(r)}⟩'

def rows_text(rows, lo, hi, indent):
    pad = ' ' * indent
    if hi - lo == 1:
        w0, d0, n0 = rows[lo, 0]
        w1, d1, n1 = rows[lo, 1]
        return pad + f'if read then ({boolean(w1)}, {boolean(d1)}, {n1}) else ({boolean(w0)}, {boolean(d0)}, {n0})\n'
    mid = (lo + hi) // 2
    return (pad + f'if q < {mid} then\n' + rows_text(rows, lo, mid, indent + 2)
            + pad + 'else\n' + rows_text(rows, mid, hi, indent + 2))

def step(rows, c):
    q, l, r = c
    read = r[0] if r else False
    w, right, nxt = rows[q, int(read)]
    tail = r[1:] if r else []
    if right:
        l, r = [bool(w)] + l, tail
    else:
        head = l[0] if l else False
        l, r = l[1:] if l else [], [head, bool(w)] + tail
    while l and not l[-1]: l.pop()
    while r and not r[-1]: r.pop()
    return nxt, l, r

def generate():
    raw = (ROOT / 'data/pa196.tm').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SHA256
    rows = {}
    for line in raw.decode().splitlines():
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q,b,w,n))
        assert b in (0,1) and w in (0,1) and d in ('L','R')
        assert (q,b) not in rows
        rows[q,b] = (w, d == 'R', n)
    assert set(rows) == {(q,b) for q in range(196) for b in range(2)}
    assert all(0 <= n <= 196 for w,d,n in rows.values())
    assert [(q,b,w,d,n) for (q,b),(w,d,n) in rows.items() if n == 196] == [(63,1,1,True,196)]
    out = {}
    literal = '''module
public import M6.Zip

/-!
Exact PA196 machine generated from `data/pa196.tm`.
SHA-256: e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8

The transition lookup is a balanced decision tree with at most eight state
comparisons, preceded by one domain test in `machine`.
No generated assertion is trusted: the finite claims below use kernel reduction.
-/
@[expose] public section
namespace PA196.Literal
open M6.Zip

/-- Transition data on the working domain `q < 196`. -/
def transition (q : Nat) (read : Bool) : Bool × Bool × Nat :=
'''
    literal += rows_text(rows, 0, 196, 2)
    literal += '''
/-- A binary Turing machine; all labels at least 196 have no transition. -/
def machine : TMN := fun q read =>
  if q < 196 then some (transition q read) else none

def workingLabels : List Nat := List.range 196
def start : Nat := 0
def root : Nat := 75
def halt : Nat := 196

theorem working_count : workingLabels.length = 196 := by decide +kernel
theorem row_count : workingLabels.length * 2 = 392 := by decide +kernel
theorem working_nodup : workingLabels.Nodup := by decide +kernel
theorem start_working : start ∈ workingLabels := by decide +kernel
theorem halt_not_working : halt ∉ workingLabels := by decide +kernel

theorem terminal_row (b : Bool) : machine 196 b = none := by
  simp only [machine, Nat.lt_irrefl, ↓reduceIte]

theorem domain (q : Nat) (b : Bool) : machine q b ≠ none ↔ q < 196 := by
  simp only [machine]
  split <;> simp_all

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem all_rows_closed : (List.range 196).all (fun q =>
    [false,true].all (fun b => decide ((transition q b).2.2 ≤ 196))) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem unique_halting_row_check : (List.range 196).all (fun q =>
    [false,true].all (fun b =>
      decide ((transition q b).2.2 = 196 ↔ q = 63 ∧ b = true))) = true := by
  decide +kernel

theorem unique_halting_row {q : Nat} {b w d : Bool}
    (h : machine q b = some (w,d,196)) : q = 63 ∧ b = true := by
  have hq : q < 196 := (domain q b).mp (by rw [h]; simp)
  have hx := List.all_eq_true.mp unique_halting_row_check q (List.mem_range.mpr hq)
  have hb : b ∈ [false,true] := by cases b <;> simp
  have hh := of_decide_eq_true (List.all_eq_true.mp hx b hb)
  simp only [machine, hq, ↓reduceIte, Option.some.injEq] at h
  exact hh.mp (by rw [h])

theorem halt_transition : machine 63 true = some (true,true,196) := rfl

end PA196.Literal
'''
    out['PA196/Literal.lean'] = literal
    cur = (0, [], [])
    checkpoints = [cur]
    lengths = []
    for t in range(TOTAL):
        cur = step(rows, cur)
        if (t + 1) % CHUNK == 0 or t + 1 == TOTAL:
            lengths.append((t + 1) - sum(lengths))
            checkpoints.append(cur)
    physical = [0,0,0,0,0,0,2,0,0] + [1]*26
    seps = [bit for v in physical for bit in [False]+[True]*(v+1)]
    expected = (75,[True],[True]+[False]*47+[True]+seps)
    assert cur == expected
    data = '''module
public import PA196.Literal
@[expose] public section
namespace PA196.Startup
open M6.Zip
/-- Unary register-file encoding, identical to `M6.Runtime.sepsR`. -/
def sepsR (vs : List Nat) : List Bool :=
  vs.flatMap fun v => false :: List.replicate (v + 1) true

def physicalFile : List Nat := [0,0,0,0,0,0,2,0,0] ++ List.replicate 26 1
def blank : Conf := zc 0 [] []
def clean : Conf := zc 75 [true]
  ([true] ++ List.replicate 47 false ++ [true] ++ sepsR physicalFile)
'''
    for i,c in enumerate(checkpoints): data += f'def c{i:04d} : Conf := {conf(c)}\n'
    data += f'''theorem first_eq : c0000 = blank := by decide +kernel
theorem last_eq : c{len(checkpoints)-1:04d} = clean := by decide +kernel
theorem file_length : physicalFile.length = 35 := by decide +kernel
end PA196.Startup
'''
    out['PA196/Startup/Data.lean'] = data
    imports=[]
    for block in range((len(lengths)+PER_FILE-1)//PER_FILE):
        imports.append(f'public import PA196.Startup.S{block:03d}')
        dependency = 'Data' if block == 0 else f'S{block-1:03d}'
        text = f'''module
public import PA196.Startup.{dependency}
public import PA196.FastRun
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
'''
        for i in range(block*PER_FILE,min((block+1)*PER_FILE,len(lengths))):
            text += f'theorem run{i:04d} : run Literal.machine {lengths[i]} c{i:04d} = some c{i+1:04d} := by\n  exact FastRun.checked (by decide +kernel) (by decide +kernel)\n'
        text += 'end PA196.Startup\n'
        out[f'PA196/Startup/S{block:03d}.lean'] = text
    text = 'module\n'+'\n'.join(imports)+'''
@[expose] public section
namespace PA196.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

private theorem compose {M : TMN} {a b c : Conf} {n m : Nat}
    (ha : run M n a = some b) (hb : run M m b = some c) :
    run M (n+m) a = some c := by rw [run_add,ha]; exact hb

/-- The complete blank-tape startup, composed from bounded kernel checks. -/
theorem startup_exact : run Literal.machine 58154 blank = some clean := by
  have step0000 := run0000
'''
    for i in range(1,len(lengths)):
        text += f'  have step{i:04d} := compose step{i-1:04d} run{i:04d}\n'
    text += f'''  simpa only [first_eq,last_eq] using step{len(lengths)-1:04d}

theorem startup_reach : Reach Literal.machine blank clean := ⟨58154,startup_exact⟩

#print axioms startup_exact
end PA196.Startup
'''
    out['PA196/Startup.lean'] = text
    return out

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='verify generated sources without rewriting')
    args = parser.parse_args()
    files = generate()
    failures = []
    for name, text in files.items():
        path = ROOT / name
        if args.check:
            if not path.exists() or path.read_text() != text: failures.append(name)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            if not path.exists() or path.read_text() != text:
                path.write_text(text)
    if failures: raise SystemExit('Stale generated files: ' + ', '.join(failures))
    print(('Checked' if args.check else 'Generated') + f' {len(files)} Lean files; input SHA-256 {SHA256}')
