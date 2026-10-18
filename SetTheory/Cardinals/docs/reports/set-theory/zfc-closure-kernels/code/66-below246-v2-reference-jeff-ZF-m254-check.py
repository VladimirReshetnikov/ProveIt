#!/usr/bin/env python3
"""Build and check the formalization of zfc_254.tm (portable: Linux / macOS / Windows).

    python3 check.py            # coqc from $COQC, default `coqc` on PATH (Coq 8.20.x)

1. Refuses any of our sources (coq/) containing Admitted / admit / Axiom / Parameter outside comments
   (vendored code is covered by Print Assumptions).
2. Checks that the literal transition table table254 (coq/tm/Table254.v) is exactly the table of
   machine/zfc_254.tm, and that the file has the published sha256.
3. Compiles, in dependency order, the closure of coq/e2e/E2E254.v.  Load paths: our layers
   coq/tm -> M254, coq/prog -> M254P, coq/logic -> M254L, coq/settheory -> M254S; shared with the
   sibling packages: ../stdzf/coq -> ZF, ../stdzf_r3/regcon -> RegCon, ../stdzf_r3/zfc -> ZFC,
   ../stdzf_r3/vendor/undecidability/theories -> Undecidability, ../stdzf_r3/vendor/busycoq -> BusyCoq.
4. Requires "Closed under the global context" 3 times in E2E254.v.  Prints CHECK PASS / CHECK FAIL.
"""
import hashlib, os, re, subprocess, sys, time
from pathlib import Path
for _s in (sys.stdout, sys.stderr):
    try:
        _s.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass

HERE = Path(__file__).resolve().parent
ZF = HERE.parent
COQC = os.environ.get('COQC', 'coqc')
UNDEC = ZF / 'stdzf_r3' / 'vendor' / 'undecidability' / 'theories'
ROOTS = {'Undecidability': [UNDEC], 'BusyCoq': [ZF / 'stdzf_r3' / 'vendor' / 'busycoq'],
         'ZF': [ZF / 'stdzf' / 'coq'], 'RegCon': [ZF / 'stdzf_r3' / 'regcon'], 'ZFC': [ZF / 'stdzf_r3' / 'zfc'],
         'M254': [HERE / 'coq' / 'tm'], 'M254P': [HERE / 'coq' / 'prog'], 'M254L': [HERE / 'coq' / 'logic'],
         'M254S': [HERE / 'coq' / 'settheory']}
TOP = HERE / 'coq' / 'e2e' / 'E2E254.v'
EXPECTED_CLOSED = 3
TM_FILE = HERE / 'machine' / 'zfc_254.tm'
TM_SHA256 = 'd655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb'
WARN = ['-w', '-notation-overridden,-stdlib-vector,-notation-incompatible-prefix,'
              '-postfix-notation-not-level-1,-closed-notation-not-level-0,-deprecated']
LIBFLAGS = ['-set', 'Default Proof Using = Type']     # as in the library's _CoqProject

if os.name == 'nt':                                   # run at Idle priority on Windows
    import ctypes
    ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x40)


def strip_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('(*', i):
            depth += 1; i += 2
        elif text.startswith('*)', i) and depth:
            depth -= 1; i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return ''.join(out)


REQ = re.compile(r'(?:From\s+([\w.]+)\s+)?Require\s+(?:Import\s+|Export\s+)?(.*?)\.(?:\s|$)', re.S)


def resolve(roots, prefix, name):
    """Map a (From prefix, module name) pair to a source file below our load paths, or None (stdlib)."""
    full = f'{prefix}.{name}' if prefix else name
    parts = full.split('.')
    if parts[0] not in roots:
        return None
    for root in roots[parts[0]]:
        f = root.joinpath(*parts[1:]).with_suffix('.v')
        if f.exists():
            return f
    # partially qualified name: a suffix of a module path below the prefix directory
    tail = '/' + '/'.join(name.split('.'))
    for root in roots[parts[0]]:
        base = root.joinpath(*prefix.split('.')[1:]) if prefix else root
        cands = sorted(p for p in base.rglob(name.split('.')[-1] + '.v')
                       if p.with_suffix('').as_posix().endswith(tail))
        if cands:
            return cands[0]
    raise SystemExit(f'cannot resolve {full}')


def deps(roots, f):
    out = []
    for prefix, names in REQ.findall(strip_comments(f.read_text(encoding='utf-8'))):
        if prefix and prefix.split('.')[0] not in roots:
            continue
        for n in names.split():
            if not prefix and n.split('.')[0] not in roots:
                continue
            r = resolve(roots, prefix, n)
            if r is not None:
                out.append(r)
    return out


def closure(roots, top):
    order, seen = [], set()
    def visit(f, stack):
        if f in seen:
            return
        if f in stack:
            raise SystemExit(f'dependency cycle at {f}')
        for d in deps(roots, f):
            visit(d, stack | {f})
        seen.add(f)
        order.append(f)
    visit(top, frozenset())
    return order


def check_table():
    if hashlib.sha256(TM_FILE.read_bytes()).hexdigest() != TM_SHA256:
        return 'machine/zfc_254.tm: sha256 mismatch'
    rows, start = {}, None
    for line in TM_FILE.read_text(encoding='utf-8').splitlines():
        line = line.strip()
        if line.startswith('#!'):
            p = line[2:].split()
            if p and p[0] == 'start':
                start = int(p[1])
        elif line and not line.startswith('#'):
            q, r, w, d, n = line.split()
            assert r in '01' and w in '01' and d in 'LR', line
            assert (int(q), int(r)) not in rows, f'duplicate row {line}'
            rows[(int(q), int(r))] = (int(w), d, int(n))
    if start != 0 or set(rows) != {(q, r) for q in range(254) for r in (0, 1)}:
        return 'zfc_254.tm: expected start 0 and exactly the rows of states 0..253 (254 = halt)'
    text = (HERE / 'coq' / 'tm' / 'Table254.v').read_text(encoding='utf-8')
    body = text[text.index('Definition table254'):]
    tup = re.findall(r'\((true|false), ([LR]), (\d+), (true|false), ([LR]), (\d+)\)', body)
    if len(tup) != 254:
        return f'Table254.v has {len(tup)} rows'
    for q, (w0, d0, n0, w1, d1, n1) in enumerate(tup):
        if rows[(q, 0)] != (int(w0 == 'true'), d0, int(n0)) or rows[(q, 1)] != (int(w1 == 'true'), d1, int(n1)):
            return f'Table254.v row {q} differs from zfc_254.tm'
    return None


def main():
    t0 = time.time()
    bad = [str(f.relative_to(HERE)) for f in (HERE / 'coq').rglob('*.v')
           if re.search(r'\b(Admitted|admit|Axiom|Parameter)\b', strip_comments(f.read_text(encoding='utf-8')))]
    if bad:
        print('forbidden keyword in:', *bad, sep='\n  ')
        print('CHECK FAIL'); return 1
    err = check_table()
    if err:
        print(err); print('CHECK FAIL'); return 1
    print('zfc_254.tm: sha256 ok, 254 states x 2 symbols + halt; literal table = Table254.v table254')
    qflags = [x for p, ds in ROOTS.items() for d in ds for x in ('-Q', os.path.relpath(d, HERE), p)]
    files = closure(ROOTS, TOP)
    print(f'{len(files)} files', flush=True)
    ok = True
    for f in files:
        lib = UNDEC in f.parents
        cmd = [COQC, *qflags, *WARN, *(LIBFLAGS if lib else []), os.path.relpath(f, HERE)]
        t = time.time()
        r = subprocess.run(cmd, cwd=HERE, capture_output=True, text=True, encoding='utf-8', errors='replace')
        if r.returncode:
            print(f'FAILED {os.path.relpath(f, HERE)}\n{r.stdout}{r.stderr}')
            print('CHECK FAIL'); return 1
        if f == TOP:
            print(r.stdout)
            k = r.stdout.count('Closed under the global context')
            print(f'E2E254: {k}/{EXPECTED_CLOSED} closed', flush=True)
            ok = k == EXPECTED_CLOSED and 'Axioms:' not in r.stdout
        else:
            print(f'{time.time() - t:7.1f}s  {os.path.relpath(f, HERE)}', flush=True)
    print(f'total {time.time() - t0:.0f}s')
    print('CHECK', 'PASS' if ok else 'FAIL')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
