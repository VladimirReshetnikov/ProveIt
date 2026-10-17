"""Ordinary Mealy-style transition refinement for complete binary TMs.

The independently checked certificate is a total state homomorphism, with
the terminal mapped only to the terminal. It preserves every literal step,
the whole tape, head position, exact halting time and score on every input.
"""
from __future__ import annotations


def minimize(table, start=0):
    N = len(table)//2
    assert set(table) == {(q,b) for q in range(N) for b in (0,1)}
    assert all(0 <= t <= N for w,d,t in table.values())
    colors = {q:0 for q in range(N)}
    while True:
        signatures = {q:tuple((w,d,colors.get(t,-1))
                       for b in (0,1) for w,d,t in [table[q,b]]) for q in range(N)}
        unique = {s:i for i,s in enumerate(dict.fromkeys(signatures.values()))}
        new = {q:unique[signatures[q]] for q in range(N)}
        # The refinement never coarsens. Equal block count therefore means stable.
        if len(set(new.values())) == len(set(colors.values())):
            colors = new
            break
        colors = new
    blocks = {}
    for q in range(N): blocks.setdefault(colors[q],[]).append(q)
    order = [colors[start]] + sorted(set(blocks)-{colors[start]},key=lambda c:min(blocks[c]))
    relabel = {c:j for j,c in enumerate(order)}
    M = len(order)
    mapping = {q:relabel[colors[q]] for q in range(N)}
    mapping[N] = M
    output = {}
    for c in order:
        representative = blocks[c][0]
        for b in (0,1):
            w,d,t = table[representative,b]
            output[relabel[c],b] = w,d,mapping[t]
    certificate = dict(source_states=N,target_states=M,start_source=start,start_target=0,
                       state_map=[mapping[q] for q in range(N+1)],
                       nontrivial_classes=[blocks[c] for c in order if len(blocks[c])>1])
    verify_certificate(table,output,certificate)
    return output, certificate


def verify_certificate(source,target,certificate):
    N,M = certificate["source_states"],certificate["target_states"]
    f = certificate["state_map"]
    assert len(f) == N+1 and f[N] == M
    assert set(source) == {(q,b) for q in range(N) for b in (0,1)}
    assert set(target) == {(q,b) for q in range(M) for b in (0,1)}
    assert set(f[:-1]) == set(range(M))
    assert f[certificate["start_source"]] == certificate["start_target"]
    for q in range(N):
        for b in (0,1):
            w,d,t = source[q,b]
            assert 0 <= t <= N and w in (0,1) and d in ("L","R")
            assert target[f[q],b] == (w,d,f[t])
    return True


def encode(table):
    return ("#! start 0\n" + "".join(
        f"{q} {b} {w} {d} {t}\n" for (q,b),(w,d,t) in sorted(table.items()))).encode()


def parse(data):
    table = {}
    for line in data.decode().splitlines():
        if not line or line.startswith("#"): continue
        q,b,w,d,t = line.split()
        key = int(q),int(b)
        assert key not in table
        table[key] = int(w),d,int(t)
    return table
