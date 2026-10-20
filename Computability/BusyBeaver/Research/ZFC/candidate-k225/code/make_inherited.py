"""Write zfc_k225_old.tm: the delivered legacy-label table (start 95, dispatcher 96, halt 254)
with its working labels above 253 renumbered into the lowest free labels, so that Source 103's
checkers (which hard-code fold241's engine labels) apply. Also checks, by a BFS canonical form,
that the delivered canonical table zfc_k225.tm is the same machine.
Usage: make_inherited.py   (run from the page directory)"""
import hashlib, json


def load(p):
    T, start = {}, None
    for l in open(p):
        if l.startswith("#! start"): start = int(l.split()[2])
        elif l.strip() and not l.startswith("#"):
            q, b, w, d, z = l.split(); T[int(q), int(b)] = (int(w), d, int(z))
    return T, start


def canon(T, start):
    states = {q for q, _ in T}; order, seen, i = [start], {start}, 0
    while i < len(order):
        q = order[i]; i += 1
        for b in (0, 1):
            z = T[q, b][2]
            if z in states and z not in seen: seen.add(z); order.append(z)
    order += sorted(states - seen); m = {q: k for k, q in enumerate(order)}
    for z in {z for *_, z in T.values() if z not in states}: m[z] = len(order)
    return hashlib.sha256("".join(f"{m[q]} {b} {w} {d} {m[z]}\n" for (q, b), (w, d, z)
                                  in sorted(T.items(), key=lambda x: (m[x[0][0]], x[0][1]))).encode()).hexdigest()


T, st = load("ingredients/candidate225_legacy.tm")
assert st == 95
states = sorted({q for q, _ in T}); free = [x for x in range(254) if x not in states]
ren = {q: (q if q < 254 else free.pop(0)) for q in states}; ren[254] = 254
N = {(ren[q], b): (w, d, ren[z]) for (q, b), (w, d, z) in T.items()}
text = "#! start 95\n" + "".join(f"{q} {b} {w} {d} {z}\n" for (q, b), (w, d, z) in sorted(N.items()))
open("zfc_k225_old.tm", "w", newline="\n").write(text)
json.dump({"legacy_to_inherited": {str(k): v for k, v in ren.items() if k != v}}, open("ingredients/legacy_compaction.json", "w"), indent=1)
C, cs = load("zfc_k225.tm")
assert canon(N, 95) == canon(C, cs), "canonical table differs from the legacy table"
print("zfc_k225_old.tm", hashlib.sha256(text.encode()).hexdigest(), "states", len(states), "; same machine as zfc_k225.tm")
