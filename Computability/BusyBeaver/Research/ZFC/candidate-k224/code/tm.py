def load(p):
    T = {}
    for line in open(p, encoding="utf-8"):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        q, b, w, d, r = line.split()
        T[(int(q), int(b))] = (int(w), d, int(r))
    return T

def diff(a, b, na, nb):
    sa = {q for q, _ in a}; sb = {q for q, _ in b}
    print(f"{na}: {len(sa)} states; {nb}: {len(sb)} states")
    print("  only in", na, sorted(sa - sb)); print("  only in", nb, sorted(sb - sa))
    for k in sorted(set(a) & set(b)):
        if a[k] != b[k]:
            print(f"  {k[0]}/{k[1]}: {a[k]} -> {b[k]}")
