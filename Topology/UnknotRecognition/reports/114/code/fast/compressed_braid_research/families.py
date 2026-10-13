from fastunknot.compressed_braid.grammar import Builder


def sleeve(k, *, negative=False, reassociated=False):
    b = Builder()
    m = 1 << k
    u = b.power(b.word([1, -2]), m)
    v = b.word([1, -2] * 2 if negative else [1, 2])
    if reassociated:
        # Same conjugating word with a deliberately different SLP parse.
        other = b.concat(b.concat(b.letter(1), b.power(b.word([-2, 1]), m - 1)), b.letter(-2))
        inverse = b.inverse(other)
    else:
        inverse = b.inverse(u)
    return b.data(b.concat(b.concat(u, v), inverse))


def singleton_forest(factors, k, *, negative_index=None):
    out, interner = [['e']], {}
    def add(rule):
        key = tuple(rule)
        if key not in interner:
            interner[key] = len(out)
            out.append(rule)
        return interner[key]
    def cat(u, v):
        return add(['c', u, v]) if u and v else (u or v)
    root = 0
    for block in range(factors):
        local = sleeve(k, negative=block == negative_index)
        mapped = [0]
        for rule in local['rules'][1:]:
            if rule[0] == 'g':
                g = rule[1]
                value = add(['g', (1 if g > 0 else -1) * (abs(g) + 3 * block)])
            else:
                value = cat(mapped[rule[1]], mapped[rule[2]])
            mapped.append(value)
        root = cat(root, mapped[local['root']])
    for block in range(1, factors):
        root = cat(root, add(['g', 3 * block]))
    return dict(strands=3 * factors, rules=out, root=root)
