"""Exhaust the ordered two-member covers on three labeled vertices."""
from itertools import product
from nerve_transfer import Cover, boundary, parity_sum, bits, mask


def subchains(basis):
    return [{b for i, b in enumerate(basis) if choice & (1 << i)}
            for choice in range(1 << len(basis))]


def valid_complex(simplices):
    return all((boundary(s) - {0}) <= simplices for s in simplices)


def chain_boundary(chain, augmented):
    result = parity_sum(boundary(s) for s in chain)
    return result if augmented else result - {0}


def cycles_and_boundaries(space, rank, augmented):
    basis = set(space)
    if augmented:
        basis.add(0)
    source = [s for s in basis if s.bit_count() == rank]
    fills = [s for s in basis if s.bit_count() == rank + 1]
    cycles = [chain for chain in subchains(source) if not chain_boundary(chain, augmented)]
    boundaries = [chain_boundary(chain, augmented) for chain in subchains(fills)]
    return cycles, boundaries


def acyclic(space):
    for rank in range(4):
        cycles, boundaries = cycles_and_boundaries(space, rank, True)
        if any(cycle not in boundaries for cycle in cycles):
            return False
    return True


def map_indices(cycle, mapping):
    output = set()
    for s in cycle:
        img = mask(*(mapping[i] for i in bits(s)))
        if img.bit_count() == s.bit_count():
            output ^= {img}
    return output


def run():
    spaces = [s for s in subchains(range(1, 8)) if valid_complex(s)]
    counts = dict(accepted=0, obstructed=0, round_trips=0, squares=0)
    for left, right in product(spaces, repeat=2):
        space = left | right
        intersections = [part for part in (left, right, left & right) if part]
        expected = all(acyclic(part) for part in intersections)
        try:
            cover = Cover(space, [left, right])
        except ValueError:
            assert not expected
            counts["obstructed"] += 1
            continue
        assert expected
        counts["accepted"] += 1
        reverse = Cover(space, [right, left])
        # This compatible cover map takes both members into one if the base is acyclic.
        merged = Cover(space, [space]) if not space or acyclic(space) else None
        for rank in (1, 2, 3):
            maps = [([1, 0], reverse)]
            if merged is not None:
                maps.append(([0, 0], merged))
            for side, faces in (("space", space), ("nerve", cover.intersections.keys())):
                cycles, boundaries = cycles_and_boundaries(faces, rank, False)
                other = "nerve" if side == "space" else "space"
                for src in cycles:
                    dest = cover.transfer(src, side)
                    back = cover.transfer(dest, other)
                    assert back ^ src in boundaries
                    counts["round_trips"] += 1
                    if side == "space":
                        for mapping, target in maps:
                            lhs = target.transfer(src, side)
                            rhs = map_indices(dest, mapping)
                            _, target_boundaries = cycles_and_boundaries(
                                target.intersections.keys(), rank, False)
                            assert lhs ^ rhs in target_boundaries
                            counts["squares"] += 1
    print(f"{len(spaces)} finite complexes; " + ", ".join(f"{k}={v}" for k,v in counts.items()))


if __name__ == "__main__":
    run()
