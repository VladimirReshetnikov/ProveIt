"""Decode the Bouwkamp code of Duijvestijn's order-21 simple perfect squared
square (side 112) into explicit placements, and verify the tiling exactly.

Bouwkamp convention: squares are listed in groups; each successive square is
placed with its top-left corner at the leftmost point of the currently
uppermost horizontal segment of the "skyline" (y grows downward).
"""

CODE = [[50, 35, 27], [8, 19], [15, 17, 11], [6, 24], [29, 25, 9, 2],
        [7, 18], [16], [42], [4, 37], [33]]
SIDE = 112

sizes = [s for g in CODE for s in g]
assert len(sizes) == 21 and len(set(sizes)) == 21

heights = [0] * SIDE  # depth of filled region per column, measured from top
placements = []       # (x, y_top_down, s)

for s in sizes:
    h = min(heights)
    x = heights.index(h)
    # width of the flat run at this height starting at x
    w = 0
    while x + w < SIDE and heights[x + w] == h:
        w += 1
    assert s <= w, f"square {s} does not fit flat run of width {w} at x={x}, h={h}"
    for c in range(x, x + s):
        heights[c] = h + s
    placements.append((x, h, s))

assert all(h == SIDE for h in heights), heights

# convert to y-up coordinates: y_up = SIDE - (y_top_down + s)
tiles = [(x, SIDE - (y + s), s) for (x, y, s) in placements]

# independent verification on the unit grid
cover = [[0] * SIDE for _ in range(SIDE)]
for (x, y, s) in tiles:
    assert 0 <= x and x + s <= SIDE and 0 <= y and y + s <= SIDE
    for i in range(x, x + s):
        for j in range(y, y + s):
            cover[i][j] += 1
assert all(cover[i][j] == 1 for i in range(SIDE) for j in range(SIDE)), "overlap/gap"
assert sum(s * s for (_, _, s) in tiles) == SIDE * SIDE

print("verified: 21 pairwise-distinct squares tile the 112 x 112 square")
print("tiles (x, y, s) with mathematical y-up coordinates:")
for t in sorted(tiles, key=lambda t: (-t[2])):
    print(f"  {t}")
print()
print("Lean/Coq order (placement order):")
for t in tiles:
    print(f"  {t}")
