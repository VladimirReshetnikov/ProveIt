"""Export the certified, dilated upper-bound body with exact decimal vertices."""
import json
from check_adaptive import DIR, points, face, ring, dot, cross

def decimal(numerator):
    """Render numerator / 10**15 exactly, retaining meaningful digits."""
    whole, tail = divmod(abs(numerator), 10**15)
    text = f"{whole}.{tail:015d}".rstrip("0").rstrip(".")
    return ("-" if numerator < 0 else "") + text

def export():
    pts = points()
    center = (17000000, 13000000, 7000000)
    facets = []
    hints = json.loads((DIR / "adaptive_facets.json").read_text())
    for a,b,c in hints:
        plane = face(pts[a],pts[b],pts[c])
        normal = plane[:3]
        if dot(normal,center) + plane[3] > 0:
            plane = tuple(-v for v in plane)
            normal = plane[:3]
        dist = [dot(normal,p) + plane[3] for p in pts]
        assert max(dist) == 0 and min(dist) < 0
        cycle = ring(pts, [j for j,val in enumerate(dist) if val == 0], normal)
        binding = [pts[j] for j in cycle[:3]]
        u,v = (tuple(b-a for a,b in zip(binding[0],q)) for q in binding[1:])
        orient = dot(cross(u,v),normal)
        assert orient
        facets.append(cycle if orient>0 else cycle[::-1])

    used = sorted({i for cycle in facets for i in cycle})
    ids = {i: j+1 for j,i in enumerate(used)}
    with (DIR / "cover.obj").open("w",encoding="ascii") as out:
        out.write("# Universal convex cover of unit space curves. Exact decimal coordinates.\n")
        for i in used:
            numerators = (2*(5000001*v-c) for v,c in zip(pts[i],center))
            out.write("v " + " ".join(map(decimal,numerators)) + "\n")
        for cycle in facets:
            out.write("f " + " ".join(str(ids[i]) for i in cycle) + "\n")
    print(f"Exported {len(used)} vertices and {len(facets)} outward polygonal faces.")

if __name__ == "__main__":
    export()
