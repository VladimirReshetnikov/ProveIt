"""Independent full search at 131 (including the optional zero residue)."""
from replay_previous import enumerate_max
from verify import depths

steps=((1,0),(0,1),(0,42),(1,20),(28,18))
p=131
result=enumerate_max(p)
print("Normalized list counts and maxima (zero allowed, nonzero only):", result)
assert result==([46849,46816],[540,540])
r=list(depths(p,steps))
assert [i for i,x in enumerate(r) if x!=2]==[61,89]
assert r[61]==r[89]==5
assert len({min((x,y),(-x%p,-y%p)) for x,y in steps})==5
print("Witness exceptional directions: (1,61), (1,89), both of depth 5.")
