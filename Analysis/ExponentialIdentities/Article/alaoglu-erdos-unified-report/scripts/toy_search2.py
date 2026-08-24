"""Same exact laboratory, but enumerate the balance lattice with a REDUCED basis
(adjacent-ratio relations), which reaches patterns with all coefficients moderate."""
import numpy as np, json, itertools, sys
Vu = np.load("V.npy"); lab = json.load(open("lab.json"))
cells=[tuple(x) for x in lab["cells"]]; w=np.array(lab["w"],dtype=np.int64)
# reduced lattice basis of {c : c.w = 0}; ratios w[k+1]/w[k] = 5,11,5,11,5,5
ratios=[w[k+1]//w[k] for k in range(6)]
assert all(w[k]*ratios[k]==w[k+1] for k in range(6)), ratios
Bas=np.zeros((6,7),dtype=np.int64)
for k in range(6):
    Bas[k,k]=-ratios[k]; Bas[k,k+1]=1
assert np.all(Bas@w==0)
print("reduced basis rows:"); print(Bas)
B=int(sys.argv[1]) if len(sys.argv)>1 else 4
rng=list(range(-B,B+1))
coef=np.array(list(itertools.product(rng,repeat=6)),dtype=np.int64)
C=coef@Bas
nz=np.any(C!=0,axis=1); C=C[nz]
print("nonzero balanced vectors:",C.shape[0],"  max |c| =",int(np.abs(C).max()))
assert np.all(C@w==0)
def tails_ok(c):
    for j in sorted({j for (i,j) in cells}):
        idx=sorted([k for k,(i,jj) in enumerate(cells) if jj==j],key=lambda k:cells[k][0])
        s=0
        for k in reversed(idx):
            s+=c[k]
            if s<0: return False
    return True
found=[]
CH=20000
for s in range(0,C.shape[0],CH):
    blk=C[s:s+CH]; val=blk@Vu.T; ok=val.min(axis=1)>=0
    for r in np.nonzero(ok)[0]: found.append(blk[r].copy())
print("INTEGRAL nonzero balanced patterns:",len(found))
for c in found[:30]:
    print("   ",dict(zip(cells,[int(x) for x in c])),"top-heavy:",tails_ok(c))
# how close does anything get?  report the best (max over patterns of min_p v_p)
best=-10**9;bc=None
for s in range(0,C.shape[0],CH):
    blk=C[s:s+CH]; val=(blk@Vu.T).min(axis=1)
    r=int(val.argmax())
    if val[r]>best: best=int(val[r]); bc=blk[r].copy()
print("best min_p v_p(F) over all nonzero balanced patterns:",best,"at",dict(zip(cells,[int(x) for x in bc])))
