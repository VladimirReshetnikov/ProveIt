#!/usr/bin/env python3
"""Rebuild PA194P5 and replay exact finite/symbolic certificates (Python 3.10+).
No network or third-party Python package is required. Do not use Python -O.
The symbolic register-box contracts are inherited lemmas, not re-proved here.
"""
from pathlib import Path
import hashlib, importlib.util, json, sys
ROOT = Path(__file__).resolve().parent
BASE = ROOT / "reference"
OLD = [6, 2, 0, 4, 3, 7, 8, 5, 1]
NEW = [6, 3, 0, 2, 4, 8, 7, 5, 1]
PI = [0, 1, 3, 4, 2, 5, 6, 8, 7]
SK = [51, 36, 25, 48, 32, 33, 22, 55, 60]
HASH_BASE = "4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f"
HASH_CHILD = "cf3a2c2d3ba8e95d5c0ea825c3f279ae529b6591cc1280264b0ba3793e77d026"
HASH_NATIVE = "a9d3a13786b6a0018713d8803865860b5e9e26692fde34975545c3bb0f09501c"
CHANGES = {42: (60, 85), 48: (68, 114), 73: (85, 60),
           109: (95, 68), 110: (95, 68), 120: (68, 114), 124: (114, 95)}
def digest(s):
    return hashlib.sha256(s.encode("ascii")).hexdigest()
def parse(s):
    rows = {}
    for line in s.splitlines():
        if not line.strip() or line.lstrip().startswith("#"): continue
        q,b,w,d,n = line.split()
        assert d in ("L","R")
        key = int(q),int(b)
        assert key not in rows
        rows[key] = int(w),d=="R",int(n)
    return rows
def encode(rows):
    return "".join(f"{q} {b} {w} {'R' if d else 'L'} {n}\n"
                   for (q,b),(w,d,n) in sorted(rows.items()))
def simulate(rows, target_steps):
    state, head, ones = 0, 0, set()
    for t in range(target_steps):
        assert state != 194, ("premature halt",t)
        w,d,state = rows[state,int(head in ones)]
        (ones.add if w else ones.discard)(head)
        head += 1 if d else -1
    return state,head,ones
def expected_seed():
    # Source site25 is path100000, header distance48, nine work blocks,
    # followed by26 one-valued spare blocks. All exterior cells are zero.
    h=-2
    ones={h-1,h,h+48}
    pos=h+49
    physical=[0,0,0,0,0,0,2,0,0]+[1]*26
    for value in physical:
        pos+=1
        ones.update(range(pos,pos+value+1))
        pos+=value+1
    return (24,h,ones)
def main():
    if not __debug__: raise SystemExit("Run without -O: assertions are certificate checks.")
    parent_text=(BASE/"pa194.tm").read_text()
    assert digest(parent_text)==HASH_BASE
    parent=parse(parent_text)
    child=dict(parent)
    for q,(old,new) in CHANGES.items():
        assert child[q,1]==(0,True,old)
        child[q,1]=(0,True,new)
    child_text=encode(child)
    assert digest(child_text)==HASH_CHILD
    assert child_text==(ROOT/"machine/pa194p5.tm").read_text()
    controls={q for q,b in child}
    assert controls==set(range(194)) and len(child)==388
    assert all((q,b) in child for q in controls for b in (0,1))
    assert {n for w,d,n in child.values()}-controls=={194}
    reached={0}
    while True:
        extra={n for (q,b),(w,d,n) in child.items() if q in reached and n!=194}
        if extra <= reached: break
        reached |= extra
    assert reached==controls
    labels=json.loads((BASE/"pa194.labels.json").read_text())
    native={(labels[q],b):(w,d,labels[n]) for (q,b),(w,d,n) in child.items()}
    original_native=parse((BASE/"pa194.native.tm").read_text())
    assert len(set(PI))==9 and all(NEW[r]==PI[OLD[r]] for r in range(9))
    routed={}
    for (q,b),(w,d,n) in original_native.items():
        if q not in SK and n in SK:
            assert (b,w,d)==(1,0,True)
            n=SK[PI[SK.index(n)]]
        routed[q,b]=(w,d,n)
    assert routed==native
    assert digest(encode(native))==HASH_NATIVE
    assert encode(native)==(ROOT/"machine/pa194p5.native.tm").read_text()
    assert sum(child[k]!=parent[k] for k in parent)==7
    seed=expected_seed()
    assert simulate(parent,58154)==seed
    assert simulate(child,56158)==seed
    spec=importlib.util.spec_from_file_location("retained_runtime",BASE/"symbolic_runtime.py")
    runtime=importlib.util.module_from_spec(spec);spec.loader.exec_module(runtime)
    assert all(native[q,b]==original_native[q,b] for q in runtime.BOXSTATES for b in (0,1))
    runtime.PHYSICAL[:]=NEW
    sites=json.loads((BASE/"pa194.sites.json").read_text())
    ins=json.loads((BASE/"pa194.instructions.json").read_text())
    assert len(sites)==len(ins)==3673 and sites[25][0]=="100000"
    cs=[]
    for i,code in enumerate(ins):
        st=runtime.frame(tuple(map(int,sites[i][0])))
        def endpoint(j,extra=0,effect=runtime.PLAIN):
            return runtime.canonical(runtime.frame(tuple(map(int,sites[j][0])),extra,effect))
        if code[0]=="inc":
            _,r,n=code
            cs.append((i,None,st,endpoint(n,0,("x","inc",NEW[r]))))
        elif code[0]=="dec":
            _,r,z,p=code
            cs.append((i,(NEW[r],True),st,endpoint(z)))
            cs.append((i,(NEW[r],False),st,endpoint(p,1,("x","dec",NEW[r]))))
        elif code[0]=="jump":
            cs.append((i,None,st,endpoint(code[1])))
        else:
            assert code==["halt"]
            cs.append((i,None,st,None))
    result=runtime.validate(native,cs)
    assert result=={"ok":True,"contracts":4780,"max_steps":497,"total_steps":1479348}
    receipt={"candidate":"PA194P5","states":194,"transitions":388,
             "dense_sha256":HASH_CHILD,"native_sha256":HASH_NATIVE,
             "source_sites":3673,"symbolic":result,
             "startup_steps":56158,"parent_startup_steps":58154,
             "entire_seed_tape_identical":True,"seed_state_dense":24,
             "seed_head":-2,"seed_one_cells":sorted(seed[2]),
             "physical_map":NEW,"changed_transitions":7,
             "arithmetic_box_rows_unchanged":True,"kernel_checked":False}
    print(json.dumps(receipt,indent=2))
if __name__=="__main__": main()
