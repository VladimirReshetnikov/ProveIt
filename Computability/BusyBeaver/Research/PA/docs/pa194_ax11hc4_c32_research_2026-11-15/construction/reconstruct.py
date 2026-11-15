#!/usr/bin/env python3
"""Offline reconstruction and exact startup verification of PA194C32.

Python 3.10+, standard library only. No network or repository checkout needed.
The embedded baseline is the primary PA194 native table pinned in ProveIt
2ca99e3d23a5397aae4c786f4da7dfe1cca87f85, reconstructed from raw201 and folds.
This checks literal tables, physical allocation, and complete blank startup.
Universal source verification is documented separately; this script does not
prove the unfinished iPRA-to-Con(PA) calibration.
"""
from pathlib import Path
import argparse, base64, hashlib, json

BASELINE_B64 = "MCAwIDEgUiA5NAowIDEgMSBSIDAKMSAwIDAgTCAxCjEgMSAxIEwgMgoyIDAgMCBMIDMKMiAxIDEgTCAyCjMgMCAwIEwgNQozIDEgMSBMIDIKNCAwIDEgUiA2CjQgMSAwIEwgNAo1IDAgMCBMIDkKNSAxIDEgTCAyCjYgMCAwIFIgNgo2IDEgMCBSIDEwCjggMCAwIFIgMTQKOCAxIDEgUiAxMwo5IDAgMCBMIDE1CjkgMSAxIEwgMgoxMCAwIDAgTCAxNgoxMCAxIDAgUiAxMAoxMSAwIDAgTCAyNgoxMSAxIDEgUiAxOAoxMiAwIDAgUiAxOQoxMiAxIDEgUiAyMAoxMyAwIDAgTCA5MQoxMyAxIDEgTCAzMQoxNCAwIDAgTCAxMQoxNCAxIDAgUiAyMgoxNSAwIDAgTCAyMwoxNSAxIDEgTCAyCjE2IDAgMSBMIDEKMTYgMSAwIEwgMQoxNyAwIDAgUiAyNAoxNyAxIDAgUiAzMgoxOCAwIDAgUiA5NgoxOCAxIDAgTCAxMDgKMTkgMCAwIFIgMjgKMTkgMSAxIFIgMjkKMjAgMCAwIFIgMzAKMjAgMSAxIFIgMzEKMjEgMCAwIFIgMjQKMjEgMSAwIFIgNjAKMjIgMCAwIFIgMzMKMjIgMSAxIFIgMjIKMjMgMCAwIEwgMzQKMjMgMSAxIEwgMgoyNCAwIDAgTCAzNQoyNCAxIDAgUiAwCjI1IDAgMCBSIDM2CjI1IDEgMSBSIDI1CjI2IDAgMCBSIDE5NAoyNiAxIDEgUiA0MgoyNyAwIDAgUiAzOQoyNyAxIDAgTCA0MAoyOCAwIDAgUiA0MQoyOCAxIDEgUiA0MgoyOSAwIDAgUiA0MwoyOSAxIDEgUiA0NAozMCAwIDAgUiA0NQozMCAxIDEgUiA0NgozMSAwIDAgUiAyMQozMSAxIDEgUiA0NwozMiAwIDAgUiA0OAozMiAxIDEgUiAzMgozMyAwIDAgUiAzMgozMyAxIDEgUiAzMwozNCAwIDAgTCA3NQozNCAxIDEgTCAyCjM1IDAgMSBSIDM1CjM1IDEgMSBMIDEKMzYgMCAwIFIgNTEKMzYgMSAxIFIgMzYKMzggMCAwIFIgMjgKMzggMSAxIFIgMjAKMzkgMCAwIEwgMTEKMzkgMSAwIFIgMzYKNDAgMCAwIEwgNAo0MCAxIDEgTCA1NAo0MSAwIDAgUiAyNAo0MSAxIDAgUiAyNQo0MiAwIDAgUiAxMwo0MiAxIDAgTCAxNgo0MyAwIDAgUiA1Ngo0MyAxIDEgUiA1Nwo0NCAwIDAgUiA1OAo0NCAxIDEgUiA1OQo0NSAwIDAgUiAyNAo0NSAxIDAgUiA1NQo0NiAwIDAgUiA2MQo0NiAxIDEgUiA2Mgo0NyAwIDAgUiA2Mwo0NyAxIDAgTCAxNgo0OCAwIDAgUiAyNQo0OCAxIDEgUiA0OAo0OSAwIDAgTCAzNQo0OSAxIDAgUiA2NAo1MSAwIDAgUiAxNgo1MSAxIDEgUiA1MQo1MyAwIDAgUiA2OAo1MyAxIDEgUiA2OQo1NCAwIDAgTCA0MAo1NCAxIDEgTCA1NAo1NSAwIDAgUiAyMgo1NSAxIDEgUiA1NQo1NiAwIDAgTCAxMQo1NiAxIDAgUiA1MQo1NyAwIDAgUiA2MQo1NyAxIDAgTCAxNgo1OCAwIDAgUiA3MAo1OCAxIDEgUiA3MQo1OSAwIDAgUiA2Mgo1OSAxIDEgUiA3Mgo2MCAwIDAgUiA1NQo2MCAxIDEgUiA2MAo2MSAwIDAgUiA0OQo2MSAxIDAgUiAyNQo2MiAwIDAgTCAyOAo2MiAxIDEgTCA3Mwo2MyAwIDAgTCAxMjMKNjMgMSAxIEwgMzAKNjQgMCAwIFIgNzQKNjQgMSAxIFIgNjQKNjYgMCAxIFIgMTk4CjY2IDEgMSBMIDU0CjY4IDAgMCBSIDc3CjY4IDEgMSBSIDI1NAo2OSAwIDAgTCAyMTMKNjkgMSAxIFIgMzEKNzAgMCAwIFIgNDEKNzAgMSAxIFIgNjMKNzEgMCAwIEwgOTEKNzEgMSAxIFIgODAKNzIgMCAwIFIgNTYKNzIgMSAxIEwgODEKNzMgMCAwIFIgODIKNzMgMSAxIFIgODMKNzQgMCAxIFIgMAo3NCAxIDEgUiA2NAo3NSAwIDAgUiA3NQo3NSAxIDEgUiA4NAo3NyAwIDAgUiA4Nwo3NyAxIDEgUiA4OAo4MCAwIDAgUiA5MQo4MCAxIDEgTCAxMzgKODEgMCAwIEwgMTExCjgxIDEgMSBSIDU3CjgyIDAgMCBSIDQ5CjgyIDEgMCBSIDMzCjgzIDAgMCBSIDkzCjgzIDEgMCBMIDQyCjg0IDAgMCBSIDUzCjg0IDEgMSBSIDMxMAo4NyAwIDAgUiAzMDEKODcgMSAxIFIgMjEKODggMCAwIFIgMTIyCjg4IDEgMSBSIDEwMwo5MCAwIDAgUiAxMDUKOTAgMSAxIFIgMTA2CjkxIDAgMCBSIDgyCjkxIDEgMSBSIDgxCjkyIDAgMCBSIDEwNAo5MiAxIDEgUiAxODUKOTMgMCAwIFIgMTA4CjkzIDEgMSBSIDEwOQo5NCAwIDAgUiA2Ngo5NCAxIDAgUiAwCjk1IDAgMCBSIDI3Cjk1IDEgMSBSIDExMAo5NiAwIDAgUiAxMDEKOTYgMSAxIFIgMTAwCjk3IDAgMSBMIDExMwo5NyAxIDEgTCA5Nwo5OCAwIDAgUiAxOQo5OCAxIDEgUiAxMTQKOTkgMCAwIFIgNjEKOTkgMSAxIFIgNjEKMTAwIDAgMCBSIDE3NAoxMDAgMSAxIFIgMTY0CjEwMSAwIDAgTCAyNgoxMDEgMSAxIFIgMjAwMAoxMDMgMCAwIFIgMTA4CjEwMyAxIDAgTCAzMDIKMTA0IDAgMCBSIDEyMwoxMDQgMSAxIFIgMTI0CjEwNSAwIDAgUiA3MgoxMDUgMSAxIFIgNTkKMTA2IDAgMCBSIDU4CjEwNiAxIDEgUiAxMjUKMTA3IDAgMCBSIDIxCjEwNyAxIDEgUiAxMjYKMTA4IDAgMCBSIDIxCjEwOCAxIDAgTCAxMAoxMDkgMCAwIFIgNjIKMTA5IDEgMSBSIDQyCjExMCAwIDAgUiAxMjcKMTEwIDEgMSBSIDgKMTExIDAgMCBSIDEwNAoxMTEgMSAxIFIgMTI4CjExMyAwIDAgTCAzMDIKMTEzIDEgMCBMIDk3CjExNCAwIDAgUiAxMzAKMTE0IDEgMSBSIDEwNwoxMjIgMCAwIEwgMTM3CjEyMiAxIDAgTCAxCjEyMyAwIDAgUiAzOQoxMjMgMSAxIFIgNzMKMTI0IDAgMCBSIDYyCjEyNCAxIDEgUiAxMzgKMTI1IDAgMCBSIDYyCjEyNSAxIDEgUiAxMzkKMTI2IDAgMCBSIDcxCjEyNiAxIDAgTCAxNgoxMjcgMCAwIFIgMTQKMTI3IDEgMSBSIDEzOAoxMjggMCAwIFIgMjEKMTI4IDEgMSBSIDE0MQoxMzAgMCAwIFIgMTQ0CjEzMCAxIDEgTCAyMAoxMzcgMCAwIFIgMzAKMTM3IDEgMSBSIDcwCjEzOCAwIDAgUiAzOQoxMzggMSAxIEwgMTMwCjEzOSAwIDAgUiAxOTAKMTM5IDEgMCBMIDE2CjE0MSAwIDAgUiAxNjEKMTQxIDEgMCBMIDE2CjE0NCAwIDAgUiAyNAoxNDQgMSAwIFIgNDgKMTYxIDAgMCBSIDQ5CjE2MSAxIDAgUiAzMgoxNjQgMCAwIFIgNzcKMTY0IDEgMSBSIDk4CjE2NiAwIDAgUiAxOQoxNjYgMSAxIFIgMTc5CjE3NCAwIDAgUiAyMTMKMTc0IDEgMSBSIDI4CjE3OSAwIDAgUiAxOTQKMTc5IDEgMSBSIDEyOAoxODUgMCAwIFIgMTA3CjE4NSAxIDEgUiA5OAoxODggMCAwIFIgOTUKMTg4IDEgMSBSIDExMQoxOTAgMCAwIFIgOTkKMTkwIDEgMSBSIDk5CjE5NCAwIDAgUiAxNwoxOTQgMSAxIEwgMTM3CjE5NiAwIDAgUiA3NwoxOTYgMSAxIFIgMTIyCjE5NyAwIDAgUiAxMDkKMTk3IDEgMSBSIDEzMAoxOTggMCAxIEwgNDAKMTk4IDEgMSBMIDExMwoyMTMgMCAwIFIgOTIKMjEzIDEgMSBSIDkwCjIxNCAwIDAgUiAxODgKMjE0IDEgMSBSIDMxMgoyMTcgMCAwIFIgMTk3CjIxNyAxIDEgUiAxOTYKMjIxIDAgMCBSIDE5NgoyMjEgMSAxIFIgMjE3CjMwMSAwIDAgUiA0NQozMDEgMSAxIFIgMTAzCjMwMiAwIDAgTCA0CjMwMiAxIDAgTCAzMDIKMzEwIDAgMCBSIDIxNAozMTAgMSAxIFIgNjIKMzEyIDAgMCBSIDExCjMxMiAxIDEgUiAzOAoyMDAwIDAgMCBSIDIwMDEKMjAwMCAxIDEgUiAyMDMzCjIwMDEgMCAwIFIgMjAwMgoyMDAxIDEgMSBSIDIwMDUKMjAwMiAwIDAgUiAxMgoyMDAyIDEgMSBSIDIwMDMKMjAwMyAwIDAgUiAyMDA0CjIwMDMgMSAxIFIgOTkKMjAwNCAwIDAgUiA5OAoyMDA0IDEgMSBSIDkwCjIwMDUgMCAwIFIgMjAwNgoyMDA1IDEgMSBSIDIwMjMKMjAwNiAwIDAgUiAyMDA3CjIwMDYgMSAxIFIgMjAxNAoyMDA3IDAgMCBSIDY5CjIwMDcgMSAxIFIgMjAwOAoyMDA4IDAgMCBSIDIwMDkKMjAwOCAxIDEgUiAyMDE5CjIwMDkgMCAwIFIgMjAxMAoyMDA5IDEgMSBSIDIwMTEKMjAxMCAwIDAgUiAxMgoyMDEwIDEgMSBSIDIwMDQKMjAxMSAwIDAgUiAyMTMKMjAxMSAxIDEgUiAyMDEyCjIwMTIgMCAwIFIgMjAxMwoyMDEyIDEgMSBSIDIwMTUKMjAxMyAwIDAgUiA5OAoyMDEzIDEgMSBSIDIwMTQKMjAxNCAwIDAgTCAyMDUwCjIwMTQgMSAxIEwgMjA2NAoyMDE1IDAgMCBMIDIwNDQKMjAxNSAxIDEgUiAyMDE3CjIwMTcgMCAwIFIgMjAyNwoyMDE3IDEgMSBSIDIwMDIKMjAxOSAwIDAgTCAyMDU5CjIwMTkgMSAxIEwgMjA1NgoyMDIwIDAgMCBSIDIwMjEKMjAyMCAxIDEgUiAyMDAzCjIwMjEgMCAwIFIgMjAzMgoyMDIxIDEgMSBSIDkwCjIwMjMgMCAwIFIgMjA0NgoyMDIzIDEgMSBSIDIwMjkKMjAyNSAwIDAgUiAxMgoyMDI1IDEgMSBSIDIwMjYKMjAyNiAwIDAgUiAxNjYKMjAyNiAxIDEgUiAyMDI3CjIwMjcgMCAwIFIgOTAKMjAyNyAxIDEgTCAyMDIwCjIwMjggMCAwIFIgMjAwMwoyMDI4IDEgMSBSIDIwMDIKMjAyOSAwIDAgUiAyMDMwCjIwMjkgMSAxIFIgMjAzMQoyMDMwIDAgMCBSIDIwMjYKMjAzMCAxIDEgUiA5MAoyMDMxIDAgMCBSIDEyCjIwMzEgMSAxIFIgMjAzMgoyMDMyIDAgMCBMIDIwMDIKMjAzMiAxIDEgUiA2MQoyMDMzIDAgMCBSIDIwMzQKMjAzMyAxIDEgUiAyMDM5CjIwMzQgMCAwIFIgMjAyNQoyMDM0IDEgMSBSIDIwMzUKMjAzNSAwIDAgUiA2MQoyMDM1IDEgMSBSIDIwMzYKMjAzNiAwIDAgUiAyMDE1CjIwMzYgMSAxIFIgNjEKMjAzOCAwIDAgUiAxNjYKMjAzOCAxIDEgUiAyMDMyCjIwMzkgMCAwIFIgMjA1MgoyMDM5IDEgMSBSIDIwNDAKMjA0MCAwIDAgUiAyMDQxCjIwNDAgMSAxIFIgMjA2NgoyMDQxIDAgMCBSIDIwNDIKMjA0MSAxIDEgUiAyMDQ3CjIwNDIgMCAwIFIgMjA0MwoyMDQyIDEgMSBSIDIwNDQKMjA0MyAwIDAgUiAyMDM1CjIwNDMgMSAxIFIgMjAxOQoyMDQ0IDAgMCBSIDIwNDUKMjA0NCAxIDEgUiAyMDQ2CjIwNDUgMCAwIFIgMjAzOAoyMDQ1IDEgMSBSIDYxCjIwNDYgMCAwIEwgMjAzMwoyMDQ2IDEgMSBSIDIwMjgKMjA0NyAwIDAgUiAyMDQ4CjIwNDcgMSAxIFIgMjA1MwoyMDQ4IDAgMCBSIDIwMjcKMjA0OCAxIDEgUiAyMDQ5CjIwNDkgMCAwIFIgMjA1MAoyMDQ5IDEgMSBSIDIwMjkKMjA1MCAwIDAgUiAyMDUxCjIwNTAgMSAxIFIgMjAzMQoyMDUxIDAgMCBSIDE2NgoyMDUxIDEgMSBSIDIwNTIKMjA1MiAwIDAgUiAxNjYKMjA1MiAxIDEgTCAyMDA1CjIwNTMgMCAwIFIgMjA1NAoyMDUzIDEgMSBSIDE5NAoyMDU0IDAgMCBSIDIwMTkKMjA1NCAxIDEgUiAyMDU2CjIwNTYgMCAwIFIgMjA1NwoyMDU2IDEgMSBSIDIwNTgKMjA1NyAwIDAgUiAyMDI3CjIwNTcgMSAxIFIgMjAzOAoyMDU4IDAgMCBSIDIwNTkKMjA1OCAxIDEgUiAyMDIxCjIwNTkgMCAwIFIgMjAxNAoyMDU5IDEgMSBSIDIwNjMKMjA2MSAwIDAgUiA5MAoyMDYxIDEgMSBSIDIwNjIKMjA2MiAwIDAgUiAyMDIxCjIwNjIgMSAxIFIgOTAKMjA2MyAwIDAgUiAyMDIwCjIwNjMgMSAxIFIgMjA2NAoyMDY0IDAgMCBSIDIwNjUKMjA2NCAxIDEgUiAyMDMwCjIwNjUgMCAwIFIgMjAxOQoyMDY1IDEgMSBSIDIwNjEKMjA2NiAwIDAgUiAyMjEKMjA2NiAxIDAgTCAzMDIK"
PRIMARY_NATIVE_SHA256 = "e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54"
PRIMARY_DENSE_SHA256 = "4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f"
CANDIDATE_NATIVE_SHA256 = "7a83339f95624c0d9b3935f081f226b17461dac6c4660e03a400ce04be8e0a9e"
CANDIDATE_DENSE_SHA256 = "3af42ea9d430e5df22b69e6fc540e3530f87263372580c7c554bae37ba524ac8"
START, HALT = 74, 254
SK = [51,36,25,48,32,33,22,55,60]
OLD_PHYSICAL = [6,2,0,4,3,7,8,5,1]
PHYSICAL = [6,4,0,3,2,8,7,5,1]
BOXSTATES = {0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}
EDITS = {(17,1):(0,"R",48), (21,1):(0,"R",55), (41,1):(0,"R",32),
         (45,1):(0,"R",60), (61,1):(0,"R",32), (144,1):(0,"R",25),
         (161,1):(0,"R",48)}

def require(ok, msg):
    if not ok:
        raise AssertionError(msg)

def digest(text):
    return hashlib.sha256(text.encode("ascii")).hexdigest()

def parse(text):
    rows = {}
    for line in text.splitlines():
        q,b,w,d,n = line.split()
        q,b,w,n = map(int,(q,b,w,n))
        require((q,b) not in rows and b in (0,1) and w in (0,1)
                and d in ("L","R"), "Malformed transition")
        rows[q,b] = (w,d,n)
    return rows

def render(rows):
    return "".join(f"{q} {b} {w} {d} {n}\n"
                   for (q,b),(w,d,n) in sorted(rows.items()))

def dense(rows):
    states = {q for q,b in rows}
    require(len(states)==194 and len(rows)==388, "Wrong state count")
    require(set(rows)=={(q,b) for q in states for b in (0,1)}, "Incomplete table")
    require({n for w,d,n in rows.values()}-states=={HALT}, "Wrong halt")
    order, index = [START], {START:0}
    for q in order:
        for b in (0,1):
            n = rows[q,b][2]
            if n != HALT and n not in index:
                index[n] = len(order)
                order.append(n)
    require(len(order)==194, "Graph-unreachable working state")
    result = {(index[q],b):(w,d,194 if n==HALT else index[n])
              for (q,b),(w,d,n) in rows.items()}
    return result, order+[HALT]

def expected_seed():
    # Frame: left marker, source path100000, zero padding, right marker,
    # nine physical unary registers, then26 one-valued spare registers.
    head, span, path = -2, 48, "100000"
    ones = {head-1, head+span}
    ones.update(head+i for i,b in enumerate(path) if b=="1")
    logical = [2]+[0]*8
    physical = [None]*9
    for r,p in enumerate(PHYSICAL):
        physical[p] = logical[r]
    pos = head+span+1
    for value in physical+[1]*26:
        pos += 1
        ones.update(range(pos,pos+value+1))
        pos += value+1
    return ones, physical

def run_sparse(rows, count, expected):
    q,head,ones = START,0,set()
    visits,first = {},{}
    leftmost=rightmost=0
    for t in range(count):
        key = (q,int(head in ones))
        require(key in rows, f"Premature halt at step{t}")
        if key in EDITS:
            name = f"{key[0]},{key[1]}"
            visits[name] = visits.get(name,0)+1
            first.setdefault(name,t)
        w,d,q = rows[key]
        (ones.add if w else ones.discard)(head)
        head += 1 if d=="R" else -1
        leftmost=min(leftmost,head)
        rightmost=max(rightmost,head)
    require((q,head)==(84,-2) and ones==expected, "Complete seed mismatch")
    return dict(steps=count,state=q,head=head,one_cells=sorted(ones),
                head_interval=[leftmost,rightmost],changed_row_visits=visits,
                changed_row_first_occurrence_zero_based=first)

def run_bytearray(rows, count, expected):
    origin=2048
    tape=bytearray(4096)
    target=bytearray(4096)
    for x in expected:
        target[origin+x]=1
    q,head=START,origin
    for t in range(count):
        require(q!=HALT and 0<=head<len(tape), "Premature halt or boundary")
        w,d,q=rows[q,tape[head]]
        tape[head]=w
        head+=1 if d=="R" else -1
    require((q,head-origin)==(84,-2) and tape==target, "Byte-array seed mismatch")
    return dict(steps=count,state=q,head=head-origin,complete_tape_equality=True)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=Path("pa194_c32_rebuilt"))
    args=parser.parse_args()
    original=base64.b64decode(BASELINE_B64).decode("ascii")
    require(digest(original)==PRIMARY_NATIVE_SHA256,"Embedded baseline corrupt")
    baseline=parse(original)
    primary_dense,_=dense(baseline)
    require(digest(render(primary_dense))==PRIMARY_DENSE_SHA256,"Primary dense hash")
    rows=baseline|EDITS
    # Verify that edits are exactly the prescribed physical allocation.
    selector_map={SK[old]:SK[new] for old,new in zip(OLD_PHYSICAL,PHYSICAL)}
    expected_rows=baseline.copy()
    for (q,b),(w,d,n) in baseline.items():
        if q not in BOXSTATES and n in selector_map:
            require((b,w,d)==(1,0,"R"),"Unexpected selector form")
            expected_rows[q,b]=(w,d,selector_map[n])
    require(rows==expected_rows,"Physical allocation differs from stated edits")
    require(all(rows[q,b]==baseline[q,b] for q in BOXSTATES for b in (0,1)),
            "Arithmetic-block row changed")
    den,labels=dense(rows)
    native_text,dense_text=render(rows),render(den)
    require(digest(native_text)==CANDIDATE_NATIVE_SHA256,"Candidate native hash")
    require(digest(dense_text)==CANDIDATE_DENSE_SHA256,"Candidate dense hash")
    expected,physical=expected_seed()
    primary_boot=run_sparse(baseline,58154,expected)
    candidate_boot=run_sparse(rows,56250,expected)
    independent=run_bytearray(rows,56250,expected)
    require(all(candidate_boot["changed_row_visits"].get(f"{q},{b}",0)>0
                for q,b in EDITS),"An edit was not exercised")
    receipt=dict(name="PA194C32",working_states=194,transition_rows=388,
        native_sha256=CANDIDATE_NATIVE_SHA256,dense_sha256=CANDIDATE_DENSE_SHA256,
        physical_map=PHYSICAL,physical_registers=physical,source_site=25,
        source_path="100000",header_distance=48,spare_values=[1]*26,
        edits=[dict(read=[q,b],old=baseline[q,b],new=rows[q,b])
               for q,b in sorted(EDITS)],
        primary_startup=primary_boot,candidate_startup=candidate_boot,
        independent_bytearray=independent,arithmetic_box_rows_unchanged=True,
        proof_scope="Literal reconstruction and exact complete-tape startup; no end-to-end iPRA consistency theorem.")
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/"pa194_c32.native.tm").write_text(native_text)
    (args.output/"pa194_c32.tm").write_text(dense_text)
    (args.output/"pa194_c32.labels.json").write_text(json.dumps(labels)+"\n")
    (args.output/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps(receipt,indent=2))

if __name__=="__main__":
    main()
