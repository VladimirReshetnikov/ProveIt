#!/usr/bin/env python3
"""Offline reconstruction and exact startup verification of PA194AX11HC4.

Python 3.10+, standard library only. No network or repository checkout needed.
The embedded baseline is the PA194AX11H native table pinned in ProveIt
2ca99e3d23a5397aae4c786f4da7dfe1cca87f85, reconstructed from the pinned dense table and label map.
This checks literal tables, physical allocation, and complete blank startup.
Universal source verification is documented separately; this script does not
prove the unfinished iPRA-to-Con(PA) calibration.
"""
from pathlib import Path
import argparse, base64, hashlib, json

BASELINE_B64 = "MCAwIDEgUiA5NAowIDEgMSBSIDAKMSAwIDAgTCAxCjEgMSAxIEwgMgoyIDAgMCBMIDMKMiAxIDEgTCAyCjMgMCAwIEwgNQozIDEgMSBMIDIKNCAwIDEgUiA2CjQgMSAwIEwgNAo1IDAgMCBMIDkKNSAxIDEgTCAyCjYgMCAwIFIgNgo2IDEgMCBSIDEwCjggMCAwIFIgMTQKOCAxIDEgUiAxMwo5IDAgMCBMIDE1CjkgMSAxIEwgMgoxMCAwIDAgTCAxNgoxMCAxIDAgUiAxMAoxMSAwIDAgTCAyNgoxMSAxIDEgUiAxOAoxMiAwIDAgUiAxOQoxMiAxIDEgUiAyMAoxMyAwIDAgTCA5MQoxMyAxIDEgTCAzMQoxNCAwIDAgTCAxMQoxNCAxIDAgUiAyMgoxNSAwIDAgTCAyMwoxNSAxIDEgTCAyCjE2IDAgMSBMIDEKMTYgMSAwIEwgMQoxNyAwIDAgUiAyNAoxNyAxIDAgUiAzMgoxOCAwIDAgUiA5NgoxOCAxIDAgTCAxMDgKMTkgMCAwIFIgMjgKMTkgMSAxIFIgMjkKMjAgMCAwIFIgMzAKMjAgMSAxIFIgMzEKMjEgMCAwIFIgMjQKMjEgMSAwIFIgNjAKMjIgMCAwIFIgMzMKMjIgMSAxIFIgMjIKMjMgMCAwIEwgMzQKMjMgMSAxIEwgMgoyNCAwIDAgTCAzNQoyNCAxIDAgUiAwCjI1IDAgMCBSIDM2CjI1IDEgMSBSIDI1CjI2IDAgMCBSIDE5NAoyNiAxIDEgUiA0MgoyNyAwIDAgUiAzOQoyNyAxIDAgTCA0MAoyOCAwIDAgUiA0MQoyOCAxIDEgUiA0MgoyOSAwIDAgUiA0MwoyOSAxIDEgUiA0NAozMCAwIDAgUiA0NQozMCAxIDEgUiA0NgozMSAwIDAgUiAyMQozMSAxIDEgUiA0NwozMiAwIDAgUiA0OAozMiAxIDEgUiAzMgozMyAwIDAgUiAzMgozMyAxIDEgUiAzMwozNCAwIDAgTCA3NQozNCAxIDEgTCAyCjM1IDAgMSBSIDM1CjM1IDEgMSBMIDEKMzYgMCAwIFIgNTEKMzYgMSAxIFIgMzYKMzggMCAwIFIgMTEKMzggMSAxIFIgMTIyCjM5IDAgMCBMIDExCjM5IDEgMCBSIDM2CjQwIDAgMCBMIDQKNDAgMSAxIEwgNTQKNDEgMCAwIFIgMjQKNDEgMSAwIFIgMjUKNDIgMCAwIFIgMTMKNDIgMSAwIEwgMTYKNDMgMCAwIFIgNTYKNDMgMSAxIFIgNTcKNDQgMCAwIFIgNTgKNDQgMSAxIFIgNTkKNDUgMCAwIFIgMjQKNDUgMSAwIFIgNTUKNDYgMCAwIFIgNjEKNDYgMSAxIFIgNjIKNDcgMCAwIFIgNjMKNDcgMSAwIEwgMTYKNDggMCAwIFIgMjUKNDggMSAxIFIgNDgKNDkgMCAwIEwgMzUKNDkgMSAwIFIgNjQKNTEgMCAwIFIgMTYKNTEgMSAxIFIgNTEKNTMgMCAwIFIgNjgKNTMgMSAxIFIgNjkKNTQgMCAwIEwgNDAKNTQgMSAxIEwgNTQKNTUgMCAwIFIgMjIKNTUgMSAxIFIgNTUKNTYgMCAwIEwgMTEKNTYgMSAwIFIgNTEKNTcgMCAwIFIgNjEKNTcgMSAwIEwgMTYKNTggMCAwIFIgNzAKNTggMSAxIFIgNzEKNTkgMCAwIFIgNjIKNTkgMSAxIFIgNzIKNjAgMCAwIFIgNTUKNjAgMSAxIFIgNjAKNjEgMCAwIFIgNDkKNjEgMSAwIFIgMjUKNjIgMCAwIEwgMjgKNjIgMSAxIEwgNzMKNjMgMCAwIEwgMTIzCjYzIDEgMSBMIDMwCjY0IDAgMCBSIDc0CjY0IDEgMSBSIDY0CjY2IDAgMSBSIDE5OAo2NiAxIDEgTCA1NAo2OCAwIDAgUiA3Nwo2OCAxIDEgUiAyNTQKNjkgMCAwIEwgMjEzCjY5IDEgMSBSIDMxCjcwIDAgMCBSIDQxCjcwIDEgMSBSIDYzCjcxIDAgMCBMIDkxCjcxIDEgMSBSIDgwCjcyIDAgMCBSIDU2CjcyIDEgMSBMIDgxCjczIDAgMCBSIDgyCjczIDEgMSBSIDgzCjc0IDAgMSBSIDAKNzQgMSAxIFIgNjQKNzUgMCAwIFIgNzUKNzUgMSAxIFIgODQKNzcgMCAwIFIgODcKNzcgMSAxIFIgODgKODAgMCAwIFIgOTEKODAgMSAxIEwgMTM4CjgxIDAgMCBMIDExMQo4MSAxIDEgUiA1Nwo4MiAwIDAgUiA0OQo4MiAxIDAgUiAzMwo4MyAwIDAgUiA5Mwo4MyAxIDAgTCA0Mgo4NCAwIDAgUiA1Mwo4NCAxIDEgUiAzMTAKODcgMCAwIFIgMzAxCjg3IDEgMSBSIDIxCjg4IDAgMCBSIDEyMgo4OCAxIDEgUiAxMDMKOTAgMCAwIFIgMTA1CjkwIDEgMSBSIDEwNgo5MSAwIDAgUiA4Mgo5MSAxIDEgUiA4MQo5MiAwIDAgUiAxMDQKOTIgMSAxIFIgMTg1CjkzIDAgMCBSIDEwOAo5MyAxIDEgUiAxMDkKOTQgMCAwIFIgNjYKOTQgMSAwIFIgMAo5NSAwIDAgUiAyNwo5NSAxIDEgUiAxMTAKOTYgMCAwIFIgMTAxCjk2IDEgMSBSIDEwMAo5NyAwIDEgTCAxMTMKOTcgMSAxIEwgOTcKOTggMCAwIFIgMTkKOTggMSAxIFIgMTE0Cjk5IDAgMCBSIDYxCjk5IDEgMSBSIDYxCjEwMCAwIDAgUiAxNzQKMTAwIDEgMSBSIDE2NAoxMDEgMCAwIEwgMjYKMTAxIDEgMSBSIDIwMDAKMTAzIDAgMCBSIDEwOAoxMDMgMSAwIEwgMzAyCjEwNCAwIDAgUiAxMjMKMTA0IDEgMSBSIDEyNAoxMDUgMCAwIFIgNzIKMTA1IDEgMSBSIDU5CjEwNiAwIDAgUiA1OAoxMDYgMSAxIFIgMTI1CjEwNyAwIDAgUiAyMQoxMDcgMSAxIFIgMTI2CjEwOCAwIDAgUiAyMQoxMDggMSAwIEwgMTAKMTA5IDAgMCBSIDYyCjEwOSAxIDEgUiA0MgoxMTAgMCAwIFIgMTI3CjExMCAxIDEgUiA4CjExMSAwIDAgUiAxMDQKMTExIDEgMSBSIDEyOAoxMTMgMCAwIEwgMzAyCjExMyAxIDAgTCA5NwoxMTQgMCAwIFIgMTMwCjExNCAxIDEgUiAxMDcKMTIyIDAgMCBMIDEzNwoxMjIgMSAwIEwgMQoxMjMgMCAwIFIgMzkKMTIzIDEgMSBSIDczCjEyNCAwIDAgUiA2MgoxMjQgMSAxIFIgMTM4CjEyNSAwIDAgUiA2MgoxMjUgMSAxIFIgMTM5CjEyNiAwIDAgUiA3MQoxMjYgMSAwIEwgMTYKMTI3IDAgMCBSIDE0CjEyNyAxIDEgUiAxMzgKMTI4IDAgMCBSIDIxCjEyOCAxIDEgUiAxNDEKMTMwIDAgMCBSIDE0NAoxMzAgMSAxIEwgMjAKMTM3IDAgMCBSIDMwCjEzNyAxIDEgUiA3MAoxMzggMCAwIFIgMzkKMTM4IDEgMSBMIDEzMAoxMzkgMCAwIFIgMTkwCjEzOSAxIDAgTCAxNgoxNDEgMCAwIFIgMTYxCjE0MSAxIDAgTCAxNgoxNDQgMCAwIFIgMjQKMTQ0IDEgMCBSIDQ4CjE2MSAwIDAgUiA0OQoxNjEgMSAwIFIgMzIKMTY0IDAgMCBSIDc3CjE2NCAxIDEgUiAxMTQKMTY2IDAgMCBSIDE5CjE2NiAxIDEgUiAxNzkKMTc0IDAgMCBSIDIxMwoxNzQgMSAxIFIgMjgKMTc5IDAgMCBSIDE5NAoxNzkgMSAxIFIgMTI4CjE4NSAwIDAgUiAxMDcKMTg1IDEgMSBSIDk4CjE4OCAwIDAgUiA5NQoxODggMSAxIFIgMTExCjE5MCAwIDAgUiA5OQoxOTAgMSAxIFIgOTkKMTk0IDAgMCBSIDE3CjE5NCAxIDEgTCAxMzcKMTk2IDAgMCBSIDc3CjE5NiAxIDEgUiAxMjIKMTk3IDAgMCBSIDEwOQoxOTcgMSAxIFIgMTMwCjE5OCAwIDEgTCA0MAoxOTggMSAxIEwgMTEzCjIxMyAwIDAgUiA5MgoyMTMgMSAxIFIgOTAKMjE0IDAgMCBSIDMxMgoyMTQgMSAxIFIgMjAKMjE3IDAgMCBSIDE5NwoyMTcgMSAxIFIgMTk2CjIyMSAwIDAgUiAxOTYKMjIxIDEgMSBSIDIxNwozMDEgMCAwIFIgNDUKMzAxIDEgMSBSIDEwMwozMDIgMCAwIEwgNAozMDIgMSAwIEwgMzAyCjMxMCAwIDAgUiAyMTQKMzEwIDEgMSBSIDYyCjMxMiAwIDAgUiAxODgKMzEyIDEgMSBSIDM4CjIwMDAgMCAwIFIgMjAwMQoyMDAwIDEgMSBSIDIwMzMKMjAwMSAwIDAgUiAyMDAyCjIwMDEgMSAxIFIgMjAwNQoyMDAyIDAgMCBSIDEyCjIwMDIgMSAxIFIgMjAwMwoyMDAzIDAgMCBSIDIwMDQKMjAwMyAxIDEgUiA5OQoyMDA0IDAgMCBSIDk4CjIwMDQgMSAxIFIgOTAKMjAwNSAwIDAgUiAyMDA2CjIwMDUgMSAxIFIgMjAyMwoyMDA2IDAgMCBSIDIwMDcKMjAwNiAxIDEgUiAyMDE0CjIwMDcgMCAwIFIgNjkKMjAwNyAxIDEgUiAyMDA4CjIwMDggMCAwIFIgMjAwOQoyMDA4IDEgMSBSIDIwMTkKMjAwOSAwIDAgUiAyMDEwCjIwMDkgMSAxIFIgMjAxMQoyMDEwIDAgMCBSIDEyCjIwMTAgMSAxIFIgMjAwNAoyMDExIDAgMCBSIDIxMwoyMDExIDEgMSBSIDIwMTIKMjAxMiAwIDAgUiAyMDEzCjIwMTIgMSAxIFIgMjAxNQoyMDEzIDAgMCBSIDk4CjIwMTMgMSAxIFIgMjAxNAoyMDE0IDAgMCBMIDIwNTAKMjAxNCAxIDEgTCAyMDY0CjIwMTUgMCAwIEwgMjA0NAoyMDE1IDEgMSBSIDIwMTcKMjAxNyAwIDAgUiAyMDI3CjIwMTcgMSAxIFIgMjAwMgoyMDE5IDAgMCBMIDIwNTkKMjAxOSAxIDEgTCAyMDU2CjIwMjAgMCAwIFIgMjAyMQoyMDIwIDEgMSBSIDIwMDMKMjAyMSAwIDAgUiAyMDMyCjIwMjEgMSAxIFIgOTAKMjAyMyAwIDAgUiAyMDQ2CjIwMjMgMSAxIFIgMjAyOQoyMDI1IDAgMCBSIDEyCjIwMjUgMSAxIFIgMjAyNgoyMDI2IDAgMCBSIDE2NgoyMDI2IDEgMSBSIDIwMjcKMjAyNyAwIDAgUiA5MAoyMDI3IDEgMSBMIDIwMjAKMjAyOCAwIDAgUiAyMDAzCjIwMjggMSAxIFIgMjAwMgoyMDI5IDAgMCBSIDIwMzAKMjAyOSAxIDEgUiAyMDMxCjIwMzAgMCAwIFIgMjAyNgoyMDMwIDEgMSBSIDkwCjIwMzEgMCAwIFIgMTIKMjAzMSAxIDEgUiAyMDMyCjIwMzIgMCAwIEwgMjAwMgoyMDMyIDEgMSBSIDYxCjIwMzMgMCAwIFIgMjAzNAoyMDMzIDEgMSBSIDIwMzkKMjAzNCAwIDAgUiAyMDI1CjIwMzQgMSAxIFIgMjAzNQoyMDM1IDAgMCBSIDYxCjIwMzUgMSAxIFIgMjAzNgoyMDM2IDAgMCBSIDIwMTUKMjAzNiAxIDEgUiA2MQoyMDM4IDAgMCBSIDE2NgoyMDM4IDEgMSBSIDIwMzIKMjAzOSAwIDAgUiAyMDUyCjIwMzkgMSAxIFIgMjA0MAoyMDQwIDAgMCBSIDIwNDEKMjA0MCAxIDEgUiAyMDY2CjIwNDEgMCAwIFIgMjA0MgoyMDQxIDEgMSBSIDIwNDcKMjA0MiAwIDAgUiAyMDQzCjIwNDIgMSAxIFIgMjA0NAoyMDQzIDAgMCBSIDIwMzUKMjA0MyAxIDEgUiAyMDE5CjIwNDQgMCAwIFIgMjA0NQoyMDQ0IDEgMSBSIDIwNDYKMjA0NSAwIDAgUiAyMDM4CjIwNDUgMSAxIFIgNjEKMjA0NiAwIDAgTCAyMDMzCjIwNDYgMSAxIFIgMjAyOAoyMDQ3IDAgMCBSIDIwNDgKMjA0NyAxIDEgUiAyMDUzCjIwNDggMCAwIFIgMjAyNwoyMDQ4IDEgMSBSIDIwNDkKMjA0OSAwIDAgUiAyMDUwCjIwNDkgMSAxIFIgMjAyOQoyMDUwIDAgMCBSIDIwNTEKMjA1MCAxIDEgUiAyMDMxCjIwNTEgMCAwIFIgMTY2CjIwNTEgMSAxIFIgMjA1MgoyMDUyIDAgMCBSIDE2NgoyMDUyIDEgMSBMIDIwMDUKMjA1MyAwIDAgUiAyMDU0CjIwNTMgMSAxIFIgMTk0CjIwNTQgMCAwIFIgMjAxOQoyMDU0IDEgMSBSIDIwNTYKMjA1NiAwIDAgUiAyMDU3CjIwNTYgMSAxIFIgMjA1OAoyMDU3IDAgMCBSIDIwMjcKMjA1NyAxIDEgUiAyMDM4CjIwNTggMCAwIFIgMjA1OQoyMDU4IDEgMSBSIDIwMjEKMjA1OSAwIDAgUiAyMDE0CjIwNTkgMSAxIFIgMjA2MwoyMDYxIDAgMCBSIDkwCjIwNjEgMSAxIFIgMjA2MgoyMDYyIDAgMCBSIDIwMjEKMjA2MiAxIDEgUiA5MAoyMDYzIDAgMCBSIDIwMjAKMjA2MyAxIDEgUiAyMDY0CjIwNjQgMCAwIFIgMjA2NQoyMDY0IDEgMSBSIDIwMzAKMjA2NSAwIDAgUiAyMDE5CjIwNjUgMSAxIFIgMjA2MQoyMDY2IDAgMCBSIDIyMQoyMDY2IDEgMSBSIDE5Cg=="
PRIMARY_NATIVE_SHA256 = "6022711dcc0a025eb4b7a5a8f690d6b52f45f3d963a0868afef10962ccc49bd3"
PRIMARY_DENSE_SHA256 = "c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a"
CANDIDATE_NATIVE_SHA256 = "8081a0ef2c2054963d3153f2a4ad385a381a9d7abe7c0301e0c98e830b2433e1"
CANDIDATE_DENSE_SHA256 = "fe4253a42045c330a499d99cc33d55a14e116cae910eb624c499161a7a7ca755"
START, HALT = 74, 254
SK = [51,36,25,48,32,33,22,55,60]
OLD_PHYSICAL = [6,2,0,4,3,7,8,5,1]
PHYSICAL = [6,4,0,3,5,7,8,2,1]
BOXSTATES = {0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}
EDITS = {(17,1):(0,"R",48), (41,1):(0,"R",32), (61,1):(0,"R",32),
         (82,1):(0,"R",25), (144,1):(0,"R",33), (161,1):(0,"R",48)}

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
    # Frame: left marker, source path1000000, zero padding, right marker,
    # nine physical unary registers, then26 one-valued spare registers.
    head, span, path = -2, 48, "1000000"
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
    parser.add_argument("--output",type=Path,default=Path("pa194_ax11hc4_rebuilt"))
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
    primary_boot=run_sparse(baseline,57922,expected)
    candidate_boot=run_sparse(rows,57406,expected)
    independent=run_bytearray(rows,57406,expected)
    require(all(candidate_boot["changed_row_visits"].get(f"{q},{b}",0)>0
                for q,b in EDITS),"An edit was not exercised")
    receipt=dict(name="PA194AX11HC4",working_states=194,transition_rows=388,
        native_sha256=CANDIDATE_NATIVE_SHA256,dense_sha256=CANDIDATE_DENSE_SHA256,
        physical_map=PHYSICAL,physical_registers=physical,source_site=25,
        source_path="1000000",header_distance=48,spare_values=[1]*26,
        edits=[dict(read=[q,b],old=baseline[q,b],new=rows[q,b])
               for q,b in sorted(EDITS)],
        primary_startup=primary_boot,candidate_startup=candidate_boot,
        independent_bytearray=independent,arithmetic_box_rows_unchanged=True,
        proof_scope="Literal reconstruction and exact complete-tape startup; no end-to-end iPRA consistency theorem.")
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/"pa194_ax11hc4.native.tm").write_text(native_text)
    (args.output/"pa194_ax11hc4.tm").write_text(dense_text)
    (args.output/"pa194_ax11hc4.labels.json").write_text(json.dumps(labels)+"\n")
    (args.output/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps(receipt,indent=2))

if __name__=="__main__":
    main()
