#!/usr/bin/env python3
"""Independent finite audit of the complete invariant and step simulation.

Every five-cell word consistent with I is checked at every old control.
No run is allowed to read outside the represented cells.  The local identity
therefore holds with arbitrary exterior tapes, and the written proof extends
these finite premises to all time by induction.
"""
from pathlib import Path
from itertools import product
from hashlib import sha256
import argparse
import json

ROOT = Path(__file__).resolve().parents[1]
EXPECTED_OLD = '4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
EXPECTED_NEW = 'c8ef2f44d25fee6813164cc59ec05061799397da8cf7f0ea7baab63d32d76e02'
GUARDED = {15,18,47,65}

def parse(path):
    start = None
    table = {}
    for line in path.read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '):
            assert start is None
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            fields = line.split()
            assert len(fields) == 5
            q,b,w = map(int, fields[:3])
            direction,target = fields[3],int(fields[4])
            assert b in (0,1) and w in (0,1) and direction in ('L','R')
            assert (q,b) not in table
            table[q,b] = (w,1 if direction=='R' else -1,target)
    controls = {q for q,b in table}
    assert set(table) == {(q,b) for q in controls for b in (0,1)}
    assert {t for w,d,t in table.values()}-controls == {254}
    assert start == 95
    return table

def invariant(q,h,tape):
    return (q not in GUARDED or tape[h-1] == 0) and (q != 27 or tape[h] == 0)

def image(q):
    return 15 if q == 27 else q

def literal(table,q,h,tape,count):
    tape = tape.copy()
    trace = []
    for _ in range(count):
        assert q != 254
        assert h in tape, ('exterior_read',q,h)
        b = tape[h]
        w,d,q1 = table[q,b]
        trace.append([q,b,w,d,q1,h])
        tape[h] = w
        h += d
        q = q1
    return q,h,tape,trace

def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,default=ROOT/'evidence/induction-audit.json')
    args = ap.parse_args()
    old_path = ROOT/'reference/combined243/zfc_combined243_old.tm'
    new_path = ROOT/'machine/zfc_return_fold242_old.tm'
    assert sha256(old_path.read_bytes()).hexdigest() == EXPECTED_OLD
    assert sha256(new_path.read_bytes()).hexdigest() == EXPECTED_NEW
    old,new = parse(old_path),parse(new_path)
    assert len(old) == 486 and len(new) == 484
    assert set(old)-set(new) == {(27,0),(27,1)}
    assert not any(t == 27 for w,d,t in new.values())
    assert image(95) == 95 and 95 not in GUARDED
    incoming = {q:[(s,b,w,d) for (s,b),(w,d,t) in old.items() if t==q]
                for q in sorted(GUARDED)}
    assert sum(map(len,incoming.values())) == 8
    assert all(w==0 and d==1 for entries in incoming.values() for s,b,w,d in entries)
    callers = sorted((s,b,w,d) for (s,b),(w,d,t) in old.items() if t==27)
    assert callers == [(18,0,0,-1),(47,0,0,-1),(65,0,0,-1)]
    ordinary_rows = []
    for (q,b),(w,d,t) in sorted(old.items()):
        if (q,b) in ((15,0),(27,1)):
            continue
        assert new[image(q),b] == (w,d,image(t))
        ordinary_rows.append((q,b))
    assert len(ordinary_rows) == 484
    checks = 0
    exceptional = 0
    rows = set()
    for q in sorted({q for q,b in old}):
        for bits in product((0,1),repeat=5):
            tape = dict(zip(range(-2,3),bits))
            if not invariant(q,0,tape):
                continue
            b = tape[0]
            oq,oh,ot,otrace = literal(old,q,0,tape,1)
            assert invariant(oq,oh,ot), ('invariant_failure',q,b,tape)
            count = 3 if (q,b)==(15,0) else 1
            nq,nh,nt,ntrace = literal(new,image(q),0,tape,count)
            assert (nq,nh,nt) == (image(oq),oh,ot), ('simulation_failure',q,b,tape)
            assert (nq==254) == (oq==254)
            checks += 1
            exceptional += count==3
            rows.add((q,b))
    assert set(old)-rows == {(27,1)}
    assert checks == 7696 and exceptional == 8
    report = {'status':'PASS_ALL_FINITE_PREMISES_OF_INDUCTION',
              'old_sha256':EXPECTED_OLD,'new_sha256':EXPECTED_NEW,
              'old_working_states':243,'new_working_states':242,
              'invariant_left_zero_states':sorted(GUARDED),
              'invariant_current_zero_state':27,'incoming_edges':incoming,
              'incoming_deleted_state':callers,
              'renamed_one_step_rows':len(ordinary_rows),
              'exceptional_old_row':[15,0],'exceptional_new_steps':3,
              'excluded_old_row':[27,1],'local_word_offsets':list(range(-2,3)),
              'admissible_control_word_cases':checks,
              'exceptional_control_word_cases':exceptional,
              'unprovided_exterior_reads':0,'whole_tape_endpoints_equal':True,
              'old_invariant_preserved':True,'halt_correspondence':True,
              'time_map':'theta(n) = n + 2 * visits_old(15,0,before n)',
              'clock_bounds':'n <= theta(n) <= 3*n',
              'scope':'Finite exhaustive premise audit; universal theorem follows by the explicit ordinary induction in the report. No proof-assistant claim.'}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
