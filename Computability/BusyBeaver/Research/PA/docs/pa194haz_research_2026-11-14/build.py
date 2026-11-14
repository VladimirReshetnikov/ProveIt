#!/usr/bin/env python3
"""Reconstruct PA194HA and PA194HAZ from frozen PA194 inputs.
Python 3.10+, standard library; assertions must be enabled.
The checker inherits arithmetic-block contracts; it is not a proof kernel.
"""
from pathlib import Path
import argparse, hashlib, json, sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "vendor"))
import compiler as c

START, HALT = 74, 254
PRIMARY_SHA = "e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54"
EXPECTED = {
    "pa194ha": {
        "native": "503e27b6b619eb04d567d94e47b3bfe667eb457bb921eab3efc4d5d4771036bc",
        "dense": "dd8b4b0a6419dde553bf840175c5e682b7b1f574f5c152278fb6dfbf2916d7e3",
        "contracts": 4750, "iterations": 1472170},
    "pa194haz": {
        "native": "5ffbc263413612caa71b85895a92860797d90f5c77315119134b6e30fd566f09",
        "dense": "f9f98218e2f949b28f0429f2bbab17babe0f4948c2e38cb786a5e3b239101981",
        "contracts": 4751, "iterations": 1472644}}
AD_PATCHES = [
    (17, 1, (0, True, 32), (0, True, 48)),
    (144, 1, (0, True, 48), (0, True, 32)),
    (161, 1, (0, True, 32), (0, True, 48))]
H_PATCH = (164, 1, (1, True, 98), (1, True, 130))
Z_PATCH = (2066, 1, (0, False, 302), (1, True, 21))

def sha(data):
    return hashlib.sha256(data).hexdigest()

def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(text.encode("utf-8"))

def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        q, bit, w, move, n = line.split()
        q, bit, w, n = map(int, (q, bit, w, n))
        assert (q, bit) not in rows
        assert bit in (0, 1) and w in (0, 1) and move in ("L", "R")
        rows[q, bit] = w, move == "R", n
    return rows

def table_text(rows):
    return "".join(f"{q} {b} {w} {'R' if d else 'L'} {n}\n"
                   for (q,b),(w,d,n) in sorted(rows.items()))

def patch(rows, edits):
    out = dict(rows)
    for q, b, before, after in edits:
        assert out[q,b] == before, (q,b,out[q,b],before)
        out[q,b] = after
    return out

def dense_table(rows):
    controls = {q for q,b in rows}
    assert len(controls) == 194 and len(rows) == 388
    assert all((q,b) in rows for q in controls for b in (0,1))
    assert {n for w,d,n in rows.values()} - controls == {HALT}
    order, index = [START], {START:0}
    for q in order:
        for bit in (0,1):
            target = rows[q,bit][2]
            if target != HALT and target not in index:
                index[target] = len(order)
                order.append(target)
    assert len(order) == 194
    dense = {(index[q],bit):(w,d,194 if n == HALT else index[n])
             for (q,bit),(w,d,n) in rows.items()}
    return dense, order + [HALT]

def startup(rows, path):
    head0 = -2
    physical = [0,0,0,0,0,0,2,0,0] + [1]*26
    expected = {head0-1,head0+48}
    expected.update(head0+i for i,b in enumerate(path) if b)
    pos = head0+49
    for value in physical:
        pos += 1
        expected.update(range(pos,pos+value+1))
        pos += value+1
    state, head, ones = START, 0, set()
    for step in range(1,100001):
        w,d,state = rows[state,int(head in ones)]
        (ones.add if w else ones.discard)(head)
        head += 1 if d else -1
        assert state != HALT
        if (state,head,ones) == (84,head0,expected):
            return dict(steps=step,state=state,head=head,
                        physical_file=physical,one_cells=sorted(ones),
                        complete_tape_equality=True)
    raise AssertionError("Expected complete startup frame not reached")

def final_zero_grammar(tree):
    count = 0
    def rec(t):
        nonlocal count
        if t == ("node150", ("leaf","breakTo",1)):
            count += 1
            return ("node150", ("leaf","dec",6))
        if isinstance(t,tuple) and len(t) == 2:
            return rec(t[0]),rec(t[1])
        return t
    result = rec(tree)
    assert count == 1
    return result

def zero_cut(old, new):
    differences = [(i,list(a),list(b)) for i,(a,b) in enumerate(zip(old,new)) if a != b]
    assert len(old) == len(new) == 3650
    assert differences == [(3553,["jump",3637],["dec",6,3637,3554])]
    zone = {3550,3551,3552,3553}
    expected_inside = {
        3550:("jump",3553),3551:("dec",1,3553,3552),
        3552:("jump",3551),3553:("dec",6,3637,3554)}
    assert all(new[i] == ins for i,ins in expected_inside.items())
    entries = []
    for i,ins in enumerate(new):
        if i in zone:
            continue
        if ins[0] == "inc":
            successors = [(ins[2],"ordinary")]
        elif ins[0] == "jump":
            successors = [(ins[1],"ordinary")]
        elif ins[0] == "dec":
            successors = [(ins[2],"zero"),(ins[3],"positive")]
        else:
            successors = []
        for n,branch in successors:
            if n in zone:
                entries.append((i,n,branch,list(ins)))
    assert entries == [
        (3545,3551,"zero",["dec",6,3551,3546]),
        (3548,3550,"zero",["dec",6,3550,3549])]
    return dict(zone=sorted(zone),differences=differences,entries=entries,
                initial_pc=25,initial_pc_outside_zone=True)

def emit(name,rows,source_data,output,primary):
    sites,instructions,contracts = source_data
    assert len(sites) == 3650
    result = c.validate(rows,contracts)
    expected = EXPECTED[name]
    assert result == dict(ok=True,contracts=expected["contracts"],
                          max_steps=497,total_steps=expected["iterations"])
    assert all(rows[q,b] == primary[q,b] for q in c.BOXSTATES for b in (0,1))
    blank = startup(rows,sites[25][0])
    assert blank["steps"] == 58122
    dense,labels = dense_table(rows)
    native_text,dense_text = table_text(rows),table_text(dense)
    assert sha(native_text.encode()) == expected["native"]
    assert sha(dense_text.encode()) == expected["dense"]
    edits = AD_PATCHES + [H_PATCH] + ([Z_PATCH] if name == "pa194haz" else [])
    receipt = dict(name=name.upper(),working_states=194,transition_rows=388,
        graph_reachable_working_states=194,native_start=START,native_halt=HALT,
        dense_start=0,dense_halt=194,source_sites=len(sites),
        source_outcomes=len(contracts),native_sha256=expected["native"],
        dense_sha256=expected["dense"],symbolic_verification=result,startup=blank,
        physical_register_map=list(c.PHYSICAL),
        changed_rows=[dict(state=q,read=b,
           old=[ow,"R" if od else "L",on],new=[nw,"R" if nd else "L",nn])
           for q,b,(ow,od,on),(nw,nd,nn) in edits],
        kernel_checked=False,
        proof_scope="Ordinary protocol and zero-cut proofs; inherited arithmetic blocks and numerical-calculus PA calibration")
    write(output/(name+".native.tm"),native_text)
    write(output/(name+".tm"),dense_text)
    write(output/(name+".labels.json"),json.dumps(labels)+"\n")
    write(output/(name+".instructions.json"),json.dumps(instructions,indent=2)+"\n")
    write(output/(name+".sites.json"),json.dumps(
        [["".join(map(str,p)),op,arg] for p,op,arg in sites])+"\n")
    write(output/(name+".verification.json"),json.dumps(receipt,indent=2)+"\n")
    if name == "pa194haz":
        table = [r"\begin{longtable}{rll}",
                 r"\toprule State & Read 0 & Read 1\\\midrule\endhead"]
        for q in range(194):
            actions = [r"\texttt{%d%s%d}" % (w,"R" if d else "L",n)
                       for w,d,n in (dense[q,0],dense[q,1])]
            table.append(f"{q} & {actions[0]} & {actions[1]}"+r"\\")
        table += [r"\bottomrule",r"\end{longtable}"]
        write(HERE/"report/transition_table.tex","\n".join(table)+"\n")
    return receipt

def main(output):
    if not __debug__ or sys.flags.optimize:
        raise SystemExit("Run without -O or PYTHONOPTIMIZE")
    path = HERE/"inputs/pa194.native.tm"
    assert sha(path.read_bytes()) == PRIMARY_SHA
    primary = read_table(path)
    grammar = c.read_grammar(HERE/"inputs/pa194.grammar.json")
    base = c.source(grammar)
    assert len(base[0]) == 3673
    assert c.validate(primary,base[2]) == dict(
        ok=True,contracts=4780,max_steps=497,total_steps=1479348)
    ad = patch(primary,AD_PATCHES)
    assert c.PHYSICAL == [6,2,0,4,3,7,8,5,1]
    c.PHYSICAL[:] = [6,2,0,3,4,7,8,5,1]
    ad_source = c.source(grammar)
    assert c.validate(ad,ad_source[2]) == dict(
        ok=True,contracts=4780,max_steps=497,total_steps=1479348)
    original_nodes = c.raw_nodes
    def hybrid_nodes():
        nodes = original_nodes()
        assert nodes["node163"] == ("node6","node55")
        nodes["node163"] = "node6","node147"
        return nodes
    c.raw_nodes = hybrid_nodes
    ha_rows = patch(ad,[H_PATCH])
    ha_source = c.source(grammar)
    haz_rows = patch(ha_rows,[Z_PATCH])
    haz_source = c.source(final_zero_grammar(grammar))
    cut = zero_cut(ha_source[1],haz_source[1])
    write(HERE/"verification/zero_cut.json",json.dumps(cut,indent=2)+"\n")
    output.mkdir(parents=True,exist_ok=True)
    results = [emit("pa194ha",ha_rows,ha_source,output,primary),
               emit("pa194haz",haz_rows,haz_source,output,primary)]
    write(HERE/"verification/python_results.json",json.dumps(results,indent=2)+"\n")
    print(json.dumps([{k:r[k] for k in (
        "name","working_states","source_sites","source_outcomes",
        "native_sha256","dense_sha256","symbolic_verification")}
        | {"startup_steps":r["startup"]["steps"]} for r in results],indent=2))

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=HERE/"machine")
    main(parser.parse_args().output)
