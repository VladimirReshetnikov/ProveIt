#!/usr/bin/env python3
"""Rebuild the exact K226 machine and verify its local machine identities.

Python3.10+, standard library only; keep verify_state_fold.py and
check_fold79_independent.py beside this file. Run without -O or -OO.

Usage:
 python3 -B build_machine226.py --k230 inputs/k230.tm \
   --source-certificate source/source_rotations.json --output-dir generated

The source-tree replay, unbounded register runtime, exact blank startup, and
inherited K230 logical theorem are separate obligations. The output explicitly
distinguishes unconditional local identities from the conditional140 fold.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import verify_state_fold as v
import check_fold79_independent as independent79

K230_SHA256 = 'e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8'
K226_SHA256 = '0d6740bbc94a92c9696ed92732b1828bec89109f8ebb6859bbb9197e2076ec89'
SOURCE_SHA256 = '31aaece78d025fbc262e742411e75e24eef9435fe196c67e65b995e8b833fe61'
ROTATIONS = [(85,65,'left'),(202,201,'right'),(174,119,'left'),
             (148,154,'left'),(52,67,'right'),(67,229,'right'),
             (210,174,'right'),(174,101,'right'),(226,224,'right'),
             (205,134,'left'),(207,205,'right'),(101,209,'left'),
             (101,208,'left')]

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def encode(t, start=0):
    return (f'#! start {start}\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {z}\n'
        for (q,b),(w,d,z) in sorted(t.items()))).encode()

def read_k230(raw):
    # Normalize only terminal230 to254 for the inherited open-tape checker.
    t = {}
    start = None
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            require(start is None, 'Repeated start')
            start = int(line[9:])
        elif line and not line.startswith('#'):
            q,b,w,d,z = line.split()
            q,b,w,z = map(int,(q,b,w,z))
            require((q,b) not in t and b in (0,1) and w in (0,1)
                    and d in ('L','R'), 'Malformed input table')
            t[q,b] = (w,1 if d == 'R' else -1,254 if z == 230 else z)
    require(start == 0 and set(t) == {(q,b) for q in range(230) for b in (0,1)},
            'Unexpected original K state census')
    require({z for w,d,z in t.values()} - set(range(230)) == {254}, 'Wrong halt')
    return t

def incoming(t, target):
    return sorted((q,b,w,d) for (q,b),(w,d,z) in t.items() if z == target)

def literal_block(t, state, tape, steps):
    tape = dict(tape)
    head = 0
    trace = []
    for _ in range(steps):
        require(state != 254 and head in tape, 'Interior halt or unbound tape read')
        read = tape[head]
        w,d,z = t[state,read]
        trace.append([state,head,read,w,d,z])
        tape[head] = w
        state,head = z,head+d
    return state,head,tape,trace

def generic_fold(old, new, keep, drop):
    proof = v.prove(old,new,0,0,keep,drop,0,None,8,65,20000)
    require(proof['status'] == 'PASS_ALL_TAPE_POSITIVE_BLOCK_SIMULATION',
            f'Local fold failed: {proof}')
    proof.update(old_sha256=sha(encode(old)),new_sha256=sha(encode(new)),
                 checker_sha256=sha(Path(v.__file__).read_bytes()))
    return proof

def conditional140(old, new):
    facts, checks = v.bit_invariant(old,0,8)
    cases = [(71,0,{-1:1},5),(140,0,{-1:0},3),
             (140,1,{-1:0,1:1},5),(80,1,{-3:0,-2:1,-1:1},9)]
    phi = lambda q: 71 if q == 140 else q
    specials = {(q,b) for q,b,g,n in cases}
    ordinary = 0
    for (q,b),(w,d,z) in old.items():
        if (q,b) in specials:
            continue
        require(new[phi(q),b] == (w,d,phi(z)), 'Noncommuting140 ordinary row')
        ordinary += 1
    records = []
    for q,b,g,n in cases:
        for k,bit in g.items():
            if (q,b,k) != (140,1,1):
                require(facts[q].get(k) == bit, 'An unclaimed140 guard is missing')
        initial = {**g,0:b}
        ans = literal_block(new,phi(q),initial,n)
        w,d,z = old[q,b]
        require(ans[:3] == (phi(z),d,{**initial,0:w}), 'Bad140 macro endpoint')
        records.append(dict(row=[q,b],guard=g,steps=n,trace=ans[3]))
    return dict(status='CONDITIONAL_LOCAL_POSITIVE_BLOCK_PROOF',
        keep=71,drop=140,ordinary_rows=ordinary,invariant_rows=checks,
        cases=records,old_sha256=sha(encode(old)),new_sha256=sha(encode(new)),
        extra_guard='At old140 on read1, the right neighbor is1.',
        scope=('The four open-tape identities are exact under their stated '
               'guards. The extra140 guard is not asserted on all tapes. '
               'The final direct universal runtime and blank startup must '
               'independently establish the actual candidate behavior.'))

def contextsplit175(old, new):
    require(all(w == 0 and d == 1 for q,b,w,d in incoming(old,150)), '150 tag')
    require(incoming(old,65) == [(175,0,0,-1)], '65 is not purely internal')
    require(incoming(old,175) == [(155,1,1,1),(176,1,1,1),(184,0,0,1)], '175 ports')
    cases = []
    for q,left,b,nq,no,nn,z in [
        (150,0,0,150,1,1,90),(150,0,1,150,1,5,90),
        (175,0,0,65,3,1,19),(175,0,1,65,1,1,61),
        (175,1,0,150,3,1,90),(175,1,1,150,1,3,61)]:
        tape = {-1:left,0:b}
        a,c = literal_block(old,q,tape,no),literal_block(new,nq,tape,nn)
        require(a[:3] == c[:3] == (z,1,tape), 'Context-split whole-tape endpoint')
        cases.append(dict(old_state=q,left=left,read=b,new_state=nq,
                          old_steps=no,new_steps=nn,old_trace=a[3],new_trace=c[3]))
    ordinary = 0
    for row,(w,d,z) in old.items():
        if row[0] in (65,150,175):
            continue
        nz = (150 if w == 1 else 65) if z == 175 else z
        require(new[row] == (w,d,nz), 'Noncommuting context-split ordinary row')
        ordinary += 1
    require({q for q,b in new} == {q for q,b in old} - {175}, 'Wrong split deletion')
    return dict(status='PASS_ALL_TAPE_CONTEXT_SPLIT_LOCAL_PROOF',
        start=0,halt=254,deleted=175,ordinary_rows=ordinary,
        incoming={str(q):incoming(old,q) for q in (65,150,175)},cases=cases,
        old_sha256=sha(encode(old)),new_sha256=sha(encode(new)),
        scope=('All initial binary tapes. At checkpoints old175 is represented '
               'by new150 on left1 and new65 on left0. Old65 occurs only '
               'inside the three-step175/0 macro. Both old and new blocks '
               'are positive, preserve the entire tape, and have no interior halt.'))

def cb1_repair(reference, repaired):
    facts, checks = v.bit_invariant(repaired,0,8)
    for q,expected in [(103,{-3:0,-2:1,-1:1}),(229,{-4:0,-3:1,-2:1,-1:1})]:
        require(all(facts[q].get(k) == b for k,b in expected.items()), 'CB1 predecessor invariant')
    require(reference[103,1] == (0,-1,52) and repaired[103,1] == (0,-1,18), '103 repair')
    require(reference[52,1] == repaired[18,1] == (0,-1,27), 'Equivalent callback actions')
    a = literal_block(reference,103,{-1:1,0:1},2)
    c = literal_block(repaired,103,{-1:1,0:1},2)
    require(a[:3] == c[:3] == (27,-2,{-1:0,0:0}), 'Callback identity')
    suffix_cases = []
    for q,zeros_at,n in [(103,-3,4),(229,-4,5)]:
        tape = {k:int(k != zeros_at) for k in range(zeros_at,1)}
        ans = literal_block(repaired,q,tape,n)
        require(ans[:3] == (4,zeros_at-1,{k:0 for k in tape}), 'CB1 suffix repair')
        suffix_cases.append(dict(state=q,guard=tape,steps=n,trace=ans[3]))
    # Regression control: simply copying the two-one fused leaf fails on
    # the new four-one suffix. This is a concrete bounded negative check;
    # the accepted positive identities above quantify over all other cells.
    wrong = dict(repaired)
    wrong[229,1] = (0,-1,27)
    negative = literal_block(wrong,229,{-4:0,-3:1,-2:1,-1:1,0:1},5)
    require(negative[:3] != (4,-5,{-4:0,-3:0,-2:0,-1:0,0:0}), 'Negative control unexpectedly passed')
    return dict(status='PASS_ALL_TAPE_GUARDED_CB1_REPAIR',
        invariant_rows=checks,invariant=facts,old_callback_trace=a[3],
        new_callback_trace=c[3],suffix_cases=suffix_cases,
        stale_fused_leaf_negative_trace=negative[3],
        repaired_sha256=sha(encode(repaired)),
        scope=('All initial binary tapes under the checked inductive facts. '
               'The103 callback preserves its original two-step block. '
               'The relocated229 leaf clears four trailing ones and their '
               'preceding zero before entering the ordinary prefix-increment '
               'state4. The source graph specifies the intended break target.'))

def main():
    require(__debug__ and not sys.flags.optimize, 'Run without -O/-OO')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--k230',type=Path,required=True)
    ap.add_argument('--source-certificate',type=Path,required=True)
    ap.add_argument('--output-dir',type=Path,required=True)
    args = ap.parse_args()
    raw = args.k230.read_bytes()
    require(sha(raw) == K230_SHA256, 'Wrong pinned K230 input bytes')
    certificate = json.loads(args.source_certificate.read_text())
    require(certificate['final_source_sha256'] == SOURCE_SHA256, 'Wrong final source')
    stages = certificate['stages']
    require([(x['outer_state'],x['inner_state'],x['direction']) for x in stages] == ROTATIONS,
            'Unexpected rotation sequence')
    output = args.output_dir
    output.mkdir(parents=True,exist_ok=True)
    files = []
    def save(name,data):
        raw = data if isinstance(data,bytes) else (json.dumps(data,indent=2)+'\n').encode()
        (output/name).write_bytes(raw)
        files.append(dict(path=name,sha256=sha(raw)))

    original = read_k230(raw)
    save('k230_original_old.tm',encode(original))
    loop = dict(original)
    require(loop[121,0] == (0,1,31) and loop[121,1] == (1,1,63), 'Loop input rows')
    loop[121,0],loop[121,1] = (0,1,63),(1,1,13)
    save('k230_loop_basis.tm',encode(loop))
    after79 = {(q,b):(w,d,63 if z == 79 else z) for (q,b),(w,d,z) in loop.items() if q != 79}
    after79[63,0],after79[63,1] = (0,-1,123),(1,-1,30)
    save('k229_fold79.tm',encode(after79))
    save('fold79.json',generic_fold(loop,after79,63,79))
    save('fold79_independent.json',independent79.verify(output/'k230_loop_basis.tm',output/'k229_fold79.tm'))
    base = {(q,b):(w,d,71 if z == 140 else z) for (q,b),(w,d,z) in after79.items() if q != 140}
    base[71,0],base[80,1] = (0,-1,91),(1,-1,138)
    save('k228_loop_folds.tm',encode(base))
    save('fold140_conditional.json',conditional140(after79,base))

    basis = dict(base)
    for number,stage in enumerate(stages,1):
        for edit in stage['literal_rotation_edits']:
            row,before,after = tuple(edit['row']),tuple(edit['before']),tuple(edit['after'])
            require(basis[row] == before, f'Rotation{number} input mismatch at{row}')
            basis[row] = after
        if number == 1:
            # The source tree has an already existing paired subtree98.
            require(basis[65,0] == basis[98,0] and basis[65,1] == basis[98,1], 'Source DAG sharing mismatch')
            require(incoming(basis,65) == [(85,0,0,1)], 'Unexpected old65 decoder caller')
            basis[85,0] = (0,1,98)
            basis[65,0],basis[65,1] = (0,1,12),(1,1,86)
            basis[175,0] = (0,-1,65)
    for row,before,after in [((103,1),(0,-1,52),(0,-1,18)),((229,1),(0,-1,27),(0,-1,103))]:
        require(basis[row] == before, 'CB1 repair input mismatch')
        basis[row] = after
    require(len(basis) == 456, 'Wrong source basis count')
    save('k228_source_basis.tm',encode(basis))
    save('cb1_repair_basis.json',cb1_repair(base,basis))
    middle = {row:a for row,a in basis.items() if row[0] != 175}
    middle[150,1] = (1,-1,173)
    middle[155,1],middle[176,1] = (1,1,150),(1,1,150)
    middle[65,0],middle[65,1],middle[184,0] = (0,1,19),(1,1,61),(0,1,65)
    save('k227_contextsplit.tm',encode(middle))
    save('contextsplit175.json',contextsplit175(basis,middle))
    final = {(q,b):(w,d,152 if z == 65 else z) for (q,b),(w,d,z) in middle.items() if q != 65}
    final[152,0],final[152,1] = (0,-1,159),(1,-1,169)
    require(len(final) == 452 and sha(encode(final)) == K226_SHA256, 'Wrong exact final226 table')
    save('k226_old.tm',encode(final))
    save('fold65_into152.json',generic_fold(middle,final,152,65))
    save('cb1_repair_final.json',cb1_repair(base,final))
    labels = sorted({q for q,b in final})
    mp = {q:n for n,q in enumerate(labels)} | {254:226}
    canonical = {(mp[q],b):(w,d,mp[z]) for (q,b),(w,d,z) in final.items()}
    require(set(canonical) == {(q,b) for q in range(226) for b in (0,1)} and mp[0] == 0, 'Bad canonicalization')
    save('k226.tm',encode(canonical))
    save('renumbering226.json',dict(old_to_new=mp,new_to_old=labels+[254],start_old=0,start_new=0,
         dispatcher_old=84,dispatcher_new=mp[84],halt_old=254,halt_new=226))
    save('construction226.json',dict(status='EXACT_CONSTRUCTION_AND_LOCAL_IDENTITIES_PASS',
         working_states=226,rows=452,start=0,canonical_halt=226,
         deleted_K_labels=[65,79,140,175],canonical_sha256=sha(encode(canonical)),
         inherited_labels_sha256=K226_SHA256,source_sha256=SOURCE_SHA256,
         K230_input_sha256=K230_SHA256,source_certificate_sha256=sha(args.source_certificate.read_bytes()),
         builder_sha256=sha(Path(__file__).read_bytes()),rotation_count=len(stages),
         independent_obligations=['Source loop equivalence','Source graph replay',
             'Universal binary runtime','Exact blank startup','Inherited logical calibration'],
         scope='Construction and local mathematical certificates; not a proof-assistant kernel theorem.'))
    (output/'machine_artifacts.json').write_text(json.dumps(files,indent=2)+'\n')
    print(json.dumps(dict(status='EXACT_CONSTRUCTION_AND_LOCAL_IDENTITIES_PASS',
        output_dir=str(output),working_states=226,canonical_sha256=sha(encode(canonical)),
        inherited_labels_sha256=K226_SHA256,artifacts=len(files)),indent=2))

if __name__ == '__main__':
    main()
