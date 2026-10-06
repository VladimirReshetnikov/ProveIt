"""Original one-use metadata composer. Never evaluate saved arithmetic rows.
After its first run this file and the first receipt are frozen forever.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json

WIP = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PARENT = WIP / 'positive7_quotient_pair_compose_root.json'
PIN = 'eda474bec49c4a2e4fef729c1cae8ed01ee940a8b63a56bb1e1d4cf64684f674'
OUT = Path('/tmp/positive7_repeated_pack_compiler_root.json')
assert not OUT.exists()
raw = PARENT.read_bytes()
assert hashlib.sha256(raw).hexdigest() == PIN
parent = json.loads(raw)

def digest(value):
    return hashlib.sha256(json.dumps(value, separators=(',', ':')).encode()).hexdigest()

def census(rows):
    c = Counter(row[1] for row in rows)
    assert set(c) <= {'+', '-', '*'}
    return dict(M=c['*'], A=c['+']+c['-'], operations=len(rows))

def compose(old):
    r, m, ell = old['r'], old['m'], old['ell']
    assert r >= 1 and m == 8+2*r and ell == 62+6*r
    blocks = old['retained_port_labels']
    widths = [len(b) for b in blocks]
    assert widths == [6]*4+[7]*4+[2]*(2*r)
    groups = {}; pos = 0
    for label, count in old['stages'].items():
        groups[label] = old['source'][pos:pos+count['operations']]
        assert census(groups[label]) == count
        pos += count['operations']
    assert pos == len(old['source'])
    rows = []; stages = {}; kept = []; removed = []
    stage = ''
    def emit(name, op, a, b):
        row = [name, op, a, b]
        rows.append(row); stages.setdefault(stage, []).append(row)
        return name
    def retain(records, mapping=None):
        mapping = mapping or {}
        for row in records:
            name, op, a, b = row
            aa = mapping.get(a, a) if isinstance(a, str) else a
            bb = mapping.get(b, b) if isinstance(b, str) else b
            emit(name, op, aa, bb)
            if aa == a and bb == b: kept.append(name)
    P, J = old['ports']['P'], old['ports']['J']
    selectors = ['selector_'+str(i) for i in range(m)]
    masks = {'aggregate_mask'} | {'letter_mask_'+str(i) for i in range(m)}
    old_by_name = {row[0]: row for row in old['source']}
    semantic_definitions = {name: old_by_name[name] for name in sorted(masks)}
    assert old_by_name['aggregate_mask'] == ['aggregate_mask', '*', 'height_mask', J]
    for i in range(m):
        assert old_by_name['letter_mask_'+str(i)] == ['letter_mask_'+str(i), '*', 'cell_mask', selectors[i]]
    stage = 'input_and_mass'; retain(groups['input_and_mass'])
    stage = 'geometry_without_redundant_masks'
    for row in groups['geometry_guard_centers_and_masks']:
        if row[0] in masks: removed.append(row)
        else: retain([row])
    stage = 'shared_centered_input_forms'; retain(groups[stage])
    stage = 'shared_pack_powers_and_coefficients'
    assert old_by_name['scale_square_0'] == ['scale_square_0', '*', P, P]
    p2 = emit('scale_square_0', '*', P, P)
    p3 = emit('pack_P3', '*', p2, P)
    p6 = emit('pack_P6', '*', p3, p3)
    p7 = emit('pack_P7', '*', p6, P)
    r2 = emit('pack_R2', '+', P, 1)
    r3 = emit('pack_R3', '+', r2, p2)
    u3 = emit('pack_P3_plus_one', '+', p3, 1)
    r6 = emit('pack_R6', '*', r3, u3)
    r7 = emit('pack_R7', '+', r6, p6)
    powers = {2:p2, 3:p3, 6:p6, 7:p7}
    reps = {2:r2, 3:r3, 6:r6, 7:r7}
    coefficients = {n:emit('pack_C'+str(n), '*', 'cell_mask', reps[n]) for n in (2,6,7)}
    assert census(stages[stage]) == dict(M=8,A=4,operations=12)
    stage = 'selector_power_and_geometric_extension'
    bits = format(m, 'b')
    seed, consumed = (int(bits[:3],2),3) if bits.startswith(('110','111')) else (2,2)
    assert seed in (2,6,7)
    n = seed; pn = powers[n]; rn = reps[n]
    for bit in bits[consumed:]:
        twice = 2*n
        pp = emit('geom_P'+str(twice), '*', pn, pn)
        plus = emit('geom_factor_'+str(twice), '+', pn, 1)
        rr = emit('geom_R'+str(twice), '*', rn, plus)
        n, pn, rn = twice, pp, rr
        if bit == '1':
            rn = emit('geom_R'+str(n+1), '+', rn, pn)
            pn = emit('geom_P'+str(n+1), '*', pn, P)
            n += 1
    assert n == m
    d = len(bits)-consumed; e = bits[consumed:].count('1')
    gm, ga = 2*d+e, d+e
    assert census(stages.get(stage,[])) == dict(M=gm,A=ga,operations=gm+ga)
    stage = 'shared_selector_polynomial'
    q = selectors[-1]
    for i in range(m-2,-1,-1):
        q = emit('selector_polynomial_shift_'+str(i), '*', q, P)
        q = emit('selector_polynomial_join_'+str(i), '+', q, selectors[i])
    stage = 'two_upper_horner_packs'
    for row in groups['three_guarded_packs']:
        name = row[0]
        side, kind, index = name.split('_'); index = int(index)
        assert side in ('left','right','output') and kind in ('shift','join')
        if side == 'right' or index < m: removed.append(row)
        else: retain([row])
    assert census(stages[stage]) == dict(M=2*ell-3-2*m,A=2*ell-3-2*m,operations=4*ell-6-4*m)
    stage = 'factored_pack_joins'
    tail = emit('right_tail_sum', '+', J, P)
    acc = emit('right_tail_product', '*', 'height_mask', tail)
    for i in range(m-1,-1,-1):
        width = widths[i]
        upper = emit('right_block_shift_'+str(i), '*', acc, powers[width])
        lower = emit('right_block_lower_'+str(i), '*', coefficients[width], selectors[i])
        acc = emit('right_block_join_'+str(i), '+', upper, lower)
    right_high = emit('right_selector_shift', '*', acc, pn)
    right_low = emit('right_selector_sum', '*', J, rn)
    right = emit('packed_right', '+', right_high, right_low)
    left_high = emit('left_selector_shift', '*', 'left_join_'+str(m), pn)
    left = emit('packed_left', '+', left_high, q)
    output_high = emit('output_selector_shift', '*', 'output_join_'+str(m), pn)
    output = emit('packed_output', '+', output_high, q)
    stage = 'fixed_native_power_after_shared_square'
    power_rows = groups['fixed_native_power']
    assert power_rows[0] == old_by_name['scale_square_0']
    retain(power_rows[1:])
    stage = 'complete_native64'
    bindings = dict(zip(old['ports']['native_packs'], [left,right,output]))
    retain(groups[stage], bindings)
    after_native = False
    for label, records in groups.items():
        if after_native:
            stage = label; retain(records)
        if label == 'complete_native64': after_native = True
    supplied = ['x']+old['positive_auxiliaries']
    known = set(supplied); dependency = {}; roles = set()
    assert len(supplied) == len(known)
    for name, op, a, b in rows:
        assert name not in known and op in ('+','-','*')
        for operand in (a,b):
            if isinstance(operand,str): assert operand in known, (name,operand)
            elif isinstance(operand,dict):
                assert set(operand)=={'fixed'}; roles.add(operand['fixed'])
            else: assert type(operand) is int
        known.add(name); dependency[name] = (a,b)
    live=set(); pending=[old['output']]
    while pending:
        node=pending.pop()
        if isinstance(node,str) and node not in live:
            live.add(node); pending.extend(dependency.get(node,()))
    assert set(dependency) <= live and set(supplied) <= live
    assert len(roles)==6+18*r
    assert roles==set(old['static_checks']['named_fixed_roles'])
    finalizer = groups['single_polynomial_finalizer']
    assert rows[-len(finalizer):] == finalizer
    poly=census(rows); cert=census(rows[:-len(finalizer)])
    pc=old['power_cost']
    assert poly==dict(M=252+34*r+pc+gm,A=541+46*r+ga,operations=793+80*r+pc+gm+ga)
    assert cert==dict(M=229+34*r+pc+gm,A=496+46*r+ga,operations=725+80*r+pc+gm+ga)
    assert len(supplied)-1==96+6*r and len(old['comparisons'])==23
    g={k:v for k,v in old.items() if k not in ['source','stages','static_checks','splice','ports','certificate_ledger','polynomial_ledger','certificate_prefix_rows','lanes_in_order']}
    g['ports']=dict(old['ports'],native_packs=[left,right,output],selector_polynomial=q,selector_power=pn,selector_geometric_sum=rn)
    g['lanes_in_order']=[[{'semantic_product':semantic_definitions[v][2:]} if isinstance(v,str) and v in masks else v for v in lane] for lane in old['lanes_in_order']]
    g['semantic_lane_note']='semantic_product describes the unchanged lane value; it is not an executable port or an extra supplied value'
    g.update(source=rows,stages={k:census(v) for k,v in stages.items()},certificate_ledger=cert,polynomial_ledger=poly,certificate_prefix_rows=len(rows)-len(finalizer),geometric_extension=dict(seed=seed,bits=bits,remaining=bits[consumed:],d=d,e=e,M=gm,A=ga),static_checks=dict(topology=True,all_computed_live=True,all_supplied_live=True,named_fixed_roles=sorted(roles)))
    g['pack_splice']=dict(removed_rows=removed,moved_first_square=old_by_name['scale_square_0'],removed_digest=digest(removed),old_source_digest=digest(old['source']),new_source_digest=digest(rows),retained_literal_row_names=kept,native_pack_bindings=bindings,comparisons_literal_equal=g['comparisons']==old['comparisons'],positive_auxiliaries_literal_equal=g['positive_auxiliaries']==old['positive_auxiliaries'],finalizer_literal_equal=True,old_mask_semantic_definitions=semantic_definitions)
    return g

examples=[compose(g) for g in parent['examples']]
assert [g['r'] for g in examples]==[1,2,4]
receipt=dict(status='FROZEN first metadata-only composition; never replay',emitter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),inputs=[dict(path=str(PARENT),sha256=PIN,bytes=len(raw))],generic_ledger=dict(domain='r>=1',certificate='(229+34r+pc(62+6r)+gM(8+2r))M+(496+46r+gA(8+2r))A',polynomial='(252+34r+pc(62+6r)+gM(8+2r))M+(541+46r+gA(8+2r))A',operations='793+80r+pc(62+6r)+gM(8+2r)+gA(8+2r)',witnesses='96+6r',equations=23,fixed_roles='6+18r',geometric_cost='seed6/7 for leading110/111, otherwise seed2 for leading10; for remaining d bits and e ones, gM=2d+e,gA=d+e'),r0_fallback=parent['r0_fallback'],fixed_data_recipe=parent['fixed_data_recipe'],examples=examples,execution_scope='Fresh construction/counting/binding/liveness of inert records only. No saved source/coefficient evaluation, scientific code replay/import, degree propagation, numerical testing or build.')
OUT.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(dict(output=str(OUT),sha256=hashlib.sha256(OUT.read_bytes()).hexdigest(),saved_rows=sum(len(g['source']) for g in examples),examples=[dict(r=g['r'],ledger=g['polynomial_ledger'],witnesses=g['witnesses']) for g in examples]),indent=2))
