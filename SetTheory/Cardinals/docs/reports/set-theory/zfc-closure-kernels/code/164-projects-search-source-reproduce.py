#!/usr/bin/env python3
"""Reproduce exact source findings and prefix allocation prices, without network.

No changed table here is certified as a blank-start consistency machine.
The allocator is tested only for internal prefix decoding; arithmetic leaves,
initialization and complete unbounded runtime remain separate obligations.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=HERE/'reproduced')
    args = ap.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Run Python without -O')
    pins = json.loads((HERE/'SOURCE_PINS.json').read_bytes())
    for name, item in pins['files'].items():
        require(sha((HERE/name).read_bytes()) == item['sha256'], 'Hash mismatch: '+name)
    sys.path.insert(0, str(HERE/'vendor'))
    import source_splice as sp
    import source_language as s
    import build221 as b
    import global_allocator_v2 as alloc
    old = s.tree(json.loads((HERE/'inputs/sites219.json').read_bytes()))
    cur = s.tree(json.loads((HERE/'inputs/sites217.json').read_bytes()))
    table = b.read_table((HERE/'inputs/k217.native.tm').read_bytes())
    require(len(table) == 434, 'Baseline working state count')
    mp, _ = sp.build(old)
    require(s.compact(s.sites(mp)) == (HERE/'inputs/dominated_yx205.json').read_bytes(), 'MP-only inherited construction')
    read_a = sp.serial(sp.closed_forest(old,23,37))
    copy_a = sp.serial(sp.closed_forest(old,40,66))
    transplant = sp.apply_closed_splices(cur, {
        (23,37):None, (187,201):None,
        (228,254):(read_a,copy_a), (4659,4685):(read_a,copy_a)})
    rows = s.sites(transplant)
    require(s.compact(rows) == (HERE/'results/mp-only202.json').read_bytes(), 'Exact 202-node transplant')
    require([r[1:] for r in rows] == [r[1:] for r in s.sites(mp)], 'Calibrated MP-only primitive word')
    require(s.graph_intervals(rows) == s.graph_arithmetic(rows)[0] == s.graph_intervals(s.sites(mp)), 'MP-only guarded CFG')
    require(s.metrics(transplant) == dict(dag_nodes=202,leaf_occurrences=4751,maximum_depth=44,maximum_zero_run=7), 'Transplant census')
    def price(tree):
        output, receipt = alloc.compile_tree(s,b,table,cur,tree,hypothetical_entries=False,require_pure_rows=True)
        return dict(working_states=receipt['working_states'],pool_reused=receipt['pool_used'],fresh=receipt['fresh'],table_sha256=sha(b.table_bytes(output)),scope='PREFIX-ONLY allocation, NOT complete runtime or blank initialization')
    mp_price = price(transplant)
    require(mp_price['working_states']==220 and mp_price['pool_reused']==18 and mp_price['fresh']==4,'MP-only prefix allocation')
    require(mp_price['table_sha256']=='29a7a9cd6aa6da3ef33019a59e81ffebfc7464d8d80bd3e93da8681df3dfc42f','MP-only allocation hash')
    retag = s.tree(json.loads((HERE/'results/retag203-27.json').read_bytes()))
    rr = s.sites(retag)
    require(s.graph_arithmetic(rr)[0] == s.graph_intervals(rr) == s.graph_intervals(s.sites(cur)), 'Retagged exact guarded CFG')
    require(s.metrics(retag)==dict(dag_nodes=203,leaf_occurrences=4751,maximum_depth=47,maximum_zero_run=6),'Retag census')
    require(sum('000000' in p for p,o,a in rr)==27,'Retag six-zero occurrence count')
    try:
        price(retag)
    except (ValueError,AssertionError,KeyError) as exc:
        retag_error = str(exc)
    else:
        raise ValueError('Expected inherited allocator to reject retag layout')
    # The second AX gate in the transplant occupies [4578,4590).
    old_gate = sp.serial(sp.closed_forest(transplant,4578,4590))
    transfer_hd = (('CD',5),(('CI',4),('CC',2)))
    transfer_xd = (('CD',6),(('CI',4),('CC',2)))
    transfer_dt = (('CD',4),(('CI',1),('CC',2)))
    gate_h = sp.apply_closed_splices(old_gate,{(5,7):transfer_hd})
    require(s.subtree(old_gate,'0110') == (('CD',6),('CC',2)),'X-side cleanup shape')
    gate_x = s.replace(old_gate,'0110',transfer_xd)
    def run_gate(gate, A, C, initial_top):
        graph = s.graph_intervals(s.sites((gate,('CH',None))))
        regs = [0,initial_top,0,0,0,A,C,0,0]
        pc = 0
        for steps in range(100000):
            effect,targets = graph[pc]
            if effect[0]=='halt':
                return regs,steps
            if effect[0]=='increment':
                regs[effect[1]] += 1
                pc = targets[0]
            elif effect[0]=='decrement':
                r = effect[1]
                positive = regs[r]>0
                regs[r] -= positive
                pc = targets[positive]
            else:
                pc = targets[0]
        raise ValueError('Bounded gate probe failed to return')
    checks = 0
    for which, gate in [('h',gate_h),('x',gate_x)]:
        require(s.boundary(gate)==(0,0,False),'Closed residual gate')
        gr = s.sites((gate,('CH',None)))
        require(s.graph_intervals(gr)==s.graph_arithmetic(gr)[0],'Dual gate CFG')
        for A in range(30):
            for C in range(30):
                regs, steps = run_gate(gate,A,C,17)
                residual = max((A-C if which=='h'else C-A)-1,0)
                require(regs==[0,0 if A==C else 17,0,0,residual,0,0,0,0], 'Residual gate equation')
                checks += 1
    variants = {}
    for which, gate in [('h',gate_h),('x',gate_x)]:
        for consume in (False,True):
            edits = {(4578,4590):gate,(4645,4659):None}
            if consume:
                edits[152,159] = transfer_dt
            tree = sp.apply_closed_splices(transplant,edits)
            name = which+('-consume' if consume else '-dominated')
            raw = s.compact(s.sites(tree))
            require(raw == (HERE/'residual'/f'{name}.json').read_bytes(), 'Residual source '+name)
            require(s.graph_intervals(s.sites(tree))==s.graph_arithmetic(s.sites(tree))[0],'Residual dual CFG '+name)
            p = price(tree)
            require(p['working_states']==(228 if consume else 225),'Literal residual prefix price')
            variants[name] = dict(source_sha256=sha(raw),metrics=s.metrics(tree),prefix_only=p,
                semantic_scope=('AX input A is independent of old D; full command compiler/calibration is a separate proof' if consume else 'A=old D+x; this version needs an additional candidate reset or another completeness argument'))
    dominated_x = s.tree(json.loads((HERE/'residual/x-dominated.json').read_bytes()))
    fetch = sp.serial(sp.closed_forest(dominated_x,2,9))
    clear_d = (('CD',4),('CC',1))
    for before in (True,False):
        replacement = (clear_d,fetch) if before else (fetch,clear_d)
        tree = sp.apply_closed_splices(dominated_x,{(2,9):replacement})
        name = 'x-reset-'+('before' if before else 'after')
        require(s.compact(s.sites(tree)) == (HERE/'residual'/f'{name}.json').read_bytes(),'Reset variant source')
        require(s.graph_intervals(s.sites(tree))==s.graph_arithmetic(s.sites(tree))[0],'Reset dual CFG')
        p = price(tree)
        require(p['working_states']==227,'Reset prefix price')
        variants[name] = dict(source_sha256=sha(s.compact(s.sites(tree))),metrics=s.metrics(tree),prefix_only=p,semantic_scope='Resets D on each newly enumerated candidate; command completeness remains a separate proof')
    rebracketed = {}
    for variant, initial_name in [('consume','x-consume'),('dominated','x-dominated')]:
        path = HERE/'residual'/f'best-{variant}.json'
        if not path.exists():
            continue
        tree = s.tree(json.loads(path.read_bytes()))
        original = s.tree(json.loads((HERE/'residual'/f'{initial_name}.json').read_bytes()))
        row = s.sites(tree)
        require([r[1:]for r in row]==[r[1:]for r in s.sites(original)],'Rebracketed primitive word')
        require(s.graph_arithmetic(row)[0]==s.graph_intervals(row)==s.graph_intervals(s.sites(original)),'Rebracketed guarded CFG')
        rebracketed[variant] = dict(source_sha256=sha(path.read_bytes()),metrics=s.metrics(tree),prefix_only=price(tree))
    findings = dict(status='EXACT_SOURCE_FINDINGS_AND_PREFIX_PRICES_REPRODUCED',
        repository_commit=pins['commit'],proof_scope='Source CFG and decoder prefixes only. No new verified consistency-machine table.',
        mp_only=dict(source_sha256=sha(s.compact(rows)),metrics=s.metrics(transplant),primitive_word_equal_to_reference=True,guarded_CFG_equal_to_reference=True,prefix_only=mp_price,scanner_warning='Zero run 7 exceeds inherited scanner budget 6'),
        retag=dict(source_sha256=sha(s.compact(rr)),metrics=s.metrics(retag),guarded_CFG_equal_to_K217=True,six_zero_occurrences=27,baseline_six_zero_occurrences=37,allocator_rejection=retag_error),
        residual_gate_probes=dict(cases=checks,A_range=[0,29],C_range=[0,29],initial_T=17,H_residual='max(A-C-1,0)',X_residual='max(C-A-1,0)',scope='Finite sanity checks; unbounded equations are proved by the loop analysis in README'),
        residual_variants=variants,rebracketed_residual=rebracketed,
        helper_span_search=json.loads((HERE/'results/helper-span-search.json').read_bytes()))
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/'findings.json').write_text(json.dumps(findings,indent=2)+'\n')
    print('Source checks passed; MP-only202 prefix allocation220; no new verified <=216-state machine.')
    print(args.output/'findings.json')

if __name__=='__main__':
    main()
