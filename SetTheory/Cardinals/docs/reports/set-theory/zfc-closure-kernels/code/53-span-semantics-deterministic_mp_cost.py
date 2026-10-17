#!/usr/bin/env python3
"""Measure a deterministic antecedent/ consequent MP parser in the full program.

This retains all logical and theory constructors. It changes MP to decode
the cached formula and infer its consequent directly, then tests F at birth.
It is a complete source/table cost control, not a verified blank machine.
"""
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import mp_birth_cost as ref

def seq(*xs):
    assert xs
    return xs[0] if len(xs) == 1 else (xs[0], seq(*xs[1:]))

def make_builder(test_birth):
    original, names = ref.recover.parse_dag((ref.REF/'Dag254.v').read_text())
    b = ref.recover.builder_from_dag(ref.backend, original, names)
    regs = [b.registers[x] for x in ref.recover.REGISTERS]
    N,T,W,A,D,H,X,Y,L = regs
    # Populate exact-pair sharing from the imported binary DAG.
    for q,s in enumerate(b.sequences): b.sequence_lookup.setdefault(s.seq,q)
    def add(tree): return b.add_sequence(tree)
    def while_raw(var, body, label):
        return b.label(label, (var.decnz, (body, 'continue_'+label)))
    def transfer(var, dest, label):
        return add(while_raw(var,dest.inc,label))
    clearA = add((A.decnz, '_continue.1'))
    clearY = add((Y.decnz, '_continue.1'))
    AtoH = transfer(A,H,'copy_a_h')
    unpairT = add((T.decnz,154))
    # The first subtraction ends the quotient loop normally at zero. Each of
    # the remaining three detects a nonzero remainder and exits the valid arm.
    require_unit = ((H.decnz, '_break.1'), 'break_valid')
    division = while_raw(H,seq(require_unit,require_unit,require_unit,T.inc),'divide')
    # 123 is the original destructive equality test X=H; its successful body
    # is the next edge. Transfer Y through X into T and skip failure clearing.
    success = seq(211,208,'break_result')
    valid = b.label('valid',seq(division,unpairT,AtoH,(123,success)))
    result = b.label('result',(valid,214))
    body = seq(216,201,result,clearA,clearY)
    if test_birth:
        guard = (T.decnz, (((T.decnz,'_break.1'),'halt'),159))
        body = (body,guard)
        # NIP now clears the previous cache and pops, with no halting test.
        b.sequences[147].seq = (148,153)
        b.sequences[153].seq = (199,170)
    body_id = add(body)
    b.sequences[150].seq = b.sequences[body_id].seq
    b.reduce_to_cons()
    b.name_sequences()
    regids = {x:i for i,x in enumerate(ref.recover.REGISTERS)}
    def parse_edge(e):
        if isinstance(e,int): return 'ENode '+str(e)
        if e == 'halt': return 'EHalt'
        if e.startswith('_break.'): return 'EBreak '+e.split('.')[1]
        if e.startswith('_continue.'): return 'EContinue '+e.split('.')[1]
        _,name,op = e.split('.')
        return ('EInc ' if op == 'inc' else 'EDecnz ')+str(regids[name])
    nodes = {q:tuple(map(parse_edge,s.seq)) for q,s in enumerate(b.sequences)}
    names = {q:s.name for q,s in enumerate(b.sequences)}
    return b,nodes,names

def unP(n):
    x=y=0
    for _ in range(n):
        if x: x-=1; y+=1
        else: x=y+1; y=0
    return x,y

def main():
    out = Path(__file__).resolve().parent/'deterministic_mp_results'
    out.mkdir(exist_ok=True)
    reports={}
    for test_birth in (False,True):
        b,nodes,names=make_builder(test_birth)
        cases=0
        for h in range(121):
            for t in range(9):
                for w,d in [(0,0),(4,7)]:
                    initial=[11,t,w,0,d,h,0,0,19]
                    expected=list(initial)
                    expected[5]=0
                    a,c=unP(h//4)
                    ok=(h%4==0 and a==t)
                    expected[1]=c if ok else 0
                    if test_birth and ok and c==1: expected=None
                    actual,_=ref.run_tree(nodes,150,initial,fuel=1000000)
                    assert actual==expected, (test_birth,h,t,actual,expected)
                    cases+=1
        b.generate(); b.tm.gc()
        active=ref.reachable(nodes)
        ref.recover.reextract(b.tm,{q:nodes[q] for q in active},{q:names[q] for q in active})
        label='deterministic_birth' if test_birth else 'deterministic_nip_halt'
        result=ref.canonical(b.tm,out/(label+'.tm'))
        framework={q for q,_ in b.tm.states if q[0].isdigit()}
        result.update(decision_states=len(active),framework_states=len(framework),
                      exact_structured_mp_cases=cases,source_reextraction=True,
                      changed_fields='success sets T to decoded consequent; W unchanged; D ignored and preserved; H/A/X/Y cleared')
        assert result['working_states']==len(active)+len(framework)
        reports[label]=result
        (out/(label+'-dag.json')).write_text(json.dumps(dict(nodes=nodes,names=names),indent=2)+'\n')
    record=dict(status='NEGATIVE_COMPLETE_COST_CONTROL',upstream_commit=ref.recover.COMMIT,
                source_sha256=ref.sha(__file__),results=reports,
                limitations=['No new binary runtime or bootstrap proof.',
                  'Ordinary proof-search completeness needs the adjusted MP compilation block.',
                  'These complete Wade costs cannot be subtracted from the optimized 252 table.'])
    (out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(reports,indent=2))

if __name__=='__main__': main()
