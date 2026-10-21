#!/usr/bin/env python3
"""Render balanced finite certificates for the checked normalized checker."""
import json
from pathlib import Path
if not __debug__:
    raise SystemExit('Run this generator without Python -O; its validation uses assertions.')

BASE=Path(__file__).resolve().parent
OUT=BASE/'normalized_lean'
NS='SetTheory.BusyBeaver.ZFC.KSource215Normalized'

def tree(es):
    if not es:return '.empty'
    if len(es)==1:return '.leaf ('+', '.join(map(str,es[0]))+')'
    k=len(es)//2
    return f'.branch {k} ({tree(es[:k])}) ({tree(es[k:])})'

def ctree(parts):
    if len(parts)==1:return parts[0][0]
    k=len(parts)//2
    return f'.branch {sum(n for _,n in parts[:k])} ({ctree(parts[:k])}) ({ctree(parts[k:])})'

def main():
    OUT.mkdir(exist_ok=True)
    c=json.loads((BASE/'normalized_certificate.json').read_text())['entries']
    c=[[int(x) for x in row] for row in c]
    parts=[c[i:i+90] for i in range(0,len(c),90)]
    header=f'namespace {NS}\n\nopen RegisterPath RMBisim RMNormalizedBisim KSource215\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
    body='import BusyBeaver.ZFC.RMNormalizedBisim\nimport BusyBeaver.ZFC.KSource215Data\n\n'+header
    for i,part in enumerate(parts):body+=f'def chunk{i} : CTree :=\n  {tree(part)}\n\n'
    body+=f'def certificate : CTree :=\n  {ctree([(f"chunk{i}",len(p)) for i,p in enumerate(parts)])}\n\n'
    body+='def checkEntry : Entry → Bool := RMNormalizedBisim.entryOk t215 tD certificate\n\n'
    body+=f'end {NS}\n'
    (OUT/'KSource215NormalizedData.lean').write_text(body)
    for i,part in enumerate(parts):
        body='import BusyBeaver.ZFC.KSource215NormalizedData\n\n'+header
        if i<8:
            body+=f'theorem chunk_ok{i} : allC checkEntry chunk{i} = true := by decide +kernel\n\n'
        else:
            body+='private def left : CTree → CTree\n  | .branch _ l _ => l\n  | _ => .empty\n\nprivate def right : CTree → CTree\n  | .branch _ _ r => r\n  | _ => .empty\n\n'
            terms=[f'{outer} ({inner} chunk{i})' for inner in ['left','right'] for outer in ['left','right']]
            for j,term in enumerate(terms):
                body+=f'private theorem part{j}_ok : allC checkEntry ({term}) = true := by decide +kernel\n\n'
            checks=[f'allC checkEntry ({term})' for term in terms]
            body+=f'theorem chunk_ok{i} : allC checkEntry chunk{i} = true := by\n'
            body+=f'  have h : allC checkEntry chunk{i} =\n      (({checks[0]} && {checks[1]}) &&\n      ({checks[2]} && {checks[3]})) := rfl\n'
            body+='  rw [h, part0_ok, part1_ok, part2_ok, part3_ok]\n  rfl\n\n'
        body+=f'end {NS}\n'
        (OUT/f'KSource215NormalizedCheck{i:02d}.lean').write_text(body)
    body=''.join(f'import BusyBeaver.ZFC.KSource215NormalizedCheck{i:02d}\n' for i in range(len(parts)))+'\n'+header
    body+='theorem start_ok : RMNormalizedBisim.branchOk t215 tD certificate [] [] 0 = true := by decide +kernel\n\n'
    body+='theorem all_ok : allC checkEntry certificate = true := by\n  unfold certificate\n  simp only [allC, '+', '.join(f'chunk_ok{i}' for i in range(len(parts)))+', Bool.and_self]\n\n'
    body+='theorem start_ok\' : RMNormalizedBisim.branchOk (ptree p215) (ptree pathDagPerm) certificate [] [] 0 = true := by\n  rw [t215_eq, tD_eq]; exact start_ok\n\n'
    body+='theorem all_ok\' : allC (RMNormalizedBisim.entryOk (ptree p215) (ptree pathDagPerm) certificate) certificate = true := by\n  rw [t215_eq, tD_eq]; exact all_ok\n\n'
    body+='theorem p215_halts_iff (R : Registers) : Halts p215 ⟨[], R⟩ ↔ Halts pathDagPerm ⟨[], R⟩ :=\n  RMNormalizedBisim.check_halts_iff start_ok\' all_ok\' R\n\n#print axioms p215_halts_iff\n\n'
    body+=f'end {NS}\n'
    (OUT/'KSource215Normalized.lean').write_text(body)
    print(json.dumps({'chunks':[len(p) for p in parts],'lean_bytes':sum(p.stat().st_size for p in OUT.glob('*.lean'))}))

if __name__=='__main__':main()
