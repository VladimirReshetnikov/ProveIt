#!/usr/bin/env python3
"""Positive runtime control and deliberately unsound fusion negative control.

The 5->64 runtime-only fold is already known from ProveIt's source04 work.
It is a regression control, not a new machine or state-count improvement.
"""
import hashlib
import json
from pathlib import Path
import hybrid_fusion_search as h
import hybrid_window_search as w

def main():
    for file,pin in h.PINS.items():
        assert hashlib.sha256((h.SRC/file).read_bytes()).hexdigest()==pin
    compact,start=h.read_table(h.SRC/'zfc_253.tm')
    labels=h.assignment(h.SRC/'12-sorts-code-regenerate_253.py','OLD_LABELS')
    table={(str(labels[int(q)]),b):(a,d,str(labels[int(n)]))for(q,b),(a,d,n)in compact.items()}
    fold={(q,b):(a,d,'64'if n=='5'else n)for(q,b),(a,d,n)in table.items()if q!='5'}
    box=h.assignment(h.SRC/'20-complete-vendor-decoder255-verify.py','BOX_STATES')
    protected={(str(q),b)for q in box for b in(0,1)}-{('3',0)}
    assert len(protected)==55 and all(table[k]==fold[k]for k in protected)
    ns=h.cs.executor(fold,h.SRC/'symexec.py')
    cases=h.cs.cases(ns,h.cs.program_sites(h.SRC/'Prog254.v'))
    assert len(cases)==8391
    for i,case in enumerate(cases): assert h.cs.check(ns,case,1000),i
    ones={-18,23};pos=24
    for v in [0,2,0,0,0,0,5,0,0]+[0,0,1,0,0,0,0,0,1]+[0]*149:
        pos+=1;ones.update(range(pos,pos+v+1));pos+=v+1
    assert len(ones)==178
    boot=h.literal_blank_run(fold,'64',2000000,(-17,ones))
    assert boot==dict(outcome='fuel_limit',steps=2000000,state='95',head=750,ones=646),boot
    result=dict(known_runtime252_control=dict(affine_cases_passed=8391,
                all55_protected_rows_unchanged=True,blank_prefix=boot,
                attribution='Existing source04 public253 fold 5->64; reproduced only as a regression',
                meaning='A runtime contract can pass while the public blank initializer contract remains unverified'),
                hybrid_controls=w.self_tests(),
                driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (h.HERE/'controls.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
