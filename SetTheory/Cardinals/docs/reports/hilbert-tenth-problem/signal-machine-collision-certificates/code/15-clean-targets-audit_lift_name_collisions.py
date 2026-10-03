#!/usr/bin/env python3
"""Regression: valid compact names may coincide with extra full-core slots."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
SUB=HERE.parent
sys.path.insert(0,str(SUB))
import clean_targets as ct
from check_clean_targets import check
import checker as forward_checker
I,M=ct.Instruction,ct.Machine

def main():
    cases=[]
    for machine,q0,h in [(M(('h',),'h',()),'h',0),
                        (M(('s','h'),'h',(I('s','h','inc',0),)),'s',1)]:
        names=('e_0_0','u_1_1','e_0_1') if h==0 else ('e_0_1','u_0_1','e_3_3','u_3_3','lift_0')
        for name in names:
            for mode in ('raw','time','bounded','raw_and_time'):
                inp={'mode':'fixed_raw','N':1};free={};time_spec=None
                if mode in ('raw','raw_and_time'):
                    inp={'mode':'free_raw','name':name};free={name:0}
                if mode in ('time','raw_and_time'):
                    other=('u_1_1' if name!='u_1_1' else 'e_0_0') if h==0 else ('u_0_1' if name!='u_0_1' else 'e_0_1')
                    time_spec={'mode':'free','name':name if mode=='time' else other}
                if mode=='bounded':
                    inp={'mode':'bounded_counters','A':1,'B':0,'a':None,'b':0,'a_name':name};free={name:0}
                for model in ('native','spatial-radius-one','phase-radius-one'):
                    c=ct.export_clean_certificate(machine,q0,h,inp,time_spec,model)
                    w=ct.make_clean_witness(c,free);co=check(c,w)
                    full,lw=ct.lift_clean_witness(c,w)
                    nf,forms=ct.affine_full_witness_lift(c)
                    assert full==nf
                    assert lw=={n:ct.core.evaluate_affine(f,w) for n,f in forms.items()}
                    fo=forward_checker.check(full,lw)
                    assert fo['physical_time']==co['physical_time'] and fo['final_N']==1
                    full_inputs={n:ct.core.evaluate_affine(forms[n],w) for n in full['input_variables']}
                    assert ct.core.make_witness(full,full_inputs)==lw
                    assert len(full['variables'])==len(set(full['variables']))
                    cases.append({'h':h,'name':name,'mode':mode,'model':model})
    out={'status':'PASS','cases':len(cases),'subject_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
         for p in [SUB/'clean_targets.py',SUB/'check_clean_targets.py']},'details':cases}
    (HERE/'lift-name-collision-receipt.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='details'},indent=2))
if __name__=='__main__':main()
