#!/usr/bin/env python3
"""Check the affine-on-zero-fibers compact-to-full witness lift independently."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import importlib.util,json
HERE=Path(__file__).resolve().parent
SUB=HERE.parent
spec=importlib.util.spec_from_file_location('lift_clean_subject',SUB/'clean_targets.py')
ct=importlib.util.module_from_spec(spec);sys.modules[spec.name]=ct;spec.loader.exec_module(ct)
spec=importlib.util.spec_from_file_location('lift_forward_checker',SUB/'vendor/checker.py')
checker=importlib.util.module_from_spec(spec);sys.modules[spec.name]=checker;spec.loader.exec_module(checker)
I,M=ct.Instruction,ct.Machine

def lifted(original, w, full):
    h=original['horizon'];B=len(original['branches'])
    out={name:0 for name in full['variables']}
    # Preserve true input coordinates and the complete original input loader.
    core_vars={v for row in original['steps'] for b in row for v in (b['e'],b['u'])}
    for v in original['variables']:
        if v not in core_vars:out[v]=w[v]
    for t in range(h):
        for j in range(B):
            for name in ('e','u'):
                value=w[f'{name}_{t}_{j}']
                out[f'{name}_{t}_{j}']=value
                out[f'{name}_{2*h-t}_{B+j}']=value
    N0=ct.core.evaluate_affine(original['initial_N'],w)
    Nh=ct.core.evaluate_affine(original['final_N'],w)
    out[f'e_{h}_{2*B}']=1;out[f'u_{h}_{2*B}']=Nh-1
    out[f'e_{2*h+1}_{2*B+1}']=1;out[f'u_{2*h+1}_{2*B+1}']=N0-1
    assert min(out.values(),default=0)>=0
    return out

def main():
    cases=[]
    for machine,q0,h in [
        (M(('h',),'h',()),'h',0),
        (M(('s','h'),'h',(I('s','h','inc',1),)),'s',1),
        (M(('s','h'),'h',(I('s','h','zero',1),)),'s',1),
        (M(('s','a','h'),'h',(I('s','a','inc',0),I('a','h','dec',0))),'s',2),
    ]:
        for inp,free in [({'mode':'fixed_raw','N':5},{}),({'mode':'free_raw','name':'x'},{'x':4}),
             ({'mode':'bounded_counters','A':2,'B':1,'a':None,'b':0},{'input_a':1})]:
            orig=ct.core.export_certificate(machine,q0,h,inp)
            w=ct.core.make_witness(orig,free)
            wm,wi=ct.clean_source(machine,q0)
            for scale in (1,4):
                full=ct.core.export_certificate(wm,wi,2*h+2,inp,clock_scale=scale)
                lw=lifted(orig,w,full)
                independent=checker.check(full,lw)
                assert lw==ct.core.make_witness(full,free)
                assert ct.core.polynomial_value(full,lw)==0
                N0=ct.core.evaluate_affine(orig['initial_N'],w)
                Nh=ct.core.evaluate_affine(orig['final_N'],w)
                theta=ct.core.evaluate_affine(orig['physical_time'],w)
                assert independent['physical_time']==scale*(2*theta+192*(N0+Nh)+16)
                assert independent['final_N']==N0
                # Projection by F-copy slots recovers every original core variable.
                assert all(lw[v]==w[v] for row in orig['steps'] for b in row for v in (b['e'],b['u']))
                cases.append({'h':h,'B':len(orig['branches']),'input_mode':inp['mode'],'clock_scale':scale,
                              'original_core_variables':orig['ledger']['core_variables'],
                              'full_core_variables':full['ledger']['core_variables']})
    result={'status':'PASS','zero_fiber_lift_cases':len(cases),'cases':cases,
            'scope':'Lift and inverse projection on natural zero fibers; no off-zero polynomial identity or globally natural affine map claimed'}
    (HERE/'witness-lift-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','cases':len(cases)},indent=2))
if __name__=='__main__':main()
