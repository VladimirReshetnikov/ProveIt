#!/usr/bin/env python3
"""Check affine lift against independent full cleaned-source witnesses."""
from pathlib import Path
import json
import clean_targets as ct
from check_clean_targets import check
from vendor import checker


def main():
    I,M=ct.Instruction,ct.Machine
    fixtures=[(M(('s','h'),'h',(I('s','h',op,c),)),'s',1,n)
              for op,c,n in [('inc',0,5),('inc',1,2),('dec',0,6),('dec',1,6),
                             ('zero',0,5),('zero',1,4),('zero',1,5),('positive',0,6),('positive',1,6),('nop',0,7)]]
    fixtures+=[(M(('h',),'h',()),'h',0,5),
               (M(('s','a','h'),'h',(I('s','a','inc',0),I('a','h','inc',1))),'s',2,5)]
    results=[]
    for machine,initial,h,n in fixtures:
        for model in ('native','spatial-radius-one','phase-radius-one'):
            for endpoint in (None,{'mode':'free'}):
                cert=ct.export_clean_certificate(machine,initial,h,{'mode':'fixed_raw','N':n},endpoint,model)
                w=ct.make_clean_witness(cert); naive,lifted=ct.lift_clean_witness(cert,w)
                if lifted != ct.core.make_witness(naive):raise AssertionError('lift differs from unique naive witness')
                r=checker.check(naive,lifted)
                if r['physical_time']!=check(cert,w)['physical_time']:raise AssertionError('clock differs')
                if any(lifted[v]!=w[v] for v in cert['variables']):raise AssertionError('forward restriction not inverse')
                results.append({'horizon':h,'N':n,'model':model,'time_output':endpoint is not None,
                                'compact_variables':len(w),'full_variables':len(lifted),'physical_time':r['physical_time']})
    machine,initial,h,n=fixtures[-1]
    for spec,inputs in [({'mode':'free_raw','name':'x'},{'x':4}),
                        ({'mode':'bounded_counters','A':2,'B':2},{'input_a':2,'input_b':1})]:
        cert=ct.export_clean_certificate(machine,initial,h,spec,{'mode':'free','name':'T'},'phase-radius-one')
        w=ct.make_clean_witness(cert,inputs);naive,lifted=ct.lift_clean_witness(cert,w)
        if lifted!=ct.core.make_witness(naive,inputs):raise AssertionError('input lift differs')
        checker.check(naive,lifted)
        results.append({'input_mode':spec['mode'],'compact_variables':len(w),'full_variables':len(lifted)})
    # New naive witness slots must not capture legal original interface names.
    for machine,initial,h,spec,inputs,output in [
        (M(('h',),'h',()),'h',0,{'mode':'free_raw','name':'e_0_0'},{'e_0_0':4},'u_1_1'),
        (M(('s','h'),'h',(I('s','h','inc'),)),'s',1,{'mode':'free_raw','name':'e_1_0'},{'e_1_0':4},'u_2_3'),
        (M(('s','h'),'h',(I('s','h','inc'),)),'s',1,
         {'mode':'bounded_counters','A':2,'B':2,'a_name':'e_1_0','b_name':'u_3_3'},
         {'e_1_0':1,'u_3_3':2},'u_2_3')]:
        cert=ct.export_clean_certificate(machine,initial,h,spec,{'mode':'free','name':output})
        w=ct.make_clean_witness(cert,inputs);naive,lifted=ct.lift_clean_witness(cert,w)
        checker.check(naive,lifted)
        naive_inputs={v:lifted[v] for v in naive['input_variables']}
        if lifted!=ct.core.make_witness(naive,naive_inputs):raise AssertionError('hygienic lift differs')
        results.append({'hygienic_interface_rename':True,'input_mode':spec['mode'],'horizon':h})
    receipt={'status':'passed','zero_fiber_bijection_cases':len(results),'cases':results,
             'qualification':'Affine lift preserves natural zero fibers; no global natural-map or off-zero polynomial identity is claimed.'}
    (Path(__file__).parent/'receipts'/'affine_lift.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='cases'},indent=2))

if __name__=='__main__':main()
