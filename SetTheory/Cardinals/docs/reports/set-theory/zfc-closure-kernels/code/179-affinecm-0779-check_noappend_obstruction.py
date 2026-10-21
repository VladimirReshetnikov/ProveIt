#!/usr/bin/env python3
"""Concrete, independently replayed zero-decrement obstruction to the skeleton."""
from pathlib import Path
import json,hashlib
from search_existential_spares import parse,run,expect
from audit_spare_counterexamples import replay,table,source_output

def main():
    root=Path(__file__).resolve().parent;t=parse(root/'k215.tm');site=['0100','CD',0];regs=[0]*9;spares=[0];gap=0;mutation=((66,0),(0,-1,54))
    parent_ok,parent_steps,_,parent_output=run(t,site,regs,spares,gap,20000)
    ok,steps,used,actual=run(t,site,regs,spares,gap,20000,mutation)
    assert parent_ok and not ok and 'bound' not in actual and 189 not in used
    w={'site_index':2,'site':site,'registers':regs,'spares':spares,'gap':gap,'parent_steps':parent_steps,'parent_output':parent_output,'steps':steps,'actual':actual}
    independent=table(root/'k215.tm');assert replay(independent,w,parent_steps)==parent_output
    assert replay(independent,w,steps,mutation)==actual;want=source_output(site,regs)
    assert parent_output['pc_one_positions']==want[0] and parent_output['registers']==want[1]
    assert actual['pc_one_positions']!=want[0] or actual['registers']!=want[1]
    out={'status':'ZERO_DECREMENT_COUNTEREXAMPLE_INDEPENDENTLY_REPLAYED','changed_dense_row':[66,0,0,'L',54],'deleted_dense_state':189,'deleted_native_state':198,'skeleton_sha256':hashlib.sha256((root/'rejected_noappend214.native.tm').read_bytes()).hexdigest(),'witness':w,'expected_counter_one_positions':want[0],'expected_logical_registers':want[1],'scope':'Refutes the uniform first-clean-redispatch primitive contract on a valid dispatcher input. Does not exclude a later-redispatch existential contract. Makes no claim about this altered table\'s blank-run halting or Con(ZFC) equivalence.'}
    (root/'noappend_obstruction.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
