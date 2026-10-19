#!/usr/bin/env python3
"""Extend the verified K227 recipe by one exact duplicate-state quotient.

The first closed rotation exposes two literally identical decoder states.
Five further closed rotations repair the source address budget. The complete
unbounded native and Rocq runtime checks are separate proof artifacts.
"""
from pathlib import Path
import argparse,json
import build227 as b
g=b.g;HERE=Path(__file__).resolve().parent
REPAIRS=[(101,209,'left'),(101,208,'left'),(226,224,'right'),(205,134,'left'),(207,205,'right')]
FINAL_TABLE='6f5a35c58961c77baf595ab743a185f4df6815aaaceb89a5b1494521b96f1d6c'
FINAL_SOURCE='47f5cfac0ec765c6f84f9d29973d4c9b3d79f12482a2cd1268d582e85c814bd3'
FINAL_CANONICAL='b58279b8b2e2cf029dd94e084d47cd6097772d7bce2a62653767895123d29599'
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--base',type=Path,default=HERE/'generated/05_k227');ap.add_argument('--out',type=Path,default=HERE/'generated226');a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    assert b.sha(a.base/'table_k230labels.tm')==b.FINAL_TABLE and b.sha(a.base/'sites.json')==b.FINAL_SOURCE
    table=b.read_table(a.base/'table_k230labels.tm');root=g.tree(json.loads((a.base/'sites.json').read_text()));reference=g.graph(g.sites(root))[1:]
    root,table,c=g.stage(root,table,85,65,'left')
    assert g.graph(g.sites(root))[1:]==reference
    assert table[65,0]==table[98,0]==(0,1,19) and table[65,1]==table[98,1]==(1,1,114)
    stages=[b.save_stage(a.out,'00_duplicate_basis227',root,table,{'status':'CLOSED_ROTATION_EXPOSES_LITERAL_DUPLICATE','rotation':c})]
    old=dict(table);phi=lambda q:98 if q==65 else q
    table={(q,bit):(w,d,phi(z)) for(q,bit),(w,d,z) in old.items() if q!=65}
    # Verify the exact one-step quotient on both rows of every old state,
    # including the removed state, with no context or tape hypotheses.
    for(q,bit),(w,d,z) in old.items():assert table[phi(q),bit]==(w,d,phi(z))
    assert len(table)==452
    quotient={'status':'TOTAL_LITERAL_TRANSITION_QUOTIENT_PASS','map_nonidentity':{'65':98},'checked_rows':454,'deleted_state':65,'retained_state':98,'identical_rows':{'0':[0,1,19],'1':[1,1,114]},'scope':'One-step bisimulation on arbitrary tapes; start0 and halt230 are fixed by the map.'}
    (a.out/'duplicate_quotient.json').write_text(json.dumps(quotient,indent=2)+'\n')
    stages.append(b.save_stage(a.out,'01_unrepaired226',root,table,{'status':'EXACT_QUOTIENT_ADDRESS_REPAIR_PENDING','quotient':quotient}))
    rotations=[]
    for number,(q,q2,direction) in enumerate(REPAIRS,1):
        root,table,cert=g.stage(root,table,q,q2,direction);assert g.graph(g.sites(root))[1:]==reference;rotations.append(cert)
        stages.append(b.save_stage(a.out,f'repair_{number}',root,table,{'status':'ALL_6656_SOURCE_GUARDS_PRESERVED','rotation':cert}))
    final=b.save_stage(a.out,'02_k226',root,table,{'status':'EXACT_K226_CONSTRUCTION','address_repairs':rotations,'guarded_cases':6656})
    assert final['table_sha256']==FINAL_TABLE and final['source_sha256']==FINAL_SOURCE
    assert final['metrics']=={'dag_nodes':211,'leaf_occurrences':5121,'maximum_depth':41,'maximum_zero_run':6}
    order=sorted({q for q,bit in table});renumber={q:i for i,q in enumerate(order)}|{230:226}
    canonical={(renumber[q],bit):(w,d,renumber[z]) for(q,bit),(w,d,z) in table.items()}
    (a.out/'02_k226/k226.tm').write_text(b.encode(canonical));assert b.sha(a.out/'02_k226/k226.tm')==FINAL_CANONICAL
    (a.out/'02_k226/renumbering.json').write_text(json.dumps({'k230_to_k226':renumber},indent=2)+'\n')
    original=b.read_table(HERE/'inputs/k230.tm')
    report={'status':'EXACT_K226_SOURCE_AND_TABLE_PASS','working_states':226,'transition_rows':452,
      'deleted_k230_states':sorted({q for q,bit in original}-{q for q,bit in table}),
      'changed_surviving_rows_vs_k230':sum(original[row]!=table[row] for row in table),
      'source_metrics':g.metrics(root),'guarded_cases':6656,'input_table_sha256':b.PIN_TABLE,'input_source_sha256':b.PIN_SITES,
      'final_table_k230labels_sha256':FINAL_TABLE,'final_table_canonical_sha256':FINAL_CANONICAL,'final_source_sha256':FINAL_SOURCE,
      'extension_closed_rotations':6,'extension_duplicate_quotients':1,'quotient':quotient,'stages':stages,
      'scope':'Exact source/table/duplicate-state certificates. Full native runtime, startup and consistency calibration are checked separately.'}
    (a.out/'construction.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in('stages','quotient')},indent=2))
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Run with assertions enabled')
    main()
