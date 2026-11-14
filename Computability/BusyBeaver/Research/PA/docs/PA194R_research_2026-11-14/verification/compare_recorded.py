#!/usr/bin/env python3
"""Bind reconstructed machine outputs to independently recorded literal checks.

This inexpensive comparison performs no symbolic simulation. It compares exact
native/dense bytes and complete source/sites/labels objects, verifies the label
conjugacy and full finite-support seed, and binds each contract file to its
independent PASS receipt. Run the literal checkers to regenerate those receipts.
"""
from pathlib import Path
import argparse,hashlib,json
HERE=Path(__file__).resolve().parent;PACKAGE=HERE.parent
FAMILIES={'PA194R':{'PA194R'},'PA194F':{'PA194F'},'PA194A':{'PA194A','CSZ_A'},'PA194X':{'PA194X','CSZ_X'}}
sha=lambda b:hashlib.sha256(b).hexdigest()
def read_json(path):return json.loads(path.read_text())
def read_table(path):
    table={}
    for line in path.read_text().splitlines():
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert b in (0,1) and w in (0,1) and d in ('L','R') and (q,b) not in table
        table[q,b]=(w,d,t)
    return table

def compare(family,machines,recorded):
    built=machines/family;independent=recorded/family
    receipt=read_json(independent/'receipt.json');construction=read_json(built/'construction_receipt.json')
    assert receipt['family'] in FAMILIES[family] and construction['family']==family
    assert receipt['status']==construction['status']=='PASS'
    hashes={}
    for filename,key in [('machine.native.tm','native_sha256'),('machine.tm','dense_sha256')]:
        data=(built/filename).read_bytes()
        assert data==(independent/filename).read_bytes(),(family,filename,'literal bytes differ')
        h=sha(data);assert h==receipt[key]==construction[key]
        hashes[key]=h
    for filename in ['instructions.json','sites.json','labels.json']:
        assert read_json(built/filename)==read_json(independent/filename),(family,filename,'complete JSON objects differ')
    native=read_table(built/'machine.native.tm');dense=read_table(built/'machine.tm')
    labels=read_json(built/'labels.json')
    assert len(labels)==len(set(labels))==195 and labels[0]==74 and labels[-1]==254
    assert set(dense)=={(q,b) for q in range(194) for b in (0,1)}
    assert set(native)=={(q,b) for q in labels[:-1] for b in (0,1)}
    assert {(labels[q],b):(w,d,labels[t]) for (q,b),(w,d,t) in dense.items()}==native
    assert {t for w,d,t in native.values()}-set(labels[:-1])=={254}
    instructions=read_json(built/'instructions.json');sites=read_json(built/'sites.json')
    assert len(instructions)==len(sites)==receipt['source_sites']==3646
    assert receipt['working_states']==194 and receipt['transition_rows']==388
    contracts_path=independent/'contracts.json';contracts=read_json(contracts_path)
    assert sha(contracts_path.read_bytes())==receipt['contracts_sha256']
    expected={(i,p) for i,c in enumerate(instructions) for p in ([False,True] if c[0]=='dec' else [False])}
    assert len(contracts)==len(expected)==receipt['universal_source_outcomes']==4746
    assert {(c['site'],c['positive']) for c in contracts}==expected
    assert sum(c['symbolic_steps'] for c in contracts)==receipt['symbolic_steps']
    assert max(c['symbolic_steps'] for c in contracts)==receipt['maximum_symbolic_steps']
    assert min(c['duration'][0] for c in contracts)==receipt['minimum_positive_duration_constant']==3
    assert len(read_json(independent/'list_lemmas.json'))==4
    assert receipt['four_list_lemmas_rederived_from_literal_table'] is True and receipt['arithmetic_box_oracles'] is False
    a=read_json(built/'blank_seed.json');b=read_json(independent/'blank_seed.json')
    for key in ['steps','state','head','source_site','logical_registers','spare_values']:assert a[key]==b[key],(family,key)
    assert a['one_cells']==b['ones']
    assert a['complete_tape_equality'] is True and receipt['whole_blank_tape_equal'] is True
    assert a['steps']==receipt['startup_steps']
    reassociation={}
    if family=='PA194R':
        ancestor=machines/'PA194F'
        assert instructions==read_json(ancestor/'instructions.json')
        old_sites=read_json(ancestor/'sites.json')
        assert len(old_sites)==len(sites)
        assert all(old[1:]==new[1:] for old,new in zip(old_sites,sites))
        changed=sum(old[0]!=new[0] for old,new in zip(old_sites,sites))
        assert changed==receipt['changed_source_paths']==1111
        assert receipt['source_instruction_graph_equal_PA194F'] is True
        reassociation={'source_instruction_graph_equal_PA194F':True,'changed_source_paths':changed}
    return {'family':family,'status':'PASS',**hashes,
            'recorded_receipt_sha256':sha((independent/'receipt.json').read_bytes()),
            'native_and_dense_bytes_equal':True,'full_source_sites_labels_objects_equal':True,
            'dense_native_conjugacy_exact':True,'complete_blank_seed_equal':True,
            'contract_file_bound_to_receipt':True,'all_4746_source_outcomes_present_once':True,
            'startup_steps':a['steps'],'independent_family_label':receipt['family'],
            'symbolic_steps':receipt['symbolic_steps'],'maximum_symbolic_steps':receipt['maximum_symbolic_steps'],
            **reassociation}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--family',choices=list(FAMILIES)+['all'],default='all')
    ap.add_argument('--machines',type=Path,default=PACKAGE/'machines')
    ap.add_argument('--recorded',type=Path,default=HERE/'recorded')
    ap.add_argument('--output',type=Path,default=HERE/'recorded_comparison.json')
    a=ap.parse_args()
    results=[compare(family,a.machines,a.recorded) for family in FAMILIES if a.family in (family,'all')]
    result={'status':'PASS','comparisons':results,'scope':'Exact binding to recorded independent literal checks; no new symbolic replay or kernel theorem is claimed.'}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':
    if not __debug__:raise SystemExit('Assertions are required; do not use python -O.')
    main()
