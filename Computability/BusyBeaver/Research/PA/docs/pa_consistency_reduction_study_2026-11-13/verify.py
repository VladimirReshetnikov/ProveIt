#!/usr/bin/env python3
"""Offline exact checks for the comparison and scoped obstruction package.

No solver, Git checkout, network access, Lean or Rocq is required.
This does not certify a sub-194 consistency machine.
"""
from pathlib import Path
from collections import Counter
import hashlib,importlib.util,json,subprocess,sys,time
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def main():
    if not __debug__:raise RuntimeError('Assertions must be enabled; do not use -O.')
    started=time.monotonic()
    manifest=ROOT/'SHA256SUMS'
    if not manifest.exists():raise RuntimeError('Release hash manifest missing.')
    hashes=0
    for line in manifest.read_text().splitlines():
        want,name=line.split('  ',1);p=ROOT/name
        assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==want,('hash mismatch',name)
        hashes+=1
    print('Release hashes:',hashes,'PASS',flush=True)
    mc=module('catalogue_classifier',ROOT/'verification/machine_classes.py')
    idx=json.loads((ROOT/'inputs/catalogue_index.json').read_text())
    counts=Counter();classes=set()
    for i,row in enumerate(idx):
        data=(ROOT/row['local_file']).read_bytes()
        assert hashlib.sha256(data).hexdigest()==row['sha256']
        got=mc.classify(data)
        assert got['states']==row['states'] and got['table']==row['table_class']
        assert got['start']==row['start'] and got['halting']==row['halt_labels']
        assert got['reachable']==(row['max_reachable'] if row['start']is None else row['start_reachable'])
        classes.add(got['table']);counts[got['states']]+=1
    assert len(idx)==len(classes)==535 and counts[194]==49 and counts[193]==1
    print('Retained catalogue:535 classes,49 with194states,one rejected193 PASS',flush=True)
    proof=module('factor3_verifier',ROOT/'verification/factor3/verify_primitive.py')
    p=proof.verify(ROOT/'verification/factor3/primitive_proof.json')
    assert p['primitive_proof_steps']==73393 and p['arithmetic_terms']==116171 and p['final_conclusion']==1
    print('Rejected coefficient-three primitive refutation: PASS',flush=True)
    helper=subprocess.run([sys.executable,str(ROOT/'verification/helper_obstruction/verify_helper_obstruction.py')],check=True,capture_output=True,text=True)
    h=json.loads(helper.stdout)
    assert h['verified'] and h['exact_final_state_lower_bound']==194
    print('Frozen raw-action selector-family exact dual: PASS',flush=True)
    rot=module('rotation_verifier',ROOT/'verification/check_rotations.py').verify()
    print('Exact source reassociation: PASS_SOURCE_ONLY',flush=True)
    grammar=module('grammar_verifier',ROOT/'verification/grammar/verify_grammar.py').verify()
    print('Cost-67 dictionary feasible witness: PASS (optimality not checked)',flush=True)
    out={'status':'PASS','hashes_checked':hashes,'catalogue_classes':535,'frontier194_classes':49,'factor3_refutation':p,'frozen_helper_obstruction':h,'source_rotations':rot,'grammar_witness':grammar,'seconds':time.monotonic()-started,'accepted_sub194_machine':False,'scope':'Exact comparison inputs and scoped certificates. No general state lower bound and no new consistency machine.'}
    print(json.dumps(out,indent=2))
    return out

if __name__=='__main__':main()
