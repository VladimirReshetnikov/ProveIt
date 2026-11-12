"""Finite complete-program checks, canonical corpus conversion, and metrics."""
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TESTS = ROOT/'tests'
sys.path.insert(0,str(TESTS))
import producer
from convert import convert


def load_module(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def run(path,packet,optimized=False,raw=False):
    result=subprocess.run([sys.executable]+(['-O'] if optimized else [])+[str(path)],
        input=packet if raw else json.dumps(packet),capture_output=True,text=True,timeout=20)
    accepted=result.returncode==0 and result.stdout.strip()=='ACCEPT'
    protocol=accepted or (result.returncode!=0 and result.stdout.strip()=='REJECT')
    return {'accepted':accepted,'protocol':protocol,'exit_code':result.returncode}


def main():
    cases=producer.build_cases()+producer.witness_boundary_cases()
    excluded={'two_child_counter_constant_update','three_child_counter_constant_update'}
    cases=[c for c in cases if c['name'] not in excluded]
    # The old raw wrappers are now predecessor terms, not submitted successor
    # constructors. Their prior negative labels therefore do not transfer.
    for c in cases:
        if c['name']=='IS_constant_update':
            c['meaning']='Constant update; the recursive image is unused and need not be eagerly traversed.'
    def add(name,packet,accept,meaning):
        cases.append({'name':name,'packet':packet,'accept':accept,'meaning':meaning})
    add('successor_zero_explicit_mode',[[0,[0,[0],1],1,0],[[[0],[0],1],[0,[0],1]]],True,
        'Step at zero predecessor, with a used recursive state and explicit step mode.')
    add('binary_zero_predecessor_is_legal',[[0,[[0,0],0,[0]],1,0],[[[[0,0]],0,[0]],[0]]],True,
        'A checked binary numerical-zero alias is a legal predecessor; the kernel builds its successor.')
    add('iterator_predecessor_is_legal',[[0,[[0,0,0],0,[0]],1,0],[[[[0,0,0]],0,[0]],[0]]],True,
        'A scalar iterator is a legal predecessor; no input successor-shape restriction is imposed.')
    add('legacy_binary_wrapper_exploit_rejected',[[0,[[0,0],0,[0]],1,0],[[[0,0],0,[0]],[0]]],False,
        'Requested I(0,0;v.1)=1 is false. The constructed source has a successor and cannot supply this equation.')
    add('missing_successor_exploit_rejected',[[0,[0,0,[0]],1,0],[[0,0,[0]],[0]]],False,
        'Omitting the constructed successor would falsely certify I(0,0;v.1)=1.')
    add('inert_base_predecessor_payload',[[0,[{'unused':True},[0],0],0,0],[[0,[0],0],[0]]],True,
        'Base mode ignores its predecessor field; its constructed equation remains I(0,1;v.0)=1.')
    add('future_label_in_demanded_state_rejected',[[0,[-1,0,1],1,0],[[[-1],0,1],[-1,0,1]]],False,
        'An unallocated free label in the requested theorem is rejected before fresh allocation.')
    (TESTS/'cases.json').write_text(json.dumps({'scope':'Finite certificates, not a formal metatheorem.','cases':cases},indent=2)+'\n')
    (TESTS/'fixtures').mkdir(exist_ok=True)
    for c in cases:
        (TESTS/'fixtures'/(c['name']+'.json')).write_text(json.dumps(c['packet'],indent=2)+'\n')
    records=[]
    for kernel in ['code/checker.py','code/readable_checker.py']:
        for optimized in [False,True]:
            for c in cases:
                r=run(ROOT/kernel,c['packet'],optimized)
                records.append({'kernel':kernel,'optimized':optimized,'case':c['name'],'expected':c['accept'],**r,
                    'passed':r['protocol'] and r['accepted']==c['accept']})
            for name,payload in [('empty_input',''),('malformed_json','{broken'),('non_array_root','{}')]:
                r=run(ROOT/kernel,payload,optimized,True)
                records.append({'kernel':kernel,'optimized':optimized,'case':name,'expected':False,**r,
                    'passed':r['protocol'] and not r['accepted']})
    mutants=[
        ('successor_constructor','[[u and [n], t, r]','[[n, t, r]',
         next(c for c in cases if c['name']=='missing_successor_exploit_rejected')['packet']),
        ('major_proof_check','        c(m, g)\n','',
         [[0,[0,0,0],0,0],[[0,[0]],0,[0],[[0,0,0],1]],[[0,0,0],[0]]]),
        ('literal_equation_progress','len(a) % 2 == m','m == 0',
         next(c for c in cases if c['name']=='forbidden_compound_progress')['packet'])]
    mutation_results=[]
    source=(ROOT/'code/checker.py').read_text()
    with tempfile.TemporaryDirectory() as tmp:
        for name,old,new,packet in mutants:
            if source.count(old)!=1:raise ValueError(name)
            path=Path(tmp)/(name+'.py');path.write_text(source.replace(old,new))
            genuine=run(ROOT/'code/checker.py',packet);mutant=run(path,packet)
            mutation_results.append({'name':name,'genuine':genuine,'mutant':mutant,
              'passed':genuine['protocol'] and mutant['protocol'] and not genuine['accepted'] and mutant['accepted']})
    measure=load_module(ROOT/'reference/source_measure.py','source_measure')
    metrics=[{'file':p,**measure.metrics(ROOT/p)} for p in ['code/checker.py','code/readable_checker.py','reference/old_checker.py','reference/old_checker_ast.py','reference/old_folded.py']]
    compact=metrics[0];floor={'normalized_tokens':281,'ast_nodes':315,'normalized_bytes':685}
    if not all(compact[key]<bound for key,bound in floor.items()):raise ValueError('Metric target failed')
    receipt={'python':platform.python_version(),'scope':'Finite checking, not proof-assistant verification.',
      'source_sha256':hashlib.sha256((ROOT/'code/checker.py').read_bytes()).hexdigest(),
      'current_coordinate_envelope':floor,'metrics':metrics,'cases':len(cases),
      'certificate_and_input_runs':len(records),'passed':sum(r['passed'] for r in records),
      'legacy_counter_shape_negatives_replaced':sorted(excluded),'results':records,'mutations':mutation_results}
    (ROOT/'evidence/verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    failures=[r for r in records+mutation_results if not r['passed']]
    print(json.dumps({'cases':len(cases),'runs':len(records),'passed':receipt['passed'],'mutations':mutation_results,'failures':failures,
        'metrics':[{k:r[k] for k in ('file','normalized_tokens','ast_nodes','normalized_bytes')} for r in metrics]},indent=2))
    if failures:raise SystemExit(1)

if __name__=='__main__':main()
