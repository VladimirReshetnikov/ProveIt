"""Finite complete-program tests and independent boundary controls."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CHECKERS = ['code/checker.py','code/readable_checker.py',
            'ancillary/checker_bytes.py','ancillary/checker_ast.py']

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    result=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result

def accepted(path,packet,optimized=False,raw=False):
    run=subprocess.run([sys.executable]+(['-O'] if optimized else [])+[str(path)],
                       input=packet if raw else json.dumps(packet),text=True,
                       capture_output=True,timeout=20)
    return run.returncode == 0 and run.stdout == 'ACCEPT\n', run.returncode

def verify(write=False):
    producer=module('new_producer',ROOT/'tests/producer.py')
    cases=json.loads(json.dumps(producer.build_cases()))
    distributed=json.loads((ROOT/'tests/cases.json').read_text())['cases']
    if cases!=distributed:
        raise ValueError('Named producer does not reproduce delivered cases')
    for case in cases:
        if json.loads((ROOT/'tests/fixtures'/(case['name']+'.json')).read_text())!=case['packet']:
            raise ValueError('Changed fixture '+case['name'])
    rows=[]
    for filename in CHECKERS:
        for case in cases:
            for optimize in (False,True):
                actual,status=accepted(ROOT/filename,case['packet'],optimize)
                rows.append(dict(checker=filename,case=case['name'],optimized=optimize,
                                 expected=case['accept'],actual=actual,exit_status=status))
                if actual!=case['accept']:
                    raise AssertionError(rows[-1])
    malformed=[]
    for raw in ('{','null','[]','{}','"text"','[null]'):
        for filename in CHECKERS:
            actual,status=accepted(ROOT/filename,raw,raw=True)
            malformed.append(dict(checker=filename,input=raw,accepted=actual,exit_status=status))
            if actual:
                raise AssertionError(malformed[-1])
    original=(ROOT/'code/checker.py').read_text()
    byname={c['name']:c for c in cases}
    mutation_specs=[
        ('unwrapped_successor_source','s and [s]','s',
         [[None,[0,0],[0],0],[[[0,0],[0],0],0]]),
        ('unrestricted_compound_progress','len(a) % 2 == m','not m',
         byname['forbidden_compound_progress']['packet']),
        ('future_parameter_scope','k <= a < d','a < d',
         [[None,0,-1,0],[[0,-1,0],-1]]),
    ]
    mutations=[]
    with tempfile.TemporaryDirectory(prefix='ipra-controls-') as temporary:
        for label,before,after,packet in mutation_specs:
            if original.count(before)!=1:
                raise ValueError('Mutation anchor drift')
            path=Path(temporary)/(label+'.py');path.write_text(original.replace(before,after))
            real,_=accepted(ROOT/'code/checker.py',packet)
            mutant,_=accepted(path,packet)
            mutations.append(dict(name=label,primary_accepts=real,mutant_accepts=mutant))
            if real or not mutant:
                raise AssertionError(mutations[-1])
    numerical=module('numerical_audit',ROOT/'tests/numerical_audit.py').audit()
    old=module('old_flat_producer',ROOT/'reference/flat_producer.py')
    old_cases={c['name']:c for c in old.build_cases()}
    comparison=[]
    for case in cases:
        if case['accept'] and 'proof_tree' in case and case['name'] in old_cases:
            previous=old_cases[case['name']]
            old_ok,_=accepted(ROOT/'reference/baseline_flat.py',previous['packet'])
            new_ok,_=accepted(ROOT/'code/checker.py',case['packet'])
            if not old_ok or not new_ok:
                raise AssertionError('Certificate comparison must check both programs')
            comparison.append(dict(name=case['name'],old_commands=len(previous['packet'])-1,
                                   new_commands=len(case['packet'])-1,
                                   old_json_bytes=len(json.dumps(previous['packet'],separators=(',',':'))),
                                   new_json_bytes=len(json.dumps(case['packet'],separators=(',',':')))))
    result={'scope':'Finite implementation evidence, not a formal metatheorem.',
            'python':sys.version,'cases':len(cases),'positive_cases':sum(c['accept'] for c in cases),
            'complete_program_runs':len(rows),'malformed_runs':len(malformed),
            'mutations':mutations,'numerical':numerical,
            'certificate_comparison_runs':2*len(comparison),
            'source_hashes':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in CHECKERS},
            'rows':rows,'malformed':malformed}
    if write:
        (ROOT/'evidence/validation.json').write_text(json.dumps(result,indent=2)+'\n')
        (ROOT/'evidence/certificate_comparison.json').write_text(json.dumps(comparison,indent=2)+'\n')
        (ROOT/'evidence/validation_summary.tex').write_text(
            f"All {len(rows)} complete-program expectations passed ({len(cases)} cases, four implementations, ordinary and optimized Python). "
            f"The suite also passed {len(malformed)} malformed-input runs and three targeted mutation controls. "
            f"Both old and new encodings were executed in {2*len(comparison)} certificate-comparison runs. "
            f"The independent arithmetic diagnostic attempted {numerical['attempted']:,} packets, generated {numerical['generated']:,} equations, "
            f"and checked {numerical['evaluated']:,} parameter valuations; it found zero counterexamples and recorded {numerical['budget_skips']:,} evaluation-budget skips.\n")
    return {k:v for k,v in result.items() if k not in ('rows','malformed')}

if __name__ == '__main__':
    print(json.dumps(verify('--write' in sys.argv),indent=2))
