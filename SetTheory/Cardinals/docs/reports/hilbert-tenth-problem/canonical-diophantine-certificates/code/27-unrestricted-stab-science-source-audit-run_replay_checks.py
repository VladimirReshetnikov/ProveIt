#!/usr/bin/env python3
"""Fresh replay and adversarial-audit runner. Runs only this packet's fresh
builder and fresh checker. Prior builders/checkers are neither imported nor run.
"""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT/'source-audit'
BUILDER = ROOT/'build_stabilization.py'
CHECKER = AUDIT/'audit_source.py'


def require(condition,message):
    if not condition: raise RuntimeError(message)


def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def command(args,success=True):
    process = subprocess.run(args,cwd='/tmp',capture_output=True,text=True)
    require((process.returncode == 0) == success,'unexpected exit: '+' '.join(map(str,args))+'\n'+process.stderr)
    return {'argv':list(map(str,args)), 'cwd':'/tmp', 'returncode':process.returncode,
            'stderr_final_line':process.stderr.strip().splitlines()[-1] if process.stderr.strip() else None}


def main():
    records = []
    for mode,flags in [('normal',[]),('optimized',['-O'])]:
        output = AUDIT/('replay-'+mode)
        records.append(command([sys.executable,*flags,str(BUILDER),'--output',str(output)]))
        records.append(command([sys.executable,*flags,str(CHECKER),'--dag',str(output/'polynomial-dag.json'),
            '--builder',str(BUILDER),'--receipt',str(AUDIT/('replay-'+mode+'.audit.json'))]))
        require((output/'polynomial-dag.json').read_bytes() == (ROOT/'evidence/polynomial-dag.json').read_bytes(),mode+' DAG replay')
        require((output/'build-receipt.json').read_bytes() == (ROOT/'evidence/build-receipt.json').read_bytes(),mode+' builder receipt replay')
    require((AUDIT/'replay-normal.audit.json').read_bytes() == (AUDIT/'replay-optimized.audit.json').read_bytes(),'checker receipts optimization-invariant')
    base = json.loads((ROOT/'evidence/polynomial-dag.json').read_bytes())
    tests = []
    altered = copy.deepcopy(base)
    altered['gates'][-1][0] = '-'
    tests.append(('SOS_final_addition_changed',altered))
    altered = copy.deepcopy(base)
    altered['gates'][altered['body_gate_count']+1][2] = 'constant:1'
    tests.append(('SOS_square_changed',altered))
    altered = copy.deepcopy(base)
    altered['gates'][0][0] = '/'
    tests.append(('nonpolynomial_gate',altered))
    altered = copy.deepcopy(base)
    altered['gates'][0][1] = 'gate:1'
    tests.append(('forward_reference',altered))
    altered = copy.deepcopy(base)
    altered['gates'].append(['+','constant:0','constant:0'])
    tests.append(('extra_dead_gate',altered))
    altered = copy.deepcopy(base)
    altered['witnesses'].append('unpaid.deadWitness')
    tests.append(('extra_dead_witness',altered))
    altered = copy.deepcopy(base)
    eq = next(e for e in altered['equalities'] if e[2] == 'tile.convert.strideBound')
    eq[1] = eq[0]
    tests.append(('omitted_conversion_stride_constraint',altered))
    altered = copy.deepcopy(base)
    macro = next(m for m in altered['macros'] if m['name'] == 'supersolution.support')
    macro['mask'] = altered['ports']['interior_mask']
    tests.append(('binary_supersolution_mask_substituted',altered))
    altered = copy.deepcopy(base)
    macro = next(m for m in altered['macros'] if m['name'] == 'tile.convert')
    macro['value'] = altered['ports']['patch']
    tests.append(('wrong_conversion_input',altered))
    altered = copy.deepcopy(base)
    gate = altered['gates'][int(altered['ports']['balance_right'][5:])]
    six_times_u = altered['gates'][int(gate[1][5:])]
    require(six_times_u[0] == '*' and six_times_u[1] == 'constant:6','find balance coefficient')
    six_times_u[1] = 'constant:7'
    tests.append(('wrong_balance_coefficient',altered))
    altered = copy.deepcopy(base)
    eq = next(e for e in altered['equalities'] if e[2] == 'patch.shift.eq8')
    eq[1] = 'constant:0'
    tests.append(('wrong_degree_nine_Pell_residual',altered))
    results = []
    with tempfile.TemporaryDirectory(prefix='sandpile-source-audit-',dir='/tmp') as directory:
        tmp = Path(directory)
        for label,dag in tests:
            path = tmp/(label+'.json')
            path.write_text(json.dumps(dag,sort_keys=True,separators=(',',':'))+'\n')
            for mode,flags in [('normal',[]),('optimized',['-O'])]:
                result = command([sys.executable,*flags,str(CHECKER),'--dag',str(path),
                    '--builder',str(BUILDER),'--receipt',str(tmp/'should-not-exist.json')],False)
                require(not (tmp/'should-not-exist.json').exists(),'failed audit must not emit PASS receipt')
                result.update({'test':label,'mode':mode,'mutant_sha256':digest(path)})
                results.append(result)
    receipt = {
        'status':'PASS','builder_sha256':digest(BUILDER),'checker_sha256':digest(CHECKER),
        'runner_sha256':digest(Path(__file__)),'dag_sha256':digest(ROOT/'evidence/polynomial-dag.json'),
        'replay_runs':records,'byte_identical_replay':True,'optimization_invariant_checker':True,
        'mutation_cases':len(tests),'mutation_rejections':len(results),'mutations':results,
        'scope':'Only this newly authored builder and independently authored checker were executed; prior packets were read as inert text.'}
    (AUDIT/'replay-and-mutation-receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps({key:receipt[key] for key in ('status','dag_sha256','mutation_cases','mutation_rejections')},indent=2))


if __name__ == '__main__': main()
