"""Regenerate examples and check both standalone interfaces and compiler edges."""
from pathlib import Path
import copy
import hashlib
import json
import subprocess
import sys
import time
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'code'))
import compiler as C
import atomic_alias as K
import build_examples as B
from measure import measure


def run(module, data, optimized=False):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT/module)]
    result = subprocess.run(command, input=json.dumps(data), text=True,
                            capture_output=True, timeout=20)
    return result.returncode == 0 and result.stdout.strip() == 'ACCEPT'


def record_case(records, name, data, expected, modules):
    for module in modules:
        for optimized in (False, True):
            actual = run(module, data, optimized)
            if actual != expected:
                raise RuntimeError((name, module, optimized, expected, actual))
            records.append({'case':name,'module':module,'optimized':optimized,
                            'accepted':actual})


def open_compiler_examples():
    rows = []
    for body_depth in (0, 1, 2):
        higher = B.box(-1, 2)
        body = [1, 1] if body_depth == 0 else B.abstract(B.box('y',body_depth),'y')
        sc = [([], [-1,-2]), (higher,body), ([],higher)]
        sp = ['u',1,-2,['u',2,0,None]]
        mapping = {-1:-3,-2:-1}
        positions = [3,1,4]
        dummy = ([],[0,0])
        tc = [dummy, tuple(C.rename(a,mapping) for a in sc[1]), dummy,
              tuple(C.rename(a,mapping) for a in sc[0]),
              tuple(C.rename(a,mapping) for a in sc[2]), dummy]
        tp = C.compile_source(sp,sc,2,tc,4,mapping,positions)
        expected = C.rename(C.S.derive(sp,sc,2),mapping)
        if K.derive(tp,tc,4) != expected:
            raise RuntimeError('open compiler example failed')
        rows.append({'body_depth':body_depth,'antecedent_depth':2,
                     'source_context':sc,'source_scope':2,'source_proof':sp,
                     'target_context':tc,'target_scope':4,
                     'mapping':mapping,'clause_positions':positions,
                     'target_goal':expected,'target_proof':tp})
    return rows


def negative_examples():
    name0 = C.name(0)
    n = name0.formula
    alias_compound = {'goal':n,'proof':['a',0,name0.proof([([],[-1,0])],1)]}
    body = C.op(n[0],-1,2)
    ctx = [(C.op(body,0),body)]
    eq = C.name_equality(0,0,-1).proof(ctx,1)
    back_compound = {'goal':n,'proof':['e',n,name0.proof([],0),
        ['v',n,eq,name0.proof(ctx,1)]]}
    wrong_newest = {'goal':[0,0], 'proof':['a',0,['a',0,
        ['v',[-1,0],['u',0,None],C.reflexivity(0).proof([([],[-1,0]),([],[-2,0])],2)]]]}
    rows = {'compound_alias_forbidden':alias_compound,
            'compound_back_forbidden':back_compound,
            'old_parameter_back_forbidden':wrong_newest,
            'future_alias_capture':{'goal':[0,0],'proof':['a',-1,['u',0,None]]},
            'false_conclusion':{'goal':[0,[0,0]],'proof':C.reflexivity(0).proof([],0)},
            'boolean_zero':{'goal':[False,False],'proof':C.reflexivity(False).proof([],0)},
            'string_zero':{'goal':['0','0'],'proof':C.reflexivity('0').proof([],0)},
            'unbound_parameter':{'goal':[-1,-1],'proof':C.reflexivity(-1).proof([],0)},
            'wrong_successor_tag':{'goal':[[0,0,1],0],'proof':['c',[1,0],0,1]},
            'extra_use_field':{'goal':[0,0],'proof':['a',0,['u',0,0,None]]},
            'missing_instruction_arguments':{'goal':[0,0],'proof':['a']},
            'missing_goal':{'proof':['c',0,0,0]},
            'extra_top_field':{'goal':[0,0],'proof':C.reflexivity(0).proof([],0),'extra':0}}
    return rows


def audit_atomic(proof):
    """Inspect every EqBack target syntactically; replay enforces EqAlias too."""
    if type(proof) is not list or not proof:
        return
    if proof[0] == 'v' and len(proof[1]) != 2:
        raise RuntimeError('compiler generated compound Back')
    for child in proof[1:]:
        if type(child) is list and child and type(child[0]) is str:
            audit_atomic(child)


def main():
    started = time.monotonic()
    B.main()
    modules = ['code/atomic_alias.py','code/atomic_alias_small.py']
    records = []
    compiled = []
    for path in sorted((ROOT/'source_tests').glob('*.json')):
        source = json.loads(path.read_text())
        target = C.translate(source)
        audit_atomic(target['proof'])
        (ROOT/'tests'/path.name).write_text(json.dumps(target,separators=(',',':'))+'\n')
        compiled.append({'case':path.stem,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                         'target_bytes':len(json.dumps(target,separators=(',',':')).encode())+1})
        record_case(records,path.stem,target,True,modules)
    negatives = negative_examples()
    (ROOT/'tests'/'negative_cases.json').write_text(json.dumps(negatives,indent=2)+'\n')
    for label,case in negatives.items():
        record_case(records,label,case,False,modules)
    # The new literal-equation restrictions have observable effects on proofs.
    controls = ['controls/general_alias.py','controls/general_alias_small.py']
    for label in ('compound_alias_forbidden','compound_back_forbidden'):
        record_case(records,label+'_control',negatives[label],True,controls)
    open_rows = open_compiler_examples()
    (ROOT/'evidence'/'open_examples.json').write_text(json.dumps(open_rows,separators=(',',':'))+'\n')
    metrics = {p:measure(ROOT/p) for p in modules+controls+['controls/template_source.py']}
    result = {'python':sys.version,'source_compilations':compiled,
              'standalone_executions':len(records),'results':records,
              'open_compiler_cases':len(open_rows),'metrics':metrics,
              'elapsed_seconds':round(time.monotonic()-started,3),
              'status':'All expected acceptances and rejections observed; finite tests are not a metatheorem proof.'}
    (ROOT/'evidence'/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    (ROOT/'evidence'/'metrics.json').write_text(json.dumps({'python':sys.version,'metrics':metrics},indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('standalone_executions','open_compiler_cases','metrics','elapsed_seconds')},indent=2))


if __name__ == '__main__':
    main()
