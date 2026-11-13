"""Finite executable checks, not a formal soundness or completeness proof."""
import ast
import copy
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

HERE=Path(__file__).resolve().parent
IGNORED={tokenize.ENCODING,tokenize.COMMENT,tokenize.NL,tokenize.NEWLINE,tokenize.INDENT,tokenize.DEDENT,tokenize.ENDMARKER}

class StripDocstrings(ast.NodeTransformer):
    def clean(self,node):
        self.generic_visit(node)
        if node.body and isinstance(node.body[0],ast.Expr) and isinstance(node.body[0].value,ast.Constant) and isinstance(node.body[0].value.value,str):node.body=node.body[1:]
        return node
    visit_Module=visit_FunctionDef=visit_AsyncFunctionDef=visit_ClassDef=clean

def metrics(path):
    raw=Path(path).read_bytes()
    tree=ast.fix_missing_locations(StripDocstrings().visit(ast.parse(raw.decode())))
    text=ast.unparse(tree)+'\n'
    return dict(normalized_tokens=sum(t.type not in IGNORED for t in tokenize.generate_tokens(io.StringIO(text).readline)),ast_nodes=sum(1 for _ in ast.walk(tree)),normalized_bytes=len(text.encode()),raw_bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())

def negative_cases(positive):
    byname={c['name']:c['packet'] for c in positive}
    out=[]
    def add(name,packet):out.append(dict(name=name,accept=False,packet=packet))
    add('false_zero_equals_one',[[0,0,0,0],[0,[0]]])
    add('wrong_seed_value',[[0,0,0,0],[[0,0,0],0]])
    add('successor_wrong_update',[[0,0,0,0],[[[0],0,3],[0]]])
    add('non_successor_binary_counter',[[0,0,0,0],[[[0,0],0,[0]],[0]]])
    add('non_successor_ternary_counter',[[0,0,0,0],[[[0,0,0],0,[0]],[0]]])
    add('unbound_negative_goal',[[0,0,0,0],[-1,-1]])
    add('unbound_positive_goal',[[0,0,0,0],[1,1]])
    add('malformed_goal_arity',[[0,0,0,0],[0,0,0,0]])
    add('malformed_goal_mapping',[[0,0,0,0],{'a':0}])
    add('malformed_goal_string',[[0,0,0,0],'formula'])
    add('empty_certificate',[])
    add('missing_computation_packet',[copy.deepcopy(byname['R_zero'][-1])])
    add('packet_wrong_arity',[[0,0],copy.deepcopy(byname['R_zero'][-1])])
    p=copy.deepcopy(byname['reflexivity_zero']);p[-2][2]=[0]
    add('transport_target_mismatch',p)
    p=copy.deepcopy(byname['reflexivity_zero']);p[-2][1]=[0]
    add('transport_source_mismatch',p)
    p=copy.deepcopy(byname['reflexivity_zero']);p[-2][0]=[0,[0]]
    add('unproved_transport_major',p)
    p=copy.deepcopy(byname['DE_QE'])
    ix=next(j for j,z in enumerate(p[:-1]) if isinstance(z[0],list) and len(z[0])==1)
    p[ix][1]=[0]
    add('closure_nonzero_source',p)
    p=copy.deepcopy(byname['DE_witness_transport'])
    ix=next(j for j,z in enumerate(p[:-1]) if not z[0] and z[3])
    p[ix][3]=-1
    add('future_eigenparameter_witness',p)
    p=copy.deepcopy(byname['DI_progress_uses_hypothesis'])
    p[-2][0]=[]
    add('case_mode_cannot_replace_used_progress',p)
    return out

def run(kernel,packet,opt=False):
    command=[sys.executable]
    if opt:command+=['-O']
    command+=[str(kernel)]
    try:
        r=subprocess.run(command,input=json.dumps(packet),capture_output=True,text=True,timeout=10)
    except subprocess.TimeoutExpired:
        return dict(accept=False,timeout=True,verdict='',exit_code=None)
    return dict(accept=r.returncode==0 and r.stdout.strip()=='ACCEPT',timeout=False,verdict=r.stdout.strip(),exit_code=r.returncode)

def main():
    profiles=[('focused','kernel_counter.py'),('unfocused','control_counter.py')]
    results=[]
    metrics_rows=[]
    for name,file in profiles:
        kernel=HERE/file
        positives=json.loads((HERE.parent/'fixtures'/f'{name}.json').read_text())['cases']
        negatives=negative_cases(positives)
        (HERE.parent/'fixtures'/f'{name}_negative.json').write_text(json.dumps(dict(cases=negatives),indent=2)+'\n')
        for opt in (False,True):
            for c in positives+negatives:
                result=run(kernel,c['packet'],opt)
                success=result['accept']==c['accept'] and not result['timeout']
                results.append(dict(profile=name,optimized=opt,name=c['name'],expected=c['accept'],passed=success,**result))
        metrics_rows.append(dict(profile=name,file=file,**metrics(kernel)))
    summary=dict(python=sys.version,check_count=len(results),passed=sum(r['passed'] for r in results),failures=[r for r in results if not r['passed']],metrics=metrics_rows,checks=results,scope='Finite public-interface checks only. General correctness uses the metatheory in the report.')
    (HERE.parent/'evidence/implementation_counter_validation.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k!='checks'},indent=2))
    if summary['failures']:raise SystemExit(1)

if __name__=='__main__':main()
