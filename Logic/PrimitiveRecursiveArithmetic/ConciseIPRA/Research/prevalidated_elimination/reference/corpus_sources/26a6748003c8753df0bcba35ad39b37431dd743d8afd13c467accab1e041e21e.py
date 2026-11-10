"""Reproduce kernel metrics, canonical proof compilation, and public checks.

Only the three kernel_*.py files form the measured checkers. Everything
in this script and compile_focused.py is untrusted testing/production code.
"""
import ast
import copy
import hashlib
import io
import json
import platform
import random
import subprocess
import sys
import tokenize
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import compile_focused as compiler

ROOT = Path(__file__).resolve().parent
PROFILES = {
    'kernel_bytes.py': (300,351,745),
    'kernel_tokens.py': (291,339,846),
    'kernel_structure.py': (298,329,855),
}
IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
           tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
           tokenize.ENDMARKER}


def metrics(path):
    raw = path.read_bytes()
    tree = ast.parse(raw.decode())
    for node in ast.walk(tree):
        if isinstance(node,(ast.Module,ast.FunctionDef,ast.AsyncFunctionDef,ast.ClassDef)):
            if (node.body and isinstance(node.body[0],ast.Expr)
                    and isinstance(node.body[0].value,ast.Constant)
                    and isinstance(node.body[0].value.value,str)):
                node.body.pop(0)
    normalized = ast.unparse(tree)+'\n'
    return {'normalized_tokens':sum(t.type not in IGNORED for t in
                                   tokenize.generate_tokens(io.StringIO(normalized).readline)),
            'ast_nodes':sum(1 for _ in ast.walk(tree)),
            'normalized_bytes':len(normalized.encode()),
            'source_sha256':hashlib.sha256(raw).hexdigest()}


def cli(job):
    profile,optimized,case = job
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT/profile)]
    p = subprocess.run(command,input=json.dumps(case['packet']),text=True,
                       capture_output=True,timeout=30)
    expected = 'ACCEPT\n' if case['accept'] else 'REJECT\n'
    if p.stdout != expected or p.returncode != (0 if case['accept'] else 1):
        raise RuntimeError('CLI mismatch: '+profile+'/'+case['name']+'/'+str(optimized))
    return {'profile':profile,'optimized':optimized,'case':case['name'],'passed':True}


def mutate(packet,rng):
    paths=[]
    def walk(a,p):
        paths.append(p)
        if type(a) is list:
            for j,b in enumerate(a): walk(b,p+(j,))
    walk(packet,())
    path=rng.choice(paths)
    value=copy.deepcopy(packet)
    replacement=copy.deepcopy(rng.choice([None,False,True,-999,-1,0,1,2,4,0.5,
                                         'x','',{},[],[0],[0,0],[0,0,0],[0,0,0,0]]))
    if not path:return replacement
    parent=value
    for j in path[:-1]:parent=parent[j]
    parent[path[-1]]=replacement
    return value


def main():
    fixtures=json.loads((ROOT/'certificates.json').read_text())
    sources=json.loads((ROOT/'source_cases.json').read_text())['cases']
    cases=fixtures['cases']
    measured={name:metrics(ROOT/name) for name in PROFILES}
    for name,expected in PROFILES.items():
        row=measured[name]
        assert tuple(row[k] for k in ('normalized_tokens','ast_nodes','normalized_bytes'))==expected, (name,row)
    positives=[x for x in cases if x['accept']]
    assert len(sources)==len(positives)==157
    for source,target in zip(sources,positives):
        produced,metadata=compiler.compile_packet(source['packet'])
        assert produced==target['packet'],source['name']
        assert metadata==target['metadata'],source['name']

    in_process=0
    for case in cases:
        for profile in PROFILES:
            result=compiler.run_packet(ROOT/profile,case['packet'])
            assert result[0]==case['accept'],(profile,case['name'],result)
            in_process+=1

    old_replays=0
    for case in positives:
        extracted=compiler.Extract(case['packet'],focused=True).run()
        tree=compiler.translate(extracted)
        old=compiler.OldEmitter().run(tree)
        assert compiler.run_packet(compiler.BASE,old,focused=False)[0],case['name']
        old_replays+=1

    # Mutations test the public untrusted boundary. Accepted mutations are
    # independently reserialized as explicit proofs for the frozen old kernel.
    rng=random.Random(20261109)
    mutations=0
    accepted_mutations=0
    for case in positives:
        for _ in range(4):
            packet=mutate(case['packet'],rng)
            outcomes=[compiler.run_packet(ROOT/p,packet)[0] for p in PROFILES]
            assert len(set(outcomes))==1,('mutation disagreement',case['name'])
            mutations+=1
            if outcomes[0]:
                extracted=compiler.Extract(packet,focused=True).run()
                old=compiler.OldEmitter().run(compiler.translate(extracted))
                assert compiler.run_packet(compiler.BASE,old,focused=False)[0]
                accepted_mutations+=1

    jobs=[(p,opt,c) for p in PROFILES for opt in (False,True) for c in cases]
    with ThreadPoolExecutor(max_workers=6) as executor:
        executions=list(executor.map(cli,jobs))
    result={'status':'PASS','python':platform.python_version(),
            'implementation':platform.python_implementation(),
            'profiles':measured,'positive_certificates':fixtures['positive_count'],
            'negative_certificates':fixtures['negative_count'],
            'compiler_regenerations':len(sources),'in_process_checks':in_process,
            'independent_old_kernel_replays':old_replays,
            'mutated_packets':mutations,'mutated_profile_executions':3*mutations,
            'accepted_mutations_replayed_by_old_kernel':accepted_mutations,
            'public_cli_checks':len(executions),'failures':0,
            'scope':'Finite executions support the written soundness and identity-expansion proofs; they are not a proof-assistant formalization.',
            'cli':executions}
    (ROOT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='cli'},indent=2))


if __name__=='__main__':
    main()
