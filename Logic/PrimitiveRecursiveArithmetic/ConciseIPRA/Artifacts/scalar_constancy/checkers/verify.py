"""Reproduce the two source refinements and finite CLI evidence.

The tests support, but do not prove, the universal arguments in PROOF.txt.
No third-party package or network access is used.
"""
from pathlib import Path
import ast, hashlib, importlib.util, io, json, subprocess, sys, tokenize

ROOT=Path(__file__).resolve().parent

def normalized(text):
    return ast.unparse(ast.parse(text))+'\n'

def metrics(path):
    data=path.read_bytes(); text=normalized(data.decode());tree=ast.parse(text)
    ignore={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NL,tokenize.NEWLINE,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}
    return {'tokens':sum(t.type not in ignore for t in tokenize.generate_tokens(io.StringIO(text).readline)),
            'ast_nodes':sum(1 for _ in ast.walk(tree)), 'normalized_bytes':len(text.encode()),
            'source_bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}

base=(ROOT/'controls/ast262.py').read_text()
expected=normalized(base.replace('k = 0\n','',1).replace('d=0):','d=(k := 0)):',1))
if expected!=(ROOT/'code/checker_ast261.py').read_text():raise AssertionError('AST delta differs')
base=(ROOT/'controls/bytes469.py').read_text()
expected=normalized(base.replace('d=0:', 'd=2:').replace('i(t, d=3)','i(t, d=5)').replace('i(t, [s, u, t], 3)','i(t, [s, u, t], 5)').replace('i(*a, t, 2)','i(*a, t, 4)').replace('c([[]], *q())','c([0], *q())'))
if expected!=(ROOT/'code/checker_bytes468.py').read_text():raise AssertionError('Byte delta differs')

spec=importlib.util.spec_from_file_location('offset',ROOT/'controls/translate_offset.py')
offset=importlib.util.module_from_spec(spec);spec.loader.exec_module(offset)
translated=ROOT/'fixtures/shifted_bytes';translated.mkdir(exist_ok=True)
for path in sorted((ROOT/'fixtures/bytes').glob('*.json')):
    # This helper is an untrusted proof producer for canonical fixtures only.
    value=offset.translate(json.loads(path.read_text()))
    (translated/path.name).write_text(json.dumps(value,separators=(',',':'))+'\n')

negative_names={'future_witness_capture.json','future_witness_neutral.jsonl','direct_false_zero_initializer.jsonl'}
def expected_accept(path):
    return path.name not in negative_names and not path.name.startswith('reject_')

checks=[]
def run(checker,fixture,opt):
    proc=subprocess.run([sys.executable,*(['-O'] if opt else []),'-I',str(ROOT/checker)],
        input=fixture.read_bytes(),stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=15)
    accepted=proc.returncode==0 and proc.stdout==b'ACCEPT\n'
    wanted=expected_accept(fixture)
    checks.append({'checker':checker,'fixture':str(fixture.relative_to(ROOT)),'optimized':opt,
                   'accepted':accepted,'expected':wanted,'exit_code':proc.returncode,
                   'passed':accepted==wanted})
    if accepted!=wanted:
        raise AssertionError((checks[-1],proc.stderr.decode()[-500:]))

for opt in (False,True):
    for fixture in sorted((ROOT/'fixtures/ast').glob('*.jsonl')):
        for checker in ('controls/ast262.py','code/checker_ast261.py'):run(checker,fixture,opt)
    for fixture in sorted((ROOT/'fixtures/bytes').glob('*.json')):
        run('controls/bytes469.py',fixture,opt)
        run('code/checker_bytes468.py',translated/fixture.name,opt)

files=['controls/tokens241.py','controls/ast262.py','code/checker_ast261.py','controls/bytes469.py','controls/offset472.py','code/checker_bytes468.py']
receipt={'python':sys.version,'metrics':{p:metrics(ROOT/p) for p in files},
         'checked_exact_source_changes':True,'process_executions':len(checks),
         'failed_expectations':sum(not c['passed'] for c in checks),'checks':checks,
         'universal_correctness_machine_checked':False}
(ROOT/'evidence/verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='checks'},indent=2))
