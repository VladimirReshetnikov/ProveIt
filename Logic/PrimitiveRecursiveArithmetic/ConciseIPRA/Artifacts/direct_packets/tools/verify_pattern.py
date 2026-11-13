"""Reproduce the independent malformed-pattern and retained-goal audit.

Adapted from the executed audit only to resolve paths within this archive.
Dynamic execution here inspects Python functions in this untrusted test tool;
none of the measured checkers imports or calls this file.
"""
from pathlib import Path
import ast, builtins, dis, io, json, subprocess, sys

ROOT = Path(__file__).resolve().parents[1]
candidate = ROOT / 'code/checkers/checker_ast_jsonl.py'
control = ROOT / 'code/checkers/control_ast262_jsonl.py'
goal = [[0, 0, 0], 0]
packets = [0, [], [0], [0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [[0], 0, 0, 0], [-1, 0, 0, 0], [0]*20, [0, 0, 0]]
records = []
for optimize in [False, True]:
    for packet in packets:
        item = {'packet':packet, 'optimized':optimize, 'expected':packet == [0, 0, 0], 'programs':[]}
        for file in [control, candidate]:
            cmd = [sys.executable] + (['-O'] if optimize else []) + [str(file)]
            run = subprocess.run(cmd, input=json.dumps(goal)+'\n'+json.dumps(packet)+'\n', text=True,
                                 capture_output=True, timeout=3)
            accepted = run.returncode == 0 and run.stdout.strip() == 'ACCEPT'
            item['programs'].append({'file':str(file), 'accepted':accepted, 'exit_code':run.returncode,
                                     'last_error':run.stderr.strip().splitlines()[-1] if run.stderr.strip() else ''})
            assert accepted == item['expected'], item
        records.append(item)

# Direct hypothesis-goal stress case: retained goal must not mask no-match.
for file in [control, candidate]:
    tree = ast.parse(file.read_text())
    nodes = [n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom, ast.FunctionDef))
             or isinstance(n, ast.Assign) and any(isinstance(t,ast.Name) and t.id=='k' for t in n.targets)]
    for packet in packets:
        ns = {'s':0, 'u':0, 't':0, 'r':[0,0,0], 'input':lambda p=packet:json.dumps(p)}
        exec(compile(ast.Module(body=nodes,type_ignores=[]),str(file),'exec'),ns)
        try:
            ns['c']([[0,0]], [0,0])
            accepted, error = True, ''
        except Exception as e:
            accepted, error = False, type(e).__name__
        assert accepted == (packet == [0,0,0]), (file,packet,accepted,error)
        records.append({'mode':'already-retained goal plus preexisting globals', 'file':str(file),
                        'packet':packet, 'accepted':accepted, 'error':error})

tree = ast.parse(candidate.read_text())
function = next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='c')
ns = {}
exec(compile(ast.Module(body=[function],type_ignores=[]),str(candidate),'exec'),ns)
bytecode = io.StringIO()
dis.dis(ns['c'], file=bytecode)
(ROOT / 'evidence/independent_review/match_cpython312_disassembly.txt').write_text(bytecode.getvalue())
evidence = {'runtime':sys.version, 'standalone_process_runs':40, 'direct_hypothesis_cases':20,
            'failed_expectations':0, 'cases':records}
(ROOT / 'evidence/independent_review/match_validation.json').write_text(json.dumps(evidence,indent=2)+'\n')
print(json.dumps({k:v for k,v in evidence.items() if k!='cases'},indent=2))
