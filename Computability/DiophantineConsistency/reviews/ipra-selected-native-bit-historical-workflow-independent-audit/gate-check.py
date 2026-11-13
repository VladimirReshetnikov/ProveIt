#!/usr/bin/env python3
"""Exercise the actual runbook's two audit receipt and exit gates with mutations."""
import ast, copy, hashlib, json, re
from pathlib import Path
from types import SimpleNamespace
if not __debug__:raise RuntimeError('review requires assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];H=ROOT/'Computability/DiophantineConsistency/research/ipra-selected-native-bit/historical'
author_path=ROOT/'Computability/DiophantineConsistency/reviews/ipra-selected-native-bit-guarded-author-independent-audit/receipt.json'
author_terminal=author_path.parent/'terminal-observation.json'
author=json.loads(author_path.read_text());autht=json.loads(author_terminal.read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(author_path)=='e47a76773c98a19ffdf90165ffda5b2f338c9b03bb31f92cc7aa8403656c8516'
assert sha(author_terminal)=='ab4a876dc8e60b13f55f9b4ee43b3e3fdd29bd8a8871265e4a13d6671e1d37b9'
shell=(H/'REAL-RUN.md').read_text().split('```bash\n',1)[1].split('\n```',1)[0]
assert "'--expected-axiom-reports','2'" in shell
assert "'test_real_policy.py'" in shell
body=re.findall(r"python3 - <<'([^']+)'\n(.*?)\n\1(?:\n|$)",shell,re.S)[0][1];tree=ast.parse(body)
selectors=('wfpath','wft[','authorterminal','authorpath','autht[')
nodes=[n for n in tree.body if isinstance(n,ast.If) and any(x in ast.unparse(n.test) for x in selectors)]
assert len(nodes)==5,[ast.unparse(n.test) for n in nodes]
code=compile(ast.fix_missing_locations(ast.Module(body=nodes,type_ignores=[])),'actual-runbook-audit-gates','exec')
wf={'status':'PASS_INDEPENDENT_SELECTED_NATIVE_BIT_WORKFLOW_REVIEW','modules':11,'reports':18}
wft={'observed_exit_code':0,'receipt_sha256':'workflow-sha'}
paths={'wf':'workflow-sha','author':sha(author_path),'author-terminal':sha(author_terminal)}
prepare=SimpleNamespace(digest=lambda p:paths[p]);os=SimpleNamespace(environ={'SELECTED_NATIVE_BIT_WORKFLOW_AUDIT_SHA256':'workflow-sha','SELECTED_NATIVE_BIT_AUTHOR_AUDIT_SHA256':paths['author'],'SELECTED_NATIVE_BIT_AUTHOR_TERMINAL_SHA256':paths['author-terminal']})
def accepts(wf,wft,author,autht):
 try:exec(code,{'wf':wf,'wft':wft,'wfpath':'wf','authorpath':'author','authorterminal':'author-terminal','author':author,'autht':autht,'prepare':prepare,'os':os,'ValueError':ValueError})
 except ValueError:return False
 return True
assert accepts(wf,wft,author,autht)
for obj,key,value in (('wf','status','BAD'),('wf','modules',8),('wf','reports',15),('wft','observed_exit_code',1),('wft','receipt_sha256','BAD'),('author','status','BAD'),('autht','observed_exit_code',1),('autht','receipt_sha256','BAD')):
 cases=[copy.deepcopy(x) for x in (wf,wft,author,autht)];cases[('wf','wft','author','autht').index(obj)][key]=value
 assert not accepts(*cases),(obj,key)
print('PASS_SELECTED_NATIVE_BIT_ACTUAL_AUDIT_GATES real author receipt accepted; eight exit/status/count/hash mutations rejected')
