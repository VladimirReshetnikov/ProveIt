#!/usr/bin/env python3
"""Read-only v3 guard/plan consistency checks; no rebuild and no Lean invocation."""
from pathlib import Path
from hashlib import sha256
import ast,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2]; R=D/'research';P=R/'ten-positive-80-coherent-rebuild';S=P/'run-v3.py';C=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json'; client=R/'ten-positive-80-symbolic-ipra-client-prototype/observations/fixed-attempt01/terminal.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(S)=='c262d844c28fe87954cfe06d14da359d08e4d88838cb32bce025f26b072269d5'
s=S.read_text();tree=ast.parse(s)
assert "s['mem_available_kib']<8*1024**2" in s and "before['mem_available_kib']>=8*1024**2" in s and "s['mem_available_kib']<2*1024**2" not in s
assert sha(client)=='ba10b48d9c2843caf24c56938c88068ddb82372a43461c7ce7fb4ad2c62004da' and sha('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
patterns=[n.args[0].value for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='search' and n.args and isinstance(n.args[0],ast.Constant) and isinstance(n.args[0].value,str) and 'sorryAx' in n.args[0].value];assert len(patterns)==1
for value in ['warning: text','warning(lean.unusedSimpArgs): text','error: text','error(lean.foo): text','decl has sorryAx','ERROR(lean.foo): text']:assert re.search(patterns[0],value)
for value in ['no diagnostic','warning policy here','[propext, Classical.choice, Quot.sound]']:assert not re.search(patterns[0],value)
x=json.loads(C.read_text());pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');system=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
for n,z in x['outside'].items():
 rel=Path(n.replace('.','/')+'.olean');p=next((root/rel for root in (pack,system) if (root/rel).is_file()),None)
 assert p is not None and str(p)==z['path'] and sha(p)==z['sha256']
assert len(x['outside'])==80
for fragment in ['outside_baseline[n]=files(',"snapshot==outside_baseline[name]", "resolve(n)==outside_baseline[n]", "post-header outside drift", "final source drift", "post-header source drift", "record={\'index\':index,\'module\':n,\'command\':command,\'status\':\'PREPARING\'}",'os.replace(temporary,obs/\'result.json\')',"result['status']='PASS'", "result['status']='FAILED'", "imports==scan['fresh_headers'][name]"]:
 assert fragment in s,fragment
subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ten-positive-80-rebuild-v2-prelaunch-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print('PASS v3 static guards and mutation examples, pinned client/Lean, current 80 outside selections and prior 127 source plan')
print('V3 stage status remains RETURNED after validation; only whole-run PASS plus runner exit/receipt reconciliation establishes success.')
print('No Lean/rebuild launch; package transitive history, omitted historical producers, external files not authenticated.')
