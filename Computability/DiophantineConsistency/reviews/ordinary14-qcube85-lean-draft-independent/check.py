#!/usr/bin/env python3
"""Independent literal-row review; no Lean invocation."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2]; A=D/'research/ordinary14-qcube85-lean-draft'
def sha(data): return hashlib.sha256(data).hexdigest()
def pin(p,h):
    d=p.read_bytes(); assert sha(d)==h,str(p); return d
source=pin(A/'P85QcubeGraph.lean','46c5ffa3344d70b22ca9bc3c56a7b0ba37ac6603a3f7b38f202f5d84fc44ef9b').decode()
pin(A/'make_graph.py','94b6952bb3f212a38e9e77f0ff2f6d6d7d0b6272b230347e897cfb8fb3b3e2bd')
receipt=pin(A/'observation.json','46be284437d24c0d298ca5afbe18ff7c24df258859859f35ea4bf371231ad0b0')
pin(D/'Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean','f1d7f3835bc2a183b0767497a45ffdd0a54e6aab086b259ccce3de4af9392cb6')
candidate=json.loads(pin(D/'research/ordinary14-qcube85-tradeoff/candidate.json','0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7'))
readme=(A/'README.md').read_bytes(); tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-qcube85-lean-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='62320dd2d8bb919c6bfc6792e293a580191ed747862d36332c86e5d7e504d6d6'
assert candidate['witnesses']==['J','F','alpha','f','i','T','X','s','r','eta','zeta','u','gamma','h']
assert candidate['fixed_numerals']==['beta','K0','MC','MF']
for i,n in enumerate(candidate['witnesses']): assert f'  let {n} : Expr (Fin 14) := .var {i}\n' in source
for i,n in enumerate(candidate['fixed_numerals']): assert f'  let {n} : Expr (Fin 14) := .constant (p {i})\n' in source
block=source.split('  -- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0]
rows=[]; known=set(candidate['witnesses']+candidate['fixed_numerals'])
for line in block.splitlines():
    m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line); assert m,line
    n,l,op,r=m.groups(); assert n not in known
    for x in (l,r): assert x.isdecimal() or x in known,(n,x)
    known.add(n); rows.append([n,op,int(l) if l.isdecimal() else l,int(r) if r.isdecimal() else r])
assert rows==candidate['source'] and len(rows)==85
assert '⟨A0, A1, Fa, g72, guard, guarded_out⟩' in source
assert candidate['output']=='guarded_out'
run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'make_graph.py'),'--check'],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not run.stderr and run.stdout==receipt
print(json.dumps({'scope':'literal source review only; no Lean','rows':len(rows),
 'candidate_sha256':'0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7',
 'prelink_readme_sha256':sha(readme[:-len(tail)])},sort_keys=True,indent=2))
