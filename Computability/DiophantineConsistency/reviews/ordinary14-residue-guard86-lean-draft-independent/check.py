#!/usr/bin/env python3
"""Independent literal 86-row graph source review; no Lean invocation."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-residue-guard86-lean-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'P86ResidueGraph.lean','5b655c426151d999745360c8366f940198fcaa1a8408eb905b6b92285a9dcf42').decode()
pin(A/'make_graph.py','8fdec3e5db6f0859bdd7f62849c52d0944f03aa0a09d1dad56f69c8078253f2e')
receipt=pin(A/'observation.json','6f4d3b8b9c3026a2c951c9c0717e7e30fa73e3fcb17c44bdec87b53b6f20d63c')
g=json.loads(pin(D/'research/ordinary14-residue-guard86/candidate.json','ecd34ccc9032fd7f2ef1b767b2182fe4d43aa82389b1a6857832c3dd3891c371'))
pin(D/'Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean','f1d7f3835bc2a183b0767497a45ffdd0a54e6aab086b259ccce3de4af9392cb6')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-residue-guard86-lean-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='389443d5a7d1cf19c80aea70985bd21cceaa524987aa07ca05673c191409ac86'
assert g['witnesses']==['J','F','alpha','f','i','T','X','Y','r','eta','zeta','u','gamma','h']
assert g['fixed_numerals']==['beta','K0','MC','MF']
for i,n in enumerate(g['witnesses']):assert f'  let {n} : Expr (Fin 14) := .var {i}\n' in src
for i,n in enumerate(g['fixed_numerals']):assert f'  let {n} : Expr (Fin 14) := .constant (p {i})\n' in src
block=src.split('  -- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0]
rows=[];known=set(g['witnesses']+g['fixed_numerals'])
for line in block.splitlines():
 m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line);assert m,line
 n,l,op,r=m.groups();assert n not in known
 for x in (l,r):assert x.isdecimal() or x in known,(n,x)
 known.add(n);rows.append([n,op,int(l) if l.isdecimal() else l,int(r) if r.isdecimal() else r])
assert rows==g['source'] and len(rows)==86 and g['output']=='guarded_out'
assert '⟨A0, A1, Fa, g72, guard, guarded_out⟩' in src
lookup={n:(a,b) for n,_,a,b in rows};live=set();todo=[g['output']]
while todo:
 n=todo.pop()
 if n in live or n not in lookup:continue
 live.add(n);todo.extend(lookup[n])
assert len(live)==len(rows)
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'make_graph.py'),'--check'],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==receipt
print(json.dumps({'scope':'literal source review only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'rows':len(rows),'live_rows':len(live)},sort_keys=True,indent=2))
