#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-circuit-transitions-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();seen={};defs={};hashes={}
def term(i):return f'Sign14Positive74.g{i:02} p' if i<65 else f'out{i} p'
for m in range(9):
 f=p/f'Sign14Positive74CircuitTransitions{m:02}.lean';s=f.read_text();hashes[f.name]=sha(f);expected='DiophantineConsistency.Sign14Positive74CircuitTransitionProbe' if m==0 else f'DiophantineConsistency.Sign14Positive74CircuitTransitions{m-1:02}'
 assert re.findall(r'^import (\S+)$',s,re.M)==[expected] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 for i,expr in re.findall(r'^def out(\d+) \(p : Fin 4 → ℤ\) : Expr \(Fin 14\) := (.*)$',s,re.M):assert int(i) not in defs;defs[int(i)]=expr
 for typ,i,statement,proof in re.findall(r'^theorem (symState|numState)(\d+) ([^\n]*) := by\n(.*?\n  rfl)',s,re.M|re.S):
  i=int(i);assert (typ,i) not in seen;seen[(typ,i)]=m
  ls=statement.split(' = [',1);assert len(ls)==2 and ls[1].endswith(']')
  elems=ls[1][:-1].split(', ');want=[term(j) if typ=='symState' else f'({term(j)}).evalRing v' for j in range(i)];assert elems==want
  assert (f'symState p {i}' if typ=='symState' else f'numState p v {i}') in ls[0]
  assert proof.strip()==f'rw [{"symState" if typ=="symState" else "numState"}, {typ}{i-1}]\n  rfl'
 assert len(re.findall(r'^theorem (?:symState|numState)\d+\b',s,re.M))==sum(mm==m for mm in seen.values())
assert set(seen)=={(t,i) for t in ('symState','numState') for i in range(4,75)}
for i in range(4,75):assert seen['symState',i]==seen['numState',i]==min((i-4)//8,8)
expected={65:'Sign14Positive74.g23 p * Sign14Positive74.g23 p',66:'Sign14Positive74.g41 p * Sign14Positive74.g41 p',67:'Sign14Positive74.g48 p * Sign14Positive74.g48 p',68:'Sign14Positive74.g61 p * Sign14Positive74.g61 p',69:'Sign14Positive74.g64 p * Sign14Positive74.g64 p',70:'(out65 p) + (out66 p)',71:'(out70 p) + (out67 p)',72:'(out71 p) + (out68 p)',73:'(out72 p) + (out69 p)'};assert defs==expected
for f in ('nine-sharing-sign14-positive74-circuit-source-independent','nine-sharing-sign14-positive74-circuit-transition-probe-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_SOURCE_AUDIT','modules':9,'symbolic_and_ring_state_theorems':142,'registers':74,'source_sha256':hashes,'scope':'staged source structural state mapping; no Lean compile or final output equality'},indent=2))
