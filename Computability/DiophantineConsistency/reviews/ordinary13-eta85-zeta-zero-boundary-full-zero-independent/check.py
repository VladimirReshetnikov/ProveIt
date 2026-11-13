from pathlib import Path
import hashlib, json, operator, subprocess, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-eta85-zeta-zero-boundary-full-zero-independent')
for name,want in json.loads((D/'pins.json').read_text()).items():
 assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==want, name
P=Path('research/ordinary13-eta85-zeta-zero-boundary-audit')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
old=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
new=json.loads((P/'probe.json').read_text())
assert old['witnesses']==new['witnesses']==['n_J','n_F','n_alpha','n_f','n_i','n_T','n_w','n_s','n_r','n_eta','n_zeta','n_y','n_gamma']
assert old['fixed_numerals']==new['fixed_numerals']==['beta','K0','MC','MF']
assert len(old['source'])==len(new['source'])==85 and old['output']==new['output']=='out'
# Exhaustive row-level derivation: old eta+zeta+1 is probe eta+zeta
# after raising the probe input by one; old (eta+zeta)-R is probe
# (eta+zeta)-R-1. Every other instruction is unchanged modulo k rename.
expected=[]
for n,op,a,b in old['source']:
 if n=='k':
  assert [n,op,a,b]==['k','+','kbase',1]; continue
 if n=='r0':
  assert [n,op,a,b]==['r0','-','kbase','R']
  expected += [['r0base','-','kbase','R'],['r0','-','r0base',1]]; continue
 assert 'kbase' not in (a,b), (n,op,a,b)
 expected.append([n,op, 'kbase' if a=='k' else a, 'kbase' if b=='k' else b])
assert new['source']==expected
ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
def values(g,w,p):
 d=dict(zip(g['witnesses'],w)); d.update(zip(g['fixed_numerals'],p))
 for name,op,a,b in g['source']:
  assert name not in d and op in ops
  d[name]=ops[op](d[a] if isinstance(a,str) else a,d[b] if isinstance(b,str) else b)
 return d
cases=[([1,0,0,1,0,0,0,0,0,0,0,1,0],[-1,0,1,0],0,0,9),([1,0,0,1,0,0,1,0,0,0,0,1,0],[0,-2,-1,0],1,1,97)]
for w,p,q,y,parent in cases:
 assert min(w)>=0 and w[9]==w[10]==0
 d=values(new,w,p); e=values(old,w,p)
 assert (d['q'],d['Y'],d['A0'],d['A1'],d['g72'],d['Fa'],d['out'],e['out'])==(q,y,0,0,0,1,0,parent)
 assert any(x<0 for x in p)
compact=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text()
beta=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in compact
assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta
print(json.dumps({'row_level_forward_substitution_verified':True,'full_integer_graph_zeros_independently_recomputed':2,'old_graph_same_tuple_outputs':[9,97], 'compact_port_scope':'Both examples use signed ports outside the natural compact tuple; no compact zero or zero-map obstruction shown.', 'lean_executed':False},sort_keys=True,indent=2))
