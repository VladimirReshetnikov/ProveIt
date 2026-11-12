#!/usr/bin/env python3
"""Independent graph dependency and source premise audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue89-root-switch-graph-draft/Residue89RootSwitchGraph.lean.src','6f5963feb1ebad8243b0464d4087aeec50471dbc68f447adf8e392d3aa6796e7')
pin('research/ordinary13-residue89-root-switch-graph-draft/receipt.json','fc35fa36472d2a889fcfc6368ab3a4e8f2e5c1ad47ad05c0a75049f4abb1c35c')
pin('reviews/ordinary13-residue-root-switch-extraction-independent/result.json','c19c21f4670ee4d6a7e01887349786c75f1ecfc8432a78873cd84467c1a8114b')
pin('reviews/ordinary13-residue89-to90-model-independent/result.json','548f207643c65e9eaffe9278e5bff1c3f112f2794e65baa24d11dc99c4b0dd49')
g=json.loads(pin('research/ordinary13-natural-residue-forced89-degree56/candidate.json','c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a'));rows={r[0]:r for r in g['source']}
for row in [['qm','*','n_J','beta'],['E','*','n_X','Y'],['kY','*','Y','k'],['ell','*','E','kY'],['g30','+','ell','k'],['g31','+','g30','n_r'],['folded_kBt','*','k','Bt'],['folded_g31','-','g31','folded_kBt'],['g32','*','qm','folded_g31'],['Z','-','g32','Bt'],['g38','*','Z','Z'],['g39','*','qm','qm'],['g40','*','ell','g30'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42']]:assert rows[row[0]]==row,row
assert sum('n_r' in row[2:] for row in g['source'])==1
def dependencies(name):
 seen={name};stack=[name]
 while stack:
  for arg in rows.get(stack.pop(),[None,None,None,None])[2:]:
   if isinstance(arg,str) and arg not in seen:seen.add(arg);stack.append(arg)
 return seen
assert 'n_r' in dependencies('A0') and all('n_r' not in dependencies(x) for x in ('A1','Fam','g72','Bt','ell','k','qm'))
for x in ['def putR','if i=8 then r else v i','theorem first_norm','theorem first_update','theorem unchanged1','theorem unchanged2','theorem unchanged3','theorem replacement_of_scale','(hb : 0<b p v)','ResidueRootSwitchExtractDraft.positive_replacement','theorem J_positive','theorem compact_positiveReplacement','CompactFixedBeta.bounds','(h82 : HAExpressionAssembly.PolynomialBridge','Residue89RootSwitchTransportDraft.polynomialBridge']:
 assert x in s,x
for idx in (0,1,2,3): assert f'(hres {idx})' in s or f'(hres {idx}' in s
for X in range(5):
 for Y in range(5):
  for k in range(5):assert (X*Y)*(Y*k)==(X*Y*Y)*k
print(json.dumps({'scope':'literal graph dependency and conditional source transport review; no Lean','coordinate_changed':8,'only_first_residual_depends_on_r':True,'requires_positive_scale':True,'compact_beta_and_natural_port_representation':True,'no_local_K_upper_bound':True,'positive82_parent_bridge_explicit':True,'lean_elaborated':False},sort_keys=True,indent=2))
