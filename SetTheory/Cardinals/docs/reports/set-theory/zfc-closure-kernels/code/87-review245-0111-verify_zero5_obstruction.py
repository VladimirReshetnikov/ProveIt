"""Exact finite proof of one unavoidable six-zero source path under five boot locks."""
import json
from pathlib import Path
import search_grammar as s
source=json.loads((s.BASE/'inputs__closed-sequence-grammar-next22.json').read_text())
certificate=json.loads((Path(__file__).resolve().parent/'zero5-strict-obstruction.json').read_text())
locks={(w,int(b)):t for w,b,t in s.locks};w=certificate['source_word'];steps=0
for edge in certificate['chain']:
 assert edge['bit']==0
 if 'word'in edge:
  assert w==edge['word'] and locks[w,0]==edge['target_word'];w=edge['target_word']
 else:
  assert w=='e' and s.ATOM[w]==edge['ast']
  node=source['ast_dag'][edge['ast']];assert node[0]=='N' and node[1]==edge['target_ast']
  assert source['ast_dag'][edge['target_ast']]==certificate['leaf']
 steps+=1
assert steps==6 and certificate['leaf']==['L',['dec',1]]
assert source['sequence_ast_roots']['172']==221 and s.AST[221]==['W',certificate['source_word']]
print('PASS: five boot-locked zero edges plus one fixed atom edge force six consecutive zeros to dec register1')
