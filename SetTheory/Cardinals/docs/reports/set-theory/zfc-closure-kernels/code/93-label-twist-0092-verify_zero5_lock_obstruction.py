#!/usr/bin/env python3
"""Check the finite locked decoder path forcing six consecutive zero bits.

This certifies a syntactic obstruction for the specified fixed interfaces.
It is not a state lower bound and does not assert concrete reachability.
"""
from pathlib import Path
import argparse,hashlib,json

p=argparse.ArgumentParser()
p.add_argument('--package',type=Path,required=True)
p.add_argument('--grammar',type=Path,required=True)
p.add_argument('--output',type=Path)
a=p.parse_args()
assert __debug__,'Assertions must remain enabled.'
source_path=a.package/'inputs/closed-sequence-grammar-next22.json'
symbols_path=a.package/'inputs/semantic-symbols.json'
locks_path=a.package/'inputs/state_reduction/bootstrap-lock54.txt'
s=json.loads(source_path.read_text());symbols=json.loads(symbols_path.read_text())
enc={name:char for char,name in symbols.items()}
names={int(q):''.join(enc[c]for c in w)for q,w in s['flattened_semantic_words'].items()}
g=json.loads(a.grammar.read_text());rules={w:(left,right)for w,left,right in g['rules']}
locklines=locks_path.read_text().splitlines();assert int(locklines[0])==54
locks=[tuple(line.split())for line in locklines[1:]if line.strip()]
assert len(locks)==54 and len(set(locks))==54
chain=['eijkKCqkjGeU','eijkKCqkjGe','eijkKCqkjG','eijkKC','eijk','e']
assert names[172]==chain[0] and 172 in s['required_entry_roots']
for parent,child in zip(chain,chain[1:]):
 assert (parent,'0',child)in locks
 assert rules[parent][0]==child
atom=s['atoms'][symbols['e']]
assert atom['ast']==40
node=s['ast_dag'][40]
assert node[0]=='N'
leaf=s['ast_dag'][node[1]]
assert leaf==['L',['dec',1]]
out=dict(status='PASS',scope='Syntactic obstruction only; fixed atom implementations and the five stated left projections imply a six-zero source path. No global machine-state lower bound or semantic scanner obstruction is claimed.',required_root_state=172,source_word=chain[0],forced_left_words=chain,forced_grammar_edges=5,final_fixed_atom_ast=40,final_fixed_edge=0,terminal_instruction=['dec',1],zero_path='000000',minimum_syntactic_maximum_zero_run=6,hashes={str(path.relative_to(a.package)):hashlib.sha256(path.read_bytes()).hexdigest()for path in[source_path,symbols_path,locks_path]},grammar_sha256=hashlib.sha256(a.grammar.read_bytes()).hexdigest())
text=json.dumps(out,indent=2)+'\n'
if a.output:a.output.write_text(text)
print(text,end='')
