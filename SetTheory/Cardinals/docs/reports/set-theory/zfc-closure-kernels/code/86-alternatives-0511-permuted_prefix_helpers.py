#!/usr/bin/env python3
"""Emit the reparameterized exact axiom word over the optimized prefix-source helpers."""
from pathlib import Path
import json,sys
H=Path(__file__).resolve().parent;R=H.parent/'context_folds/recovered/67/research'
sys.path[:0]=[str(R/'agent_logic'),str(R/'sources/beyond252/beyond252/exploratory/vendor')]
from verify_reassociation import Decoder,read_json
from dag_tools import interned,unfold
sys.path.insert(0,str(H.parent/'source/Computability/BusyBeaver/Research/ZFC'))
import recover_wade_dag as recover
import theory_backend_experiment as theory
n,root,oldhash=read_json(R/'sources/beyond252/beyond252/exploratory/data/original203.json')
best=json.loads((H.parent/'logical_routes/permuted_rows/best.json').read_text())
original=n.copy();pairs={pair:q for q,pair in n.items()};fresh=max(n)+1
def pair(a,b):
 global fresh
 if (a,b) not in pairs:pairs[a,b]=fresh;n[fresh]=(a,b);fresh+=1
 return ('N',pairs[a,b])
mapping={166:('N',43),121:('N',48),168:('N',63),171:('N',39),177:('N',91),119:('N',57),181:('N',79),180:('N',58),182:pair(('N',58),('I',1)),218:('N',92),178:('N',132),183:('N',94),176:('N',60),158:('N',18),208:('N',30),192:('N',160),131:('N',171),211:('N',11),197:('N',172),161:('N',68)}
# Independent whole-old-AX correspondence checks the complete concrete helper mapping.
raw,_=recover.parse_dag(recover.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
oldword,_,_=theory.old_contract(raw)
x=mapping[oldword[-1]]
for token in reversed(oldword[:-1]):x=pair(mapping[token],x)
dec=Decoder(n,root)
assert dec.normal(('N',183))==dec.normal(x), 'Macro mapping does not reproduce original source AX'
refs=dict(mapping)
for j,(a,b) in enumerate(best['grammar']):refs[300+j]=pair(refs[a],refs[b])
# Use the found exact grammar. The dictionary phase will rebalance the residual.
word=[refs[x] for x in best['residual']]
def balanced(xs):
 if len(xs)==1:return xs[0]
 m=len(xs)//2;return pair(balanced(xs[:m]),balanced(xs[m:]))
newroot=balanced(word)
assert n[184]==(('N',183),('B',1));n[184]=(newroot,('B',1))
d=Decoder(n,root);n={k:v for k,v in n.items()if k in d.reached}
# Equivalent data-only table with compact topological IDs.
n,r=interned(unfold(n,root));d=Decoder(n,r)
report=dict(root=r,nodes=n,source='original203.json',source_sha256=oldhash,macro_mapping={k:v for k,v in mapping.items()},word=best['word'],metrics=d.metrics(),source_nodes=len(n),ordinary_axiom_schema_equivalence='See logical_routes/permuted_rows; complete concrete helper mapping reproduces original AX ordered normal form exactly.')
(H/'permuted_prefix_helpers.json').write_text(json.dumps(report,indent=2)+'\n')
print('emitted',len(n),'metrics',d.metrics())
