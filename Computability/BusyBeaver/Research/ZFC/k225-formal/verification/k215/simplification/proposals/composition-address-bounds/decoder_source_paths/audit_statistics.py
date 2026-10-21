#!/usr/bin/env python3
"""Independent count of the literal source DAG in the checked Lean data."""
from pathlib import Path
from collections import Counter
import hashlib,json,re
ROOT=Path(__file__).resolve().parent
p=ROOT/'K215Decoder.lean';text=p.read_text();start=text.index('def sourceNodes : Array Node := #[')
stop=text.index('\n]\n',start)+2
nodes=[(m.group(1),int(m.group(2)),int(m.group(3))) for m in re.finditer(r'\.(leaf|fork) (\d+) (\d+)',text[start:stop])]
root=int(re.search(r'def sourceRoot : Nat := (\d+)',text).group(1))
paths=[];primitives=set()
def visit(i,word):
 if not 0<=i<len(nodes):raise ValueError('Invalid source node')
 kind,a,b=nodes[i]
 if kind=='leaf':paths.append(word);primitives.add((a,b));return
 if not (a<i and b<i):raise ValueError('Nondecreasing source DAG edge')
 visit(a,word+'0');visit(b,word+'1')
visit(root,'')
result={'status':'PASS_SOURCE_DAG_STATISTICS','source':'K215Decoder.lean','source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
 'nodes':len(nodes),'internal_nodes':sum(n[0]=='fork' for n in nodes),'distinct_primitives':len(primitives),
 'primitive_occurrences':len(paths),'internal_occurrences':len(paths)-1,
 'minimum_path_depth':min(map(len,paths)),'maximum_path_depth':max(map(len,paths)),
 'path_depth_histogram':dict(sorted(Counter(map(len,paths)).items())),'scope':'Ordinary source statistics; the exact upstream tree identity is proved in DecoderSourceBinding.source_tree_eq.'}
print(json.dumps(result,indent=2))
