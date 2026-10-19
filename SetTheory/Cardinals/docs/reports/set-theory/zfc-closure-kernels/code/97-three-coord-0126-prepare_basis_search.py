#!/usr/bin/env python3
"""Price classical implication bases using the existing physical dictionary."""
import json,itertools,sys
from pathlib import Path
import prepare_axiom_search as p

basis=sys.argv[1]if len(sys.argv)>1 else 'kbp'
a,b,c='a','b','c';imp=p.sm.Imp
K=imp(a,imp(b,a))
B=imp(imp(a,b),imp(imp(b,c),imp(a,c)))
S=imp(imp(a,imp(b,c)),imp(imp(a,b),imp(a,c)))
P=imp(imp(imp(a,b),a),a)
initial=[K,B,P]if basis=='kbp'else[K,S,P]
schemas=initial+p.sm.ROWS[2:]
variants=[[p.emit(p.rename(row,m))for m in p.maps]for row in schemas]
out=p.HERE/('basis_'+basis);out.mkdir(exist_ok=True)
lines=(p.HERE/'axiom_search.txt').read_text().splitlines()
header=lines[:1+len(p.tokens)]
lines=header+[p.prefix,p.tail,str(len(variants))]+[word for row in variants for word in row]
(out/'input.txt').write_text('\n'.join(lines)+'\n')
metadata=json.loads((p.HERE/'axiom_search_metadata.json').read_text())
metadata.update(basis=basis,variants=variants,schemas=schemas,
    limitation='Fixed inherited core and physical dictionary; no source proof or machine runtime certificate.')
(out/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
print(json.dumps(dict(basis=basis,rows=len(schemas),initial_lengths=[len(v[0])for v in variants[:3]],
    original_rho8=len(p.variants[0][0]),new_AX_length=len(p.prefix)+sum(len(v[0])for v in variants)+len(p.tail))))
