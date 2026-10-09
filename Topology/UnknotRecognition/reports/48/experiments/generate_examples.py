"""Generate examples and replay every published result."""
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from compressed_b3 import recognize,verify
from compressed_b3.forest import recognize_forest,verify_forest
from experiments.families import sleeve,singleton_forest

def main():
    rows=[('sleeve_256',sleeve(256),False),
          ('knotted_sleeve_64',sleeve(64,negative=True),False),
          ('singleton_forest_12',singleton_forest(4,16),True)]
    d=dict(strands=4,rules=[['e']],root=0)
    for g in [1,2,-3]*3:
        j=len(d['rules']);d['rules'].append(['g',g]);d['rules'].append(['c',d['root'],j]);d['root']=j+1
    rows.append(('unresolved_four_braid',d,True))
    for name,data,forest in rows:
        producer,checker=(recognize_forest,verify_forest) if forest else (recognize,verify)
        out=producer(data);assert checker(data,out['certificate'])==out['status']
        for suffix,obj in (('.json',data),('.result.json',out)):
            (ROOT/'examples'/(name+suffix)).write_text(json.dumps(obj,indent=2)+'\n')
    (ROOT/'examples/README.md').write_text('''# Examples

`sleeve_256.json` represents an unknot word with `4*2^256+2` letters.
`knotted_sleeve_64.json` is a conjugate of the four-letter figure-eight braid.
`singleton_forest_12.json` has four three-strand factors and twelve strands.
`unresolved_four_braid.json` intentionally returns INCONCLUSIVE: it is not an unknot assertion.
Every `.result.json` was independently replayed when generated.
''')

if __name__=='__main__':main()
