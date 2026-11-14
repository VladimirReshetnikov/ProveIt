#!/usr/bin/env python3
"""Generate/rank64 gate variants with conjugated M/E/U numeric encodings."""
from pathlib import Path
import json,sys,itertools,time
import integrated_flexible as F
G=F.G;O=F.O;SG=G.SG

def flip_tree(t,flip):
    if isinstance(t,(str,int)):return t
    tag,a,b=t;a=flip_tree(a,flip);b=flip_tree(b,flip)
    return(tag,b,a)if tag in flip else(tag,a,b)

def main():
    count=int(sys.argv[1])if len(sys.argv)>1 else 20
    starts=json.loads(Path(__file__).with_name('integrated_variants.json').read_text())
    records=[];start=time.monotonic()
    for ei,bits in enumerate(itertools.product([False,True],repeat=3)):
        flip={tag for tag,on in zip([1,3,2],bits)if on}
        prefix=G.PREFIX.copy()
        if 2 in flip:prefix[:2]=reversed(prefix[:2])
        heads=[G.code(flip_tree(G.expression(h),flip))for i,h in enumerate(G.HEADS)if i!=4]
        for vi,v in enumerate(starts):
            gate=flip_tree(v['gate_formula'],flip)
            word=prefix+sum(heads,[])+G.code(gate)+G.SUFFIX[-3:]
            assert len(word)==196
            rec=dict(index=len(records),encoding=dict(zip(['M','E','U'],bits)),gate_variant=v['name'],word=word,gate_formula=gate)
            SG.WORD=word;best=(999,999);br=None
            for rs in range(count):
                rules,root=SG.repaire(rs,0 if rs%3 else 1.2)
                t=G.opened(G.decode(rules,root));phys=O.evaluate(t)[0]
                score=(len(rules),phys)
                if score<best:best=score;br=dict(root=root,rules=rules,word=word,tokens=SG.TOKENS)
            rec['raw_nodes']=best[0];rec['physical_score']=best[1];records.append(rec)
            br.update(design='integrated witness with conjugated numeric constructors',encoding=rec['encoding'],gate_variant=v['name'])
            Path(__file__).with_name(f'encoding_seed_{rec["index"]}.json').write_text(json.dumps(br,indent=2))
            print('VARIANT',rec['index'],bits,v['name'],'raw',best[0],'physical',best[1],flush=True)
    Path(__file__).with_name('integrated_encoding_variants.json').write_text(json.dumps(records,indent=2))
    ranked=sorted(records,key=lambda r:(r['raw_nodes'],r['physical_score']))
    Path(__file__).with_name('integrated_encoding_rank.json').write_text(json.dumps(ranked,indent=2))
    print('BEST',[(r['index'],r['raw_nodes'],r['physical_score'],r['encoding'],r['gate_variant'])for r in ranked[:12]],flush=True)
    print('SECONDS',time.monotonic()-start,flush=True)
if __name__=='__main__':main()
