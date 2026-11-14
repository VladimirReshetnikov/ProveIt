#!/usr/bin/env python3
"""Compare source words and ordinal control using explicit prefix intervals."""
from pathlib import Path
from collections import Counter
import json,hashlib,argparse
HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--inputs',type=Path,default=HERE/'inputs')
parser.add_argument('--output',type=Path,default=HERE/'source_comparison.json')
args=parser.parse_args()
manifest=json.loads((args.inputs/'sources_manifest.json').read_text())
paths={k:args.inputs/v['file'] for k,v in manifest.items()}
def graph(s):
    pref={}
    for i,(addr,op,arg) in enumerate(s):
        for k in range(len(addr)+1):pref.setdefault(addr[:k],[]).append(i)
    for x,indices in pref.items():
        if indices!=list(range(indices[0],indices[-1]+1)):raise ValueError('noncontiguous')
    def branch(addr,bit,n):
        places=[i for i,v in enumerate(addr) if v==bit]
        if len(places)<n:return 0
        p=addr[:places[-n]];indices=pref[p]
        return (indices[-1]+1)%len(s) if bit=='0' else indices[0]
    out=[]
    for i,(addr,op,arg) in enumerate(s):
        aft=(i+1)%len(s)
        targets={'CI':lambda:[aft],'CD':lambda:[branch(addr,'0',1),aft],'CB':lambda:[branch(addr,'0',arg)],'CC':lambda:[branch(addr,'1',arg)],'CH':lambda:[]}[op]()
        out.append([op,arg,targets])
    return out
s={k:json.loads(p.read_text()) for k,p in paths.items()}
g={k:graph(v) for k,v in s.items()}
if g['A']!=g['B']:raise ValueError('control graph differs')
summary={'snapshot':'c086b5adaa6228009365768946d691dfc49a20bb','sites':len(s['A']),'nonhalt_edges':sum(len(x[2]) for x in g['A']),'same_ordered_opcodes_operands':[x[1:] for x in s['A']]==[x[1:] for x in s['B']],'same_ordinal_control_graph':True,'different_addresses':sum(x[0]!=y[0] for x,y in zip(s['A'],s['B'])),'graph_sha256':hashlib.sha256(json.dumps(g['A'],separators=(',',':')).encode()).hexdigest()}
for k,v in s.items():summary[k]={'sha256':hashlib.sha256(paths[k].read_bytes()).hexdigest(),'maxdepth':max(len(x[0]) for x in v),'max_zero_run':max(max(map(len,x[0].split('1'))) for x in v),'operations':dict(Counter(x[1] for x in v))}
args.output.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
