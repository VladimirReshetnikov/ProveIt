#!/usr/bin/env python3
"""Map full source constructor calls to exact optimized-tree arithmetic spans."""
import json,sys
from collections import defaultdict,Counter
from pathlib import Path
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE/'reference'))
import recover_wade_dag as rec

def main():
    source,names=rec.parse_dag((BASE/'reference/Dag254.v').read_text())
    old=json.loads((BASE/'reference/decoder_entries.json').read_text())
    optimized={int(k):tuple(map(tuple,v)) for k,v in old['nodes'].items()}
    sarith=[];source_calls=[];oarith=[];span_nodes=defaultdict(list)
    def walksrc(q,path):
        begin=len(sarith)
        for b,e in enumerate(source[q]):
            kind,*arg=e.split();r=int(arg[0]) if arg else 0
            if kind=='ENode':walksrc(r,path+str(b))
            elif kind in ('EInc','EDecnz','EHalt'):sarith.append(({'EInc':'I','EDecnz':'D','EHalt':'H'}[kind],r))
        source_calls.append((begin,len(sarith),q,path))
    def walkopt(q,path):
        begin=len(oarith)
        for b,e in enumerate(optimized[q]):
            if e[0]=='N':walkopt(e[1],path+str(b))
            elif e[0] in 'IDH':oarith.append((e[0],e[1] if len(e)>1 else 0))
        span_nodes[begin,len(oarith)].append((q,path))
    walksrc(0,'');walkopt(old['root'],'')
    def commute(a):
        out=[];pending=[]
        for op in a:
            if op[0]=='I':pending.append(op)
            else:out+=sorted(pending)+[op];pending=[]
        return out+sorted(pending)
    equal=commute(sarith)==commute(oarith)
    result={'source_arithmetic_sites':len(sarith),'optimized_arithmetic_sites':len(oarith),
      'arithmetic_preorder_equal':sarith==oarith,'arithmetic_preorder_equal_modulo_increment_commutation':equal,'constructors':{}}
    if equal:
        for name,root in [('Imp',119),('Rel',181),('All',180),('Eq',182),('F',177)]:
            calls=[c for c in source_calls if c[2]==root]
            matched=[(a,b,path,span_nodes[a,b]) for a,b,_,path in calls]
            result['constructors'][name]={'count':len(calls),'matched_count':sum(bool(x[3]) for x in matched),
               'optimized_nodes':dict(Counter(q for x in matched for q,_ in x[3])),
               'node_entries':{q:old['state_entries'][str(q)] for x in matched for q,_ in x[3]},
               'calls':matched}
    (BASE/'constructor_subtree_mapping.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({**result,'constructors':{k:{a:b for a,b in v.items() if a!='calls'} for k,v in result['constructors'].items()}},indent=2))
if __name__=='__main__':main()
