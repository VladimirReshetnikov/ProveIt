from pathlib import Path
import json,itertools
P=Path(__file__).resolve().parent
files=[P/'reference_primary/source/pa194.grammar.json',P.parent/'inputs/second_grammar.json']
leaf={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221,'node60':99,'node61':190,('leaf','inc',1):61,('leaf','breakTo',1):-1}
fixed=(P.parent/'inputs/seeds_cached.txt').read_text().splitlines();nb=int(fixed[0]);out=fixed[:nb+1]+['1440'];metadata=[]
for base,fn in enumerate(files):
    d=json.loads(fn.read_text());word=[]
    def parse(x):
        if isinstance(x,list):x=tuple(x)
        if x in leaf:word.append(leaf[x]);return leaf[x]
        return tuple(map(parse,d['rules'][x]))
    root=parse(d['root']);ranges=[(18,35),(35,54),(54,70),(70,86),(86,102),(102,121)]
    for order in itertools.permutations(range(6)):
        fresh=[(q,-1,-1) for q in word[:18]]
        for head,original in enumerate(order):
            low,high=ranges[original]
            for q in word[low:high]:
                fresh.append((q,head,[98,12,166].index(q)) if q in [98,12,166] else (q,-1,-1))
        fresh.extend((q,-1,-1) for q in word[121:]);assert len(fresh)==190
        memo={};ns=[];pos=0
        def build(t):
            nonlocal_dummy=None
            global pos
            if isinstance(t,int):row=(0,)+fresh[pos];pos+=1
            else:row=(1,build(t[0]),build(t[1]),0)
            if row not in memo:memo[row]=len(ns);ns.append(row)
            return memo[row]
        rr=build(root);tid=len(metadata);out.append(f'{tid} {len(ns)} {rr}');out.extend(' '.join(map(str,n)) for n in ns)
        metadata.append({'template':tid,'base':base,'head_order':order})
(P/'order_templates.txt').write_text('\n'.join(out)+'\n');(P/'order_templates.json').write_text(json.dumps(metadata,indent=2))
print('wrote',len(metadata),'templates')
