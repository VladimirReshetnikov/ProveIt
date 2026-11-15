#!/usr/bin/env python3
"""Replay source identity and initial cost screens, not full TM validation."""
from pathlib import Path
import json,sys
HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parents[1]
sys.path.insert(0,str(PACKAGE/'vendor/construction'))
import engine_helpers as b
from engine_foldscreen import opportunities,matching
INC=('leaf','inc',1)
results=[]
for folder in sorted((HERE/'compositions').iterdir()):
    if not folder.is_dir():continue
    nodes={k:b.tup(v)for k,v in json.loads((folder/'parent.nodes.json').read_text()).items()}
    old=b.tup(json.loads((folder/'parent.tree.json').read_text()))
    tree=b.tup(json.loads((folder/'seed.tree.json').read_text()))
    parent=b.read_table(folder/'parent.raw.native.tm')
    oldsites,oldins=b.source(nodes,old)
    sites,ins=b.source(nodes,tree)
    assert ins==oldins,folder.name
    macros={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,
            'node72':69,'node75':213,'node142':194,INC:61,'node60':99,
            'node61':190,'node54':114,'node57':20,'node69':30,
            'node146':196,'node149':217,(INC,INC):99,
            ((INC,INC),(INC,INC)):190}
    if(333,0)in parent:macros['node55','node65']=333
    raw={k:v for k,v in parent.items()if k[0]<1300};ix={}
    def state(t):
        if t in macros:return macros[t]
        if t in ix:return ix[t]
        q=2000+len(ix);ix[t]=q
        for bit,ch in enumerate(t):raw[q,bit]=(bit,True,state(ch))
        return q
    root=state(tree);raw[101,1]=(1,True,root);raw=b.reachable(raw)
    fixed={k:v for k,v in raw.items()if k[0]<1300}
    assert fixed==b.read_table(folder/'fixed.native.tm')
    bound=len(matching(opportunities(raw)))
    got={'family':folder.name,'raw':len(raw)//2,'fixed':len(fixed)//2,
         'readers':len(raw)//2-len(fixed)//2,'matching_upper_bound':bound,
         'best_nominal_statecount':len(raw)//2-bound,'source_sites':len(sites),
         'source_equal':True,'paths_changed':sum(a[0]!=z[0]for a,z in zip(sites,oldsites))}
    expected=json.loads((folder/'initial.json').read_text())
    assert all(expected[k]==v for k,v in got.items()),(folder.name,got,expected)
    results.append(got)
print(json.dumps({'status':'PASS','scope':'Source equality and initial matching-bound cost screen only; no physical correctness assertion.','families':results},indent=2))
