import re,sys,itertools
from collections import defaultdict
from pathlib import Path
BASE=Path('/workspace/scratch/b65d0f102007/sources/context246/zfc-context246');sys.path.insert(0,str(BASE/'code'))
from check_literal_instructions import read_table
T=read_table(BASE/'machine/zfc_prefix246_old.tm')
HERE=Path(__file__).parent
S=defaultdict(list)
for line in (HERE/'edge_results.txt').read_text().splitlines():
    m=re.fullmatch(r'SURVIVOR (\d+) (\d+) orig=(\d+) (-?\d+) (\d+) new=(\d+) (-?\d+) (\d+) cases=(\d+)',line)
    if m:
        a,b,w,d,q,x,y,z,n=map(int,m.groups());S[a,b].append((x,y,z))
for q in [30,39,42,57,67,69,122,235]:
    es=[(a,b) for (a,b),(w,d,c) in T.items() if c==q and a!=q]
    assert all(e in S for e in es)
    path=HERE/f'combined_options_{q}.txt'
    with path.open('w') as f:
        print(q,len(es),file=f)
        combinations=1
        for a,b in es:
            cs=S[a,b];combinations*=len(cs)
            print(a,b,len(cs),*[v for row in cs for v in row],file=f)
    print(q,combinations)
