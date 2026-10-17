from pathlib import Path
from context_search import executor,cases,program_sites,check
from analyze_table import parse_table
import json
ROOT=Path(__file__).parent
rows,*_=parse_table(ROOT/'sources/zfc_254.tm');rows.update({(3,0):(0,'L',48),(5,0):(1,'R',97),(5,1):(1,'R',64),(49,1):(0,'R',5)})
class Tracking(dict):
 def __getitem__(self,k):self.read.add(k);return super().__getitem__(k)
T=Tracking({(str(q),b):(w,d,str(r)) for(q,b),(w,d,r) in rows.items() if q!=8});T.read=set()
ns=executor(T,ROOT/'sources/symexec.py');sites=program_sites(ROOT/'sources/Prog254.v');cs=cases(ns,sites)
allowed={tuple(x) for x in json.loads((ROOT/'abstract_reachability_k2.json').read_text())['allowed']}
allreads=set();livereads=set();deadcases=[]
for j,c in enumerate(cs):
 T.read=set();assert check(ns,c);allreads|=T.read
 if (c[0],c[4]) in allowed:livereads|=T.read
 else:deadcases.append((c[0],sites[c[0]],c[4]))
print('deadcases',deadcases)
print('reads all',len(allreads),'live',len(livereads),'unused',allreads-livereads)
