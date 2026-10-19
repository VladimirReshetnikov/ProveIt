from pathlib import Path
import sys,json,collections
sys.path.insert(0,str(Path(__file__).parent));import compile_rotated as c

def compile_roles(graph,roles):
 E={int(s):v for s,v in graph['entries'].items()};qs=collections.defaultdict(list)
 for s,q in roles.items():qs[q].append(s)
 T=c.T.copy();conflicts=[]
 for q,ss in qs.items():
  for b in (0,1):
   wants=[]
   for s in ss:
    child=E[E[s][b+1]]
    if child[0]=='N':row=(b,'R',roles[E[s][b+1]])
    else:
     opts={c.T[q,b] for sg in c.qsig.get(q,set()) if c.entries[c.entries[sg][b+1]]==tuple(child)}
     row=next(iter(opts)) if len(opts)==1 else c.term[tuple(child)+(b,)].most_common(1)[0][0]
    wants.append(row)
   if len(set(wants))==1:T[q,b]=wants[0]
   else:conflicts.append((q,b,wants))
 return T,conflicts
if __name__=='__main__':
 graph=json.load(open(sys.argv[1]));roles={int(s):q for s,q in json.load(open(sys.argv[2]))['roles'].items()}
 if len(sys.argv)>4:
  a,b=map(int,sys.argv[4:6]);roles={s:(a if q==b else b if q==a else q) for s,q in roles.items()}
 T,conflicts=compile_roles(graph,roles);c.save_table(T,sys.argv[3]);print('states',len({q for q,b in T}),'conflicts',len(conflicts))
