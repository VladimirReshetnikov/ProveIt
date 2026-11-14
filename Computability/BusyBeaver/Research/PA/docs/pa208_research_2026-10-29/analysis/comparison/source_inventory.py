from pathlib import Path
import collections,importlib.util,json,sys
sys.dont_write_bytecode=True
base=Path('upstream/u208_research_2026-10-29/u208_research_2026-10-29')
spec=importlib.util.spec_from_file_location('source_language',base/'baseline_evidence/compatibility/code/source_language.py');L=importlib.util.module_from_spec(spec);spec.loader.exec_module(L)
def read(path):
 t={}
 for line in path.read_text().splitlines():
  if not line.strip() or line[0]=='#':continue
  q,b,w,d,z=line.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
 return t

def inventory(table,rows):
 root=L.tree(rows); occurrences=collections.defaultdict(list)
 def visit(node,q,path):
  occurrences[q].append((path,node))
  if L.leaf(node):return
  for b in (0,1):
   w,d,z=table[q,b]
   if (w,d)==(b,1):visit(node[b],z,path+str(b))
 visit(root,84,'')
 rotations=[]
 for p,ns in occurrences.items():
  if (p,0)not in table:continue
  if not all(table[p,b][:2]==(b,1) for b in (0,1)):continue
  if any(L.leaf(n)for _,n in ns):continue
  for side in (0,1):
   q=table[p,side][2]
   if (q,0)not in table:continue
   if not all(table[q,b][:2]==(b,1) for b in (0,1)):continue
   if [(u,b) for (u,b),(_,_,z) in table.items() if z==q]!=[(p,side)]:continue
   if any(L.leaf(n[side]) for _,n in ns):continue
   if side==0: facts=[(*n[0],n[1]) for _,n in ns]
   else:facts=[(n[0],*n[1])for _,n in ns]
   if not all(all(L.boundary(f)==(0,0,False) for f in abc) for abc in facts):continue
   rotations.append([p,q,side,len(ns),[len(L.sites(x))for x in facts[0]]])
 return root,occurrences,rotations
if __name__=='__main__':
 for label,tp,sp in [('A',base/'machine/variant_plain/u208.native.tm',base/'machine/variant_plain/u208.sites.json'),('B',base/'machine/u208.native.tm',base/'machine/u208.sites.json')]:
  t=read(tp);rows=json.loads(sp.read_text());root,occ,rots=inventory(t,rows)
  print(label,'Source states',len(occ),'pure',sum(all(t.get((q,b),None)and t[q,b][:2]==(b,1)for b in(0,1))for q in occ),'rotations',len(rots))
  print(json.dumps(rots))
