from pathlib import Path
import collections,json,sys,itertools
sys.dont_write_bytecode=True
import source_inventory as I
L=I.L
b=I.base
for label,sp in [('A',b/'machine/variant_plain/u208.sites.json'),('B',b/'machine/u208.sites.json')]:
 rows=json.loads(sp.read_text());g=L.graph_intervals(rows);pred=collections.defaultdict(set)
 for i,(_,es)in enumerate(g):
  for j in es:pred[j].add(i)
 counts=collections.Counter((rows[i][2],rows[i+1][2])for i in range(len(rows)-1)if rows[i][1]==rows[i+1][1]=='CI'and rows[i][2]!=rows[i+1][2]and pred[i+1]=={i})
 print(label,'pairs',counts)
 out=Path('analysis/comparison/ci_reorder_'+label);out.mkdir(exist_ok=True);results=[]
 for a,c in counts:
  rr=[list(x)for x in rows];changed=[]
  for i in range(len(rows)-1):
   if rr[i][1:]==['CI',a]and rr[i+1][1:]==['CI',c]and pred[i+1]=={i}:rr[i][2],rr[i+1][2]=c,a;changed.append(i)
  m=L.metrics(L.tree(rr));p=out/f'swap_{a}_{c}.json';p.write_text(json.dumps(rr,separators=(',',':'))+'\n');results.append({'file':str(p),'pair':[a,c],'swaps':changed,'metrics':m})
  print(a,c,len(changed),m['dag_nodes'])
 # Lexicographic sort each single-entry CIrun under all permutations of participating registers.
 regs=sorted({r for pair in counts for r in pair})
 if len(regs)<=8:
  best=999;bestperms=[]
  for order in itertools.permutations(regs):
   rank={r:i for i,r in enumerate(order)};rr=[list(x)for x in rows];i=0
   while i<len(rr):
    if rr[i][1]!='CI':i+=1;continue
    j=i+1
    while j<len(rr)and rr[j][1]=='CI'and pred[j]=={j-1}:j+=1
    values=sorted([rr[k][2]for k in range(i,j)],key=lambda r:rank.get(r,100+r))
    for k,r in zip(range(i,j),values):rr[k][2]=r
    i=j
   n=L.metrics(L.tree(rr))['dag_nodes']
   if n<best:best=n;bestperms=[order];print('BEST',label,best,order,flush=True)
   elif n==best:bestperms.append(order)
  print('OPTIMUM',label,best,len(bestperms),'of',len(list(itertools.permutations(regs))))
 (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
