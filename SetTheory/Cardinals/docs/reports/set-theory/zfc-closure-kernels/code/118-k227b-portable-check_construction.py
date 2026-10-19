"""Deterministic source-aware table construction and exact representation binding."""
from pathlib import Path
import argparse,json,hashlib
H=Path(__file__).resolve().parent

def require(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 T={};start=[]
 for l in p.read_text().splitlines():
  if l.startswith('#! start '):start.append(int(l[9:]))
  elif l and not l.startswith('#'):
   q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z));require(b in(0,1)and w in(0,1)and d in('L','R'),'row format');require((q,b)not in T,'duplicate');T[q,b]=(w,1 if d=='R'else-1,z)
 require(len(start)==1,'start declaration');return T,start[0]
def verify_table(T,start,halt,count):
 qs={q for q,b in T};require(len(qs)==count and set(T)=={(q,b)for q in qs for b in(0,1)},'state count/totality');require(start in qs and {z for w,d,z in T.values()}-qs=={halt},'start/halt')
 reached=set();todo=[start]
 while todo:
  q=todo.pop()
  if q in reached:continue
  reached.add(q)
  if q!=halt:todo.extend(T[q,b][2]for b in(0,1))
 require(reached==qs|{halt},'graph-unreachable row')
def main(out):
 P=H/'upstream/K230';require(sha(P/'machine/k230.tm')=='e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8','input machine pin');require(sha(P/'machine/sites230.json')=='400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487','source pin')
 manifest=json.loads((P/'manifest.json').read_text());localfiles=0
 for name,digest in manifest['local_files'].items():require(sha(P/name)==digest,('upstream local source pin',name));localfiles+=1
 O,start=table(P/'machine/k230.tm');verify_table(O,start,230,230)
 expected={(71,0):(0,1,21),(71,1):(1,1,80),(80,1):(0,-1,42),(126,0):(0,1,140),(140,0):(0,1,49),(140,1):(0,1,48)}
 for k,v in expected.items():require(O[k]==v,('delayed premise',k))
 dphi=lambda q:71 if q==140 else q
 A={(q,b):(w,d,dphi(z))for(q,b),(w,d,z)in O.items()if q!=140};A[71,0]=(0,-1,91);A[80,1]=(1,-1,138)
 require(A[121,0]==(0,1,31)and A[121,1]==(1,1,63),'source rotation rows')
 R=dict(A);R[121,0]=(0,1,63);R[121,1]=(1,1,13);require(table(H/'loop_delayed228/rotated229.klabels.tm')==(R,0),'rotated stage')
 phi=lambda q:63 if q==79 else q
 B={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in R.items()if q!=79};B[63,0]=(0,-1,123);B[63,1]=(1,-1,30)
 ops={'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'};ss=[]
 for p,x in json.loads((P/'machine/sites230.json').read_text()):
  a=x.split();ss.append([p,ops[a[0]],int(a[1])if len(a)>1 else None])
 records=[]
 for name,K,n in [('delayed_erasure229',A,229),('loop_delayed228',B,228)]:
  D=H/name;require(table(D/'candidate.klabels.tm')==(K,0),'deterministic construction');verify_table(K,0,230,n)
  maps=json.loads((D/'renumbering.json').read_text());M={int(q):z for q,z in maps['k_to_engine'].items()};C={int(q):z for q,z in maps['k_to_canonical'].items()};require(len(set(M.values()))==len(M),'engine bijection');require(C=={q:i for i,q in enumerate(sorted({q for q,b in K}))}|{230:n},'canonical bijection')
  for q,z in[(64,73),(0,95),(40,48),(97,112),(84,96),(230,254)]:require(M[q]==z,'engine entry map')
  E={(M[q],b):(w,d,M[z])for(q,b),(w,d,z)in K.items()};F={(C[q],b):(w,d,C[z])for(q,b),(w,d,z)in K.items()};require(table(D/'candidate.tm')==(E,95),'engine rows');require(table(D/'candidate.canonical.tm')==(F,0),'canonical rows');verify_table(E,95,254,n);verify_table(F,0,n,n)
  J=json.loads((D/'source.json').read_text());S=J['structures']
  def expand(i,p=''):
   x=S[i];return [[p,*x]]if isinstance(x[0],str)else expand(x[0],p+'0')+expand(x[1],p+'1')
  rows=json.loads((D/'sites.json').read_text());require(expand(J['root'])==rows,'source tree');require(name!='delayed_erasure229'or rows==ss,'original source identity')
  config=json.loads((D/'construction.json').read_text());require(config['working_states']==n and config['append']==1 and config['logical_to_physical']==[6,2,0,4,3,7,8,5,1],'runtime config');guards=sum(2 if o=='CD'else 1 for p,o,r in rows);require(config['guarded_cases']==guards,'guard census');require(max(len(p)for p,o,r in rows)<64,'header bound')
  records.append({'name':name,'working_states':n,'canonical_sha256':sha(D/'candidate.canonical.tm'),'engine_sha256':sha(D/'candidate.tm'),'sites_sha256':sha(D/'sites.json'),'guards':guards,'graph_reachable_states':n,'source_tree_exact':True})
 result={'status':'PASS_PORTABLE_DETERMINISTIC_CONSTRUCTION_AND_SOURCE_BINDING','upstream_local_source_files_checked':localfiles,'reference_dependency_scope':'The115 external upstream proof files are not replayed by this portable ordinary checker. Their earlier intake hash audit is recorded separately.','candidates':records,'checker_sha256':sha(Path(__file__))};out.mkdir(parents=True,exist_ok=True);(out/'construction.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output-dir',type=Path,required=True);args=ap.parse_args();main(args.output_dir)
