"""Rebuild repaired227 from proved228 with explicit source-role rotations."""
from pathlib import Path
from functools import cache
import argparse,json
from check_construction import require,sha,table,verify_table
H=Path(__file__).resolve().parent;D=H/'source_fold227_zerofix';B=H/'loop_delayed228'
def source(path,mapping):
 J=json.loads(path.read_text());S=J['structures']
 @cache
 def tree(n):
  x=S[n];return tuple(x)if isinstance(x[0],str)else tuple(tree(c)for c in x)
 return tree(J['root']),{tree(int(n)):mapping[q]for n,q in J['allocation'].items()},tree

def leaf(n):return isinstance(n[0],str)
@cache
def boundary(n):
 if leaf(n):
  o,r=n;return(1,0,False)if o=='CD'else(r,0,False)if o=='CB'else(0,r,False)if o=='CC'else(0,0,o=='CH')
 a,b=map(boundary,n);return max(max(a[0]-1,0),b[0]),max(a[1],max(b[1]-1,0)),a[2]or b[2]
def sites(n,p=''):
 return [[p,*n]]if leaf(n)else sites(n[0],p+'0')+sites(n[1],p+'1')
def live(n):
 out=set()
 def visit(x):
  if x in out:return
  out.add(x)
  if not leaf(x):visit(x[0]);visit(x[1])
 visit(n);return out

def main(out):
 M={int(q):z for q,z in json.loads((B/'renumbering.json').read_text())['k_to_engine'].items()};I={z:q for q,z in M.items()};root,A,_=source(B/'source.json',I);T,start=table(B/'candidate.klabels.tm');require(start==0,'start');stages=[]
 def rotate(q,q2,d):
  nonlocal root,A,T
  ns=[n for n,v in A.items()if v==q];require(len(ns)==1,('ambiguous outer role',q));n=ns[0];child=n[1 if d=='L'else 0];require(not leaf(child)and A[child]==q2,'inner source role');require(sum(v==q2 for v in A.values())==1,'ambiguous inner role')
  require(all(T[p,b][:2]==(b,1)for p in(q,q2)for b in(0,1)),'nonpure rotation row')
  if d=='L':a,(b,c)=n;replacement=((a,b),c)
  else:(a,b),c=n;replacement=(a,(b,c))
  require(all(boundary(x)==(0,0,False)for x in(a,b,c)),'escaping source chunk')
  @cache
  def f(x):return replacement if x==n else x if leaf(x)else(f(x[0]),f(x[1]))
  oldword=[x[1:]for x in sites(root)];root=f(root);require([x[1:]for x in sites(root)]==oldword,'primitive order changed');L=live(root);A={f(x):v for x,v in A.items()if f(x)in L};A[replacement[0 if d=='L'else 1]]=q2;old=dict(T)
  if d=='L':
   qa=T[q,0][2];qb=T[q2,0][2];qc=T[q2,1][2];T[q,0]=(0,1,q2);T[q,1]=(1,1,qc);T[q2,0]=(0,1,qa);T[q2,1]=(1,1,qb)
  else:
   qa=T[q2,0][2];qb=T[q2,1][2];qc=T[q,1][2];T[q,0]=(0,1,qa);T[q,1]=(1,1,q2);T[q2,0]=(0,1,qb);T[q2,1]=(1,1,qc)
  stages.append({'rotation':[q,q2,d],'all_three_chunks_closed':True,'chunk_leaves':[len(sites(x))for x in(a,b,c)],'literal_edits':[{'row':list(k),'before':old[k],'after':T[k]}for k in sorted(T)if T[k]!=old[k]]})
 for row in[(174,119,'L'),(202,201,'R'),(148,154,'L')]:rotate(*row)
 # The preserved source role is identified by its literal subtree, not its index alone.
 _,FA,ftree=source(D/'source.klabels.json',{q:q for q in range(231)});role=ftree(95);require(role in A and A[role]==175,'reallocated role mismatch');require(T[150,0]==(0,1,90)and T[150,1]==(1,1,90)and T[176,1]==(1,1,175),'realias row premises');parents=[(q,b)for n,q in A.items()for b,c in enumerate(n)if c==role];parents=[k for k in parents if T[k]==(1,1,175)];require(sorted(parents)==[(155,1),(176,1)],'direct source incoming premise');A[role]=150;T[150,1]=(1,-1,173)
 for k in parents:T[k]=(1,1,150)
 phi=lambda q:152 if q==175 else q
 T={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in T.items()if q!=175};T[152,0]=(0,-1,159);T[152,1]=(1,-1,169);A={n:phi(q)for n,q in A.items()};rotate(211,210,'L')
 require(sites(root)==json.loads((D/'sites.json').read_text()),'rebuilt source differs');require(A==FA,'final exact source-role allocation differs');K,st=table(D/'candidate.klabels.tm');require((K,st)==(T,0),('rebuilt literal table differs',[(k,T.get(k),K.get(k))for k in sorted(set(T)|set(K))if T.get(k)!=K.get(k)]));verify_table(K,0,230,227)
 maps=json.loads((D/'renumbering.json').read_text());EM={int(q):z for q,z in maps['k_to_engine'].items()};CM={int(q):z for q,z in maps['k_to_canonical'].items()};E,se=table(D/'candidate.tm');C,sc=table(D/'candidate.canonical.tm');require(E=={(EM[q],b):(w,d,EM[z])for(q,b),(w,d,z)in K.items()}and se==95,'engine isomorphism');require(C=={(CM[q],b):(w,d,CM[z])for(q,b),(w,d,z)in K.items()}and sc==0,'canonical isomorphism');verify_table(E,95,254,227);verify_table(C,0,227,227);er,EA,_=source(D/'source.json',{z:q for q,z in EM.items()});require(er==root and EA==A,'engine source allocation')
 receipt={'status':'PORTABLE_SOURCE_AWARE_227_CONSTRUCTION_PASS','baseline_sha256':sha(B/'candidate.klabels.tm'),'candidate_sha256':sha(D/'candidate.klabels.tm'),'canonical_sha256':sha(D/'candidate.canonical.tm'),'source_sites_sha256':sha(D/'sites.json'),'working_states':227,'source_roles':len(A),'rotation_stages':stages,'realias':'literal role95 moved175→150, row150/1=1L173, incoming155/1 and176/1 redirected','fold':'175→152; row152/0=0L159; row152/1=1L169','scope':'Deterministic literal/source construction and renaming proof. Complete source CFG equality, runtime, and startup are independently replayed.','checker_sha256':sha(Path(__file__))};out.mkdir(parents=True,exist_ok=True);(out/'construction227.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items()if k!='rotation_stages'},indent=2))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output-dir',type=Path,required=True);a=ap.parse_args();main(a.output_dir)
