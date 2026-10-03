"""Bounded independent patch/source-algebra review; no author-suite rerun."""
import contextlib,hashlib,importlib.util,json,random,shutil,subprocess,sys,tempfile
from pathlib import Path

OLD='94fb0aa513fc4c07860e2edab98bbb9d75fe713ed724f94e437e297a09a8666e'
PATCH='c811f6e552531f614e1fcaefffc9a296d313fe80a94a3e65aa4cf033306f2033'
NEW='96d4c2b634d465dfcd4df421d57d7f71da44efa201d00fa2518660e600507eef'
def need(ok,msg):
 if not ok:raise AssertionError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
@contextlib.contextmanager
def module(p,name):
 sentinel=object();old=sys.modules.get(name,sentinel)
 try:
  s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);yield m
 finally:
  if old is sentinel:sys.modules.pop(name,None)
  else:sys.modules[name]=old

def manual(bs,x,y,w):
 sels,copies,slacks=w;total=sum(sels);rs=[total-1]
 rs += [a-sum(z[i] for z in copies) for i,a in enumerate(x)]
 rs += [a-sum(sum(b.matrix[i][j]*copies[r][j] for j in range(len(x))) for r,b in enumerate(bs)) for i,a in enumerate(y)]
 for r,b in enumerate(bs):
  k=0
  for g in b.guards:
   v=sum(c*z for c,z in zip(g.coeff,copies[r]))
   if g.kind!='eq':v-=slacks[r][k]+(sels[r] if g.kind=='gt' else 0);k+=1
   rs.append(v)
 products=tuple(sum(sels[i] for i in range(len(bs)) if i!=r)*sum(copies[r]) for r in range(len(bs)))
 return tuple(rs),products

def verify(root,patch):
 root=Path(root);patch=Path(patch).resolve();src=root/'code/quadratic_packet.py';need(sha(src)==OLD and sha(patch)==PATCH,'Pins')
 rng=random.Random(20261006);count=0;rejects=0;canonical=0
 with tempfile.TemporaryDirectory(prefix='signal-second-reader-') as td:
  dest=Path(td);(dest/'code').mkdir();shutil.copy2(src,dest/'code/quadratic_packet.py')
  r=subprocess.run(['patch','--batch','--fuzz=0','-p1','-i',str(patch)],cwd=dest,capture_output=True,timeout=60);need(r.returncode==0,r.stderr);need(sha(dest/'code/quadratic_packet.py')==NEW,'New pin')
  with module(src,'_ind_signal_old') as old,module(dest/'code/quadratic_packet.py','_ind_signal_new') as new:
   for d in range(1,6):
    for B in range(4):
     matrices=[tuple(tuple(rng.randint(-2,3) for _ in range(d)) for _ in range(d)) for _ in range(B)]
     guards=[tuple((kind,tuple(rng.randint(-2,3) for _ in range(d))) for kind in ('eq','gt','ge')) for _ in range(B)]
     pairs=[tuple(m.Branch(M,tuple(m.Guard(k,c) for k,c in gs)) for M,gs in zip(matrices,guards)) for m in (old,new)]
     for _ in range(20):
      x=tuple(rng.randrange(5) for _ in range(d));y=tuple(rng.randrange(5) for _ in range(d));w=(tuple(rng.randrange(4) for _ in range(B)),tuple(tuple(rng.randrange(5) for _ in range(d)) for _ in range(B)),tuple(tuple(rng.randrange(5) for _ in range(2)) for _ in range(B)))
      lit=manual(pairs[1],x,y,w)
      for m,bs in zip((old,new),pairs):need(m.packet_terms(bs,x,y,w)==lit,'Complete valid affine/product rows');need(m.polynomial_value(bs,x,y,w)==sum(a*a for a in lit[0])+sum(lit[1]),'Complete polynomial')
      count+=1
    ident=tuple(tuple(int(i==j) for j in range(d)) for i in range(d));axis=(1,)+(0,)*(d-1)
    bs=(new.Branch(ident,(new.Guard('eq',axis),)),new.Branch(ident,(new.Guard('gt',axis),new.Guard('ge',axis))))
    for n in range(5):
     x=(n,)*d;w=new.canonical_witness(bs,x,x);need(w is not None and new.polynomial_value(bs,x,x,w)==0,'Unique branch section');canonical+=1
   def reject(f):
    nonlocal rejects
    try:f()
    except (ValueError,TypeError):rejects+=1;return
    raise AssertionError('Bad boundary accepted')
   branch=(new.Branch(((1,0),(0,1)),(new.Guard('ge',(1,0)),)),)
   w=new.canonical_witness(branch,(1,1),(1,1))
   for bad in ((1,),(),(1,1,3),(1.0,1),(True,1),(-1,1)):
    for fn in (new.canonical_witness,):
     reject(lambda bad=bad:fn(branch,bad,(1,1)));reject(lambda bad=bad:fn(branch,(1,1),bad))
    reject(lambda bad=bad:new.polynomial_value(branch,bad,(1,1),w));reject(lambda bad=bad:new.polynomial_value(branch,(1,1),bad,w))
   for bad in ((w[0],w[1],((1,None),)),(w[0],w[1],((1.0,),)),(w[0],w[1],((True,),)),(w[0],w[1],((-1,),)),((1.0,),w[1],w[2]),((True,),w[1],w[2]),(w[0],((1,1,2),),w[2]),(w[0],((1.0,1),),w[2]),(w[0],w[1],()),((),w[1],w[2])):
    reject(lambda bad=bad:new.polynomial_value(branch,(1,1),(1,1),bad))
   for bad in (((1,2),),((1.0,),),((True,),),()):reject(lambda bad=bad:new.Branch(bad,()))
   for bad in ((1.0,),(True,),('1',)):reject(lambda bad=bad:new.Guard('eq',bad))
   reject(lambda:new.Branch(((1,),),(new.Guard('eq',(1,2)),)))
   matrix=[[1,0],[0,1]];coeff=[1,0];guards=[new.Guard('ge',coeff)];mode=['a','b'];edges=[0]
   b=new.Branch(matrix,guards,mode,edges);matrix[0][0]=5;coeff[0]=8;guards.clear();mode.clear();edges.clear()
   need(b.matrix==((1,0),(0,1)) and b.guards[0].coeff==(1,0) and b.mode==('a','b') and b.tied_edges==(0,),'Nested snapshots')
 return {'status':'PASS','original_sha256':OLD,'patch_sha256':PATCH,'repaired_sha256':NEW,'valid_complete_row_and_polynomial_cases':count,'canonical_positive_domain_sections':canonical,'bad_boundary_calls_rejected':rejects,'nested_snapshot_regressions':1,'scope':'Only generic patch, complete natural affine/product preservation, and inspected root graph/ledger derivation; no duplicated ten-command suite or trillion-term expansion.'}

if __name__=='__main__':
 import argparse
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True);a.add_argument('--patch',type=Path,required=True);a.add_argument('--output',type=Path);args=a.parse_args();r=verify(args.root,args.patch)
 if args.output:args.output.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps(r,indent=2))
