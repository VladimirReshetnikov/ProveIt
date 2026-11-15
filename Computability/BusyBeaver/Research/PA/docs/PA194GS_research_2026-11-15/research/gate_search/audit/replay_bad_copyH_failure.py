from pathlib import Path
import sys,json
HERE=Path(__file__).resolve().parent;PACKAGE=HERE.parents[2];sys.path.insert(0,str(PACKAGE/'vendor/construction'));import engine_helpers as b
import symbolic_runtime as rt
p=HERE/'rejected/orphan_h11';r=b.read_table(p/'machine.native.tm');ss=json.loads((p/'sites.json').read_text());ii=json.loads((p/'instructions.json').read_text());site=389;_,reg,z,n=ii[site];br=(rt.PHYSICAL[reg],True)
s=rt.frame(tuple(map(int,ss[site][0])));t=rt.canonical(rt.frame(tuple(map(int,ss[z][0]))));trace=[]
for k in range(1024):
 trace.append(s);v=rt.sstep(r,br,s)
 if v is None:break
 s=v[0]
 else_dummy=0
rec={'site':site,'instruction':ii[site],'branch':br,'source_path':ss[site][0],'target':t,'trace':trace,'stuck':s,'symbolic_step':k,'reason':'Symbolic interpreter has no justified next rule; this alone is a checker rejection, not a universal counterexample.'}
(p/'failed_symbolic_trace.json').write_text(json.dumps(rec,indent=2));print({k:v for k,v in rec.items()if k not in ['trace','target','stuck']})
def frame(path):
 ones={-1,48}|{i for i,v in enumerate(path)if v=='1'};pos=49
 for v in [0]*9+[1]:
  pos+=1;ones.update(range(pos,pos+v+1));pos+=v+1
 return ones
ones=frame(ss[site][0]);target=frame(ss[z][0]);q=84;head=0;tr=[];reached=False;first=None
for k in range(10000):
 if k and(q,head,ones)==(84,0,target):reached=True;break
 if k and q==84 and first is None:first={'steps':k,'head':head,'ones':sorted(ones),'expected_head':0,'expected_ones':sorted(target)}
 tr.append([q,head,int(head in ones)])
 if q==254:break
 w,d,q=r[q,int(head in ones)];(ones.add if w else ones.discard)(head);head+=1 if d else -1
out={'site':site,'registers':[0]*9,'spares':[1],'gap':0,'limit':10000,'expected_reached':reached,'steps':k,'first_return84':first,'final':{'q':q,'head':head,'ones':sorted(ones)},'trace':tr}
(p/'failed_literal_trace.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k!='trace'})
