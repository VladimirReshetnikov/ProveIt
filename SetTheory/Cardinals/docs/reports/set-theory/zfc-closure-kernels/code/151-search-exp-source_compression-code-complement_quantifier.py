#!/usr/bin/env python3
"""Source-only dual quantifier experiment. No calibration or runtime claimed."""
import sys,json,collections
from pathlib import Path
H=Path(__file__).resolve().parent
P=H.parent/'inputs'
B=H
sys.path.insert(0,str(B));import source_language as s,build221 as b
import measure as m
rows=json.load(open(P/'sites218.json'));tree=s.tree(rows);table=b.read_table((P/'k218.native.tm').read_bytes());groups,_=b.decoder_map(table,tree)
q=lambda k:b.sole(groups,k)
push=q(98)[0];imp=q(90);inc=('CI',1)
mac={'a':q(98),'b':q(12),'c':q(166),'I':imp,'R':(imp,inc),'Q':(imp,(inc,inc)),'E':(imp,((inc,inc),inc)),'F':(push,inc)}
def op(c,x,y):return(c,x,y)
I=lambda x,y:op('I',x,y)
R=lambda x,y:op('R',x,y)
Q=lambda x,y:op('Q',x,y)
E=lambda x,y:op('E',x,y)
N=lambda x:('N',x)
a,bv,c='a','b','c'
Ex=lambda i,x:N(Q(i,N(x)))
req=Q(bv,I(c,N(Q(bv,I(c,N(R(bv,c)))))))
clos=Q(bv,I(R(bv,c),N(Q(a,I(c,N(Q(a,I(Q(c,I(R(c,a),R(c,bv))),req))))))))
nks=Q(c,I(clos,N(req)))
vrel=I(R(a,bv),Q(c,R(a,bv)))
forms={
 'GEN':Q(a,bv),
 'G':I(E(c,a),I(E(c,bv),Q(R(a,bv),E(a,bv)))),
 'rho6':I(Ex(a,Q(a,c)),c),
 'rho5':I(E(c,a),I(R(c,bv),R(a,bv))),
 'rho4':I(Q(a,Q(bv,c)),Q(bv,Q(a,c))),
 'rho3':I(E(a,bv),I(R(c,a),R(c,bv))),
 'rho2':I(Q(a,I(bv,c)),I(Q(a,bv),Q(a,c))),
 'rho1':Ex(a,E(a,bv)),
 'bundle':N(I(vrel,nks)),
}
def postfix(f):
 if isinstance(f,str):return[f]
 if f[0]=='N':return postfix(f[1])+['F','I']
 return postfix(f[1])+postfix(f[2])+[f[0]]
def word(f):return tuple(p for x in postfix(f) for p in m.flat(mac[x]))
flat=m.flat(tree)
spans={}
for name,f in forms.items():
 w=word(f);starts=[i for i in range(len(flat)-len(w)+1) if flat[i:i+len(w)]==w];print(name,len(w),starts,postfix(f),flush=True)
 if len(starts)==1:spans[name]=(starts[0],starts[0]+len(w))

def neg(x):return x[1] if isinstance(x,tuple) and x[0]=='N' else N(x)
def trans(f,mode):
 if isinstance(f,str):return f
 if f[0]=='N':return neg(trans(f[1],mode))
 x,y=f[1:]
 if f[0]=='Q':
  y=trans(y,mode)
  return neg(Q(x,y)) if mode=='coforall' else neg(Q(x,neg(y)))
 if f[0] in ('E','R'):return f
 return I(trans(x,mode),trans(y,mode))

def gen_transformed(mode):
 out={k:trans(f,mode)for k,f in forms.items()}
 if mode=='coforall':
  # Classical contrapositive/exchange normal forms: same quantifier principles.
  out['rho2']=I(Q(a,c),I(N(Q(a,I(bv,c))),Q(a,bv)))
  out['rho4']=I(Q(bv,N(Q(a,c))),Q(a,N(Q(bv,c))))
 if mode=='exists':
  # Existential commutation is equivalent to universal commutation.
  out['rho4']=I(Q(a,Q(bv,c)),Q(bv,Q(a,c)))
 return out
if __name__=='__main__':
 report={'baseline_spans':spans,'baseline_metrics':s.metrics(tree),'variants':{}}
 for mode in ['coforall','exists']:
  fs=gen_transformed(mode);print('MODE',mode,flush=True)
  for name,f in fs.items():print(name,len(word(f))-len(word(forms[name])),postfix(f),flush=True)
  rr=tree
  for name,(lo,hi) in sorted(spans.items(),key=lambda x:x[1][0],reverse=True):
   rr=m.splice(s,rr,lo,hi,m.serial([mac[x]for x in postfix(fs[name])]))
  metrics=s.metrics(rr);print('NAIVE METRICS without GEN',metrics,flush=True)
  (H/(mode+'.naive.sites.json')).write_bytes(s.compact(s.sites(rr)))
  report['variants'][mode]={'source_metrics_without_gen':metrics,'formula_lengths':{name:len(word(f))for name,f in fs.items()},'postfix':{name:postfix(f)for name,f in fs.items()}}
 (H/'complement_quantifier_naive_results.json').write_text(json.dumps(report,indent=2)+'\n')
