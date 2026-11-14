from support import *
import sys,hashlib
p=(INC,INC);c.MACROS[p]=99;c.MACROS[(p,p)]=190
name=sys.argv[1];prefix=sys.argv[2]
t=c.read_grammar(name+'.grammar.json');r,idx,shape=c.build(t)
old_sites,old_ins,_=c.source(t)
from verify import source_binding
from verify_emitter import word,audit
assert word(t)==word(c.read_grammar(Path(__file__).resolve().parents[1]/"separate196/grammar.json"))
print("EMISSION",audit("separate196"),source_binding(t,old_sites,old_ins),flush=True)
r[100,0]=0,True,213;r[100,1]=1,True,174;r[174,0]=0,True,28;r[174,1]=1,True,164
oldraw=c.raw_nodes
def rotated_raw():
 d=oldraw();d['node164']=('node75',('node37','node163'));return d
c.raw_nodes=rotated_raw
ch=bestcompatible_all(r,shape);rr,alias=apply(r,ch);ss,ins,cs=c.source(t)
old,_=c.machine()
assert all(rr[q,b]==old[q,b] for q in c.BOXSTATES for b in (0,1))
assert ins==old_ins,'source CFG changed'
print('nodes',len(shape),'folds',len(ch),'states',len(rr)//2,'contracts',len(cs),'CFG equal',ins==old_ins,flush=True)
check=c.validate(rr,cs);print('CHECK',check,flush=True);assert check['ok']
q=74;h=0;ones=set();expected=[0,0,0,0,0,0,2,0,0]+[1]*26
for i in range(58294):
 w,d,q=rr[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=1 if d else -1
want={h-1,h};pos=h+48;want.add(pos);pos+=1
for v in expected:pos+=1;want.update(range(pos,pos+v+1));pos+=v+1
assert(q,h)==(84,-2)and ones==want
reach={74};todo=[74]
while todo:
 q=todo.pop()
 for b in(0,1):
  n=rr[q,b][2]
  if n!=254 and n not in reach:reach.add(n);todo.append(n)
labels=[74]+sorted({q for q,b in rr}-{74})+[254];rev={n:i for i,n in enumerate(labels)}
Path(prefix+'.native.tm').write_text(''.join(f'{q} {b} {w} {"R"if d else"L"} {n}\n'for(q,b),(w,d,n)in sorted(rr.items())))
Path(prefix+'.tm').write_text(''.join(f'{rev[q]} {b} {w} {"R"if d else"L"} {rev[n]}\n'for(q,b),(w,d,n)in sorted(rr.items(),key=lambda z:(rev[z[0][0]],z[0][1]))))
Path(prefix+'.grammar.json').write_text(Path(name+'.grammar.json').read_text());Path(prefix+'.folds.json').write_text(json.dumps(ch,indent=2));Path(prefix+'.labels.json').write_text(json.dumps(labels));Path(prefix+'.sites.json').write_text(json.dumps([{'ordinal':i,'path':''.join(map(str,p)),'op':op,'arg':a,'instruction':ins[i]}for i,(p,op,a)in enumerate(ss)],indent=2))
bad=[i for i,(p,op,a)in enumerate(ss)if '1000000' in ''.join(map(str,p))or ''.join(map(str,p)).startswith('0000000')]
report={'validation':check,'startup_steps':58294,'startup_head':h,'startup_ones':sorted(ones),'states':len(rr)//2,'reachable':len(reach),'source_cfg_unchanged':ins==old_ins,'scanner_obstructions':bad,'sha256':hashlib.sha256(Path(prefix+'.tm').read_bytes()).hexdigest()}
Path(prefix+'.receipt.json').write_text(json.dumps(report,indent=2));print('PASS',report,flush=True)
