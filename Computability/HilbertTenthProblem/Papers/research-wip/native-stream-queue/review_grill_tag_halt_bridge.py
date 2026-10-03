#!/usr/bin/env python3
"""Bounded independent whole-table/phase/cleanup review of the frozen bridge."""
import argparse,collections,hashlib,itertools,json,random
from pathlib import Path
PINS={'source':'3984312d5a5d9c8ebfde557e683e32bcba7fc69dbf65cfe1a9037803eebdb892','receipt':'94f1e283b27c5bb3b4009fb49a64a8fcf2fd3b7d6041088fec38f277deaed767','reference':'66c64fc95574b4d938a3a05e443215f802825677129a17e3cd38fae4150a12f3'}
def need(x,s):
 if not x:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 return type(a)is type(b) and (a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a) if type(a)is dict else len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b)) if type(a)is list else a==b)
def grill(r):return (0,)+(1,0)*r
def block(n,y,width,mode,halt):
 a=28*(n+1);e=3*a//2 if y==halt else 7*a*(1-width)
 if mode=='E':return (0,)*(14*y+7)+grill(a-3)+grill(7)+grill(a-4)+(0,)*(3*a-14*y-10+e)
 if mode=='L':return (0,)*(a-3)+grill(14*y+7)+grill(3)+grill(3*a-14*y-10)+(1,0)*e
 return (0,)+grill(14*y+7)+grill(3)+grill(3*a-14*y-10+e)+(0,)*(a-4)
def program(widths,rules,halt):
 n=len(widths);a=28*(n+1);slots={}
 for phase in (0,1):
  shift=phase*7*a
  for y in range(n):
   for offset in (28*y+17,28*y+a+13):
    for d,v in zip((0,2,4),(a-3,7,a-4)):
     need(shift+offset+d not in slots,'Distinct recoding run');slots[shift+offset+d]=v
   if y==halt:continue
   out=rules[phase,y]
   for side,z in enumerate(out):
    e=3*a//2 if z==halt else 7*a*(1-widths[z]);start=shift+14*y+2*a+3+8*side
    for d,v in zip((0,2,4),(14*z+7,3,3*a-14*z-10+e)):
     need(start+d not in slots,'Distinct production run');slots[start+d]=v
 # The middle production run is zero by default; no special output helper.
 return tuple(slots.get(i,0) for i in range(14*a))
def generation(bits,phase,q):
 out=[]
 for i,b in enumerate(bits):
  if b:out.append(0);out.extend((1,0)*q[(phase+i)%len(q)])
 return tuple(out),(phase+len(bits))%len(q)
def fifo(bits,phase,q,bound):
 # Independent array with a monotonically advancing read pointer.
 tape=list(bits);head=0;minimum=10**100
 while head<len(tape):
  need(head<bound,'FIFO step bound')
  bit=tape[head];head+=1
  if bit:tape.append(0);tape.extend([1,0]*q[phase])
  phase=(phase+1)%len(q);minimum=min(minimum,len(tape)-head)
 return head,phase

def run(source,receipt,root):
 paths={'source':Path(source),'receipt':Path(receipt),'reference':Path(root)/'review_grill_encoding_e.py'}
 for k,p in paths.items():need(sha(p.read_bytes())==PINS[k],'Frozen '+k)
 m={'__name__':'_independently_reviewed_grill','__file__':str(paths['source'])};exec(compile(paths['source'].read_bytes(),str(paths['source']),'exec'),m)
 saved=json.loads(paths['receipt'].read_text());need(saved['source_sha256']==PINS['source'],'Receipt source identity')
 count=collections.Counter();digest=hashlib.sha256();rng=random.Random(20586179);fifo_records=[]
 for n in (2,3,5,7):
  a=28*(n+1)
  for halt in sorted({0,n//2,n-1}):
   active=[y for y in range(n) if y!=halt]
   for style in range(3):
    widths=tuple(0 if style==0 else 1 if style==1 else y%2 for y in range(n))
    rules={(p,y):(rng.randrange(n),rng.randrange(n)) for p,y in itertools.product((0,1),active)}
    q=program(widths,rules,halt);need(q==m['compile_program'](widths,rules,halt=halt),'Independent full literal program')
    need(len(q)==392*(n+1) and sum(z>0 for z in q)==24*n-12,'Complete table counts');count['full_programs']+=1
    support={i%(7*a) for i,v in enumerate(q) if v}
    need(all(i%2==1 and 0<2*i<5*a for i in support),'All odd active residues lie in first interval')
    need(all(q[(i+3*a)%(14*a)]==0 and q[(i+10*a)%(14*a)]==0 for i in support),'Both shifted halves vanish')
    for y in range(n):
     for mode in ('E','L','R'):
      b=block(n,y,widths[y],mode,halt);need(''.join(map(str,b))==m['encode'](y,widths,mode,halt=halt),'Every literal block')
      expected_len=(17*a//2 if mode=='E' else 10*a) if y==halt else (7*a*(2-widths[y]) if mode=='E' else 7*a*(3-2*widths[y]))
      expected_ones=2*a if mode=='E' else 9*a//2 if y==halt else 3*a+7*a*(1-widths[y])
      need(len(b)==expected_len and sum(b)==expected_ones,'Exact length and population')
      # Check every one, including variable grills crossing many program cycles.
      for ph in (3*a,10*a):need(all(q[(ph+i)%len(q)]==0 for i,z in enumerate(b) if z),'Every shifted one is erased');count['whole_block_shifted_support_proofs']+=1
      count['literal_blocks']+=1
      for ph in (0,7*a):
       got,np=generation(b,ph,q)
       if mode in ('L','R'):
        need(got==block(n,y,widths[y],'E',halt),'Normal recoding');count['normal_LR_words']+=1
       elif y!=halt:
        u,v=rules[ph//(7*a),y];expect=block(n,u,widths[u],'L',halt)+block(n,v,widths[v],'R',halt)
        need(got==expect and np==7*a*((ph//(7*a)+widths[y])%2),'Exact E word and Genera phase');count['normal_E_word_phase']+=1
    # New alphabet sizes, arbitrary halt index, mixed widths, every location in
    # each selected even-length word; each case evaluated independently.
    for length in (2,4,8):
     pos=rng.randrange(length);v=tuple(halt if i==pos else rng.choice(active) for i in range(length))
     b=tuple(bit for i,y in enumerate(v) for bit in block(n,y,widths[y],'L' if i%2==0 else 'R',halt))
     for ph in (0,7*a):
      w1,p1=generation(b,ph,q);w2,p2=generation(w1,p1,q);w3,p3=generation(w2,p2,q)
      tail=sum(3*a+7*a*(1-widths[y]) for y in v[pos+1:])
      expect=tuple(bit for y in v[:pos] for bit in block(n,y,widths[y],'E',halt))+block(n,halt,widths[halt],'E',halt)+(0,)*tail
      need(w1==expect and p1==(ph+3*a)%(14*a),'First cleanup word and phase')
      need(w2==(0,)*(2*a*(pos+1)) and not w3,'Complete shifted cleanup')
      lengths=[10*a+sum(7*a*(3-2*widths[y]) for y in v if y!=halt),17*a//2+sum(7*a*(2-widths[y]) for y in v[:pos])+tail,2*a*(pos+1)]
      need(lengths==[len(b),len(w1),len(w2)] and min(lengths)>0,'Exact positive generation lengths')
      author=m['cleanup'](v,widths,q,ph,halt)
      need(author['generation_lengths']==lengths and author['remaining_steps']==sum(lengths) and author['final_phase']==p3,'Author full cleanup result')
      count['complete_cleanup_words']+=1;digest.update(str((n,halt,style,v,ph,lengths,p3)).encode())
    # Two nonhalting source generations with odd initial word length, persistent
    # phase and no halt outputs. This is deliberately independent of cleanup.
    nohalt={(p,y):(active[(active.index(y)+p)%len(active)],active[(active.index(y)+1)%len(active)]) for p,y in itertools.product((0,1),active)}
    qn=program(widths,nohalt,halt)
    for initialphase in (0,1):
     v=tuple(rng.choice(active) for _ in range(3));p=initialphase;b=tuple(bit for y in v for bit in block(n,y,widths[y],'E',halt));gp=7*a*p
     for generation_index in range(2):
      nxt=[]
      for y in v:nxt.extend(nohalt[p,y]);p=(p+widths[y])%2
      lr,gp1=generation(b,gp,qn);b2,gp2=generation(lr,gp1,qn)
      expect=tuple(bit for y in nxt for bit in block(n,y,widths[y],'E',halt))
      need(b2==expect and gp2==7*a*p and gp1==gp2 and b2,'Whole persistent-phase source simulation')
      count['nonhalting_two_generation_simulations']+=1;v=tuple(nxt);b=b2;gp=gp2
 # Eight independently run genuine valid-halt traces at N=5, including a halt
 # label other than the last. HA has empty prefix; AH would be undefined.
 n=5;a=168
 for halt,width,phase in itertools.product((0,3),(0,1),(0,1)):
  A=1 if halt!=1 else 2;widths=tuple(width for _ in range(n));active=[y for y in range(n) if y!=halt]
  rules={(p,y):(halt,A) for p,y in itertools.product((0,1),active)};q=program(widths,rules,halt)
  b=block(n,A,width,'E',halt);remaining=10*a+7*a*(3-2*width)+17*a//2+3*a+7*a*(1-width)+2*a
  expected=len(b)+remaining;steps,final=fifo(b,phase*7*a,q,expected)
  need(steps==expected,'Literal valid first-halt trace');count['valid_whole_FIFO_first_halts']+=1
  fifo_records.append(dict(N=n,halt=halt,width=width,initial_phase=phase,steps=steps,final_phase=final))
 # Classify, rather than conflate, the author's eight original full-FIFO cases.
 for f in saved['first_halt_fixtures']:
  need(f['halt_index'] in (0,1),'Original two-output fixture')
  count['author_valid_Genera_FIFO_cases' if f['halt_index']==0 else 'author_cleanup_only_undefined_Genera_cases']+=1
 # Conditional four-gate loader: independent bit expansion and exact width.
 n=3;a=112;K=1<<(7*a);D=1<<14
 gval=lambda r:2*((1<<(2*r))-1)//3
 A=(1<<7)*(gval(a-3)+(1<<(2*a-5))*gval(7)+(1<<(2*a+10))*gval(a-4))
 for length in range(1,7):
  for x in range(1<<(length-1),1<<length):
   bits=tuple((x>>i)&1 for i in range(length));R=sum(b*K**i for i,b in enumerate(bits));J=sum(K**i for i in range(length));P=K**length
   u=(D-1)*R;v=J+u;X=A*v;Z=P-X
   word=tuple(z for b in bits for z in block(n,b,1,'E',2));actual=sum(z<<i for i,z in enumerate(word))
   need(X==actual and P==1<<len(word) and 0<3*X<P and Z>0,'Actual conditional loader and cone')
   need(x<1<<length<=2*x,'Canonical binary length condition');count['conditional_four_gate_loader_words']+=1
 # The known padding obstruction remains present in this generalized compiler.
 widths=(1,1);rules={(p,y):(0,0) for p,y in itertools.product((0,1),(0,1))};q=program(widths,rules,None);b=block(2,0,1,'E',None)
 w1,p1=generation(b,0,q);w2,p2=generation(w1,p1,q)
 need(w2==b+b and p2==588,'Old nonhalting doubling phase')
 steps,phase=fifo(b+(0,)*6,0,q,2274);need(steps==2274,'Same numeral padded input still halts')
 count['retained_padding_counterexamples']=1
 return dict(status='PASS',pins=PINS,checks=dict(count),cleanup_digest=digest.hexdigest(),valid_new_FIFO_fixtures=fifo_records,
             primary_sources={'Grill':'https://esolangs.org/wiki/Grill_Tag','Genera':'https://esolangs.org/wiki/Genera_Tag','revision_footers':[181950,182460]},
             scope='Independent general proofread plus bounded whole-table/word/FIFO evidence. Valid encoded halting iff only; exact width still required; no full universal source or arithmetic bound.')
def main():
 p=argparse.ArgumentParser();p.add_argument('--source',type=Path,required=True);p.add_argument('--receipt',type=Path,required=True);p.add_argument('--root',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();o=run(a.source,a.receipt,a.root)
 if a.expect:need(exact(o,json.loads(a.expect.read_text())),'Exact saved receipt')
 if a.output:a.output.write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':o['status'],'checks':o['checks']},sort_keys=True))
if __name__=='__main__':main()
