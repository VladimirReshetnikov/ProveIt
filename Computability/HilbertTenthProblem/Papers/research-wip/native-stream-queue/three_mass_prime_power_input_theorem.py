#!/usr/bin/env python3
"""Exact source-level evidence for a prime-power reversible input theorem.
No universal table, arithmetic circuit bound, or giant mass/Pell witness emitted.
"""
import argparse,hashlib,json
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PAPER_SHA='81677dd609d5b2c111c83fc5768382dbc14b54b1bf212a0b3fe828aca1b6c999'
PAPER_URL='https://www.mobt3ath.com/uplode/book/book-94727.pdf?download=1'
DOI='https://doi.org/10.1016/S0304-3975(96)00081-3'
PRIMES=(2,3,5,7,11,13,17)
def need(x,m):
 if not x:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def validate(k,rows,entry,exits,reversible=False):
 need(type(k)is int and k>0 and type(rows)is list,'schema')
 need(len({tuple(r) for r in rows})==len(rows),'duplicate')
 for r in rows:
  need(type(r)is list and len(r)==4,'row')
  s,i,op,t=r;need(type(s)is str and type(t)is str and type(i)is int and 0<=i<k and op in ('Z','P','+','-','0'),'row type')
 for position in (0,3) if reversible else (0,):
  groups={}
  for r in rows:groups.setdefault(r[position],[]).append(r)
  for rs in groups.values():
   need(len(rs)==1 or len(rs)==2 and rs[0][1]==rs[1][1] and {r[2] for r in rs}=={'Z','P'},'separated domain/range')
 need(not any(r[3]==entry for r in rows),'incoming entry')
 need(not any(r[0] in exits for r in rows),'outgoing exit')
 return len({r[j] for r in rows for j in (0,3)})

def enabled(op,n):return op in ('+','0') or op in ('P','-') and n>0 or op=='Z' and n==0

def run(rows,entry,values,exits,limit=3000000,boundaries=()):
 table={}
 for s,i,op,t in rows:table.setdefault(s,[]).append((i,op,t))
 c=list(values);q=entry;steps=0;trace=[(q,tuple(c))] if q in boundaries else []
 while q not in exits:
  found=[r for r in table.get(q,[]) if enabled(r[1],c[r[0]])]
  need(len(found)<=1,'nondeterministic run')
  if not found:return {'halt':False,'state':q,'counters':c,'steps':steps,'boundaries':trace}
  i,op,q=found[0]
  if op=='+':c[i]+=1
  if op=='-':c[i]-=1
  steps+=1;need(steps<=limit,'finite fixture exhausted')
  if q in boundaries:trace.append((q,tuple(c)))
 return {'halt':True,'state':q,'counters':c,'steps':steps,'boundaries':trace}

def inverse(rows):
 inv={'+':'-','-':'+','Z':'Z','P':'P','0':'0'}
 return [[t,i,inv[op],s] for s,i,op,t in rows]

def prime_compile(k,rows,entry,exits):
 """Literal construction at Morita1996 pp313–316, fresh namespace per macro.
 Tests share restoring tails by original target, as required for reverse syntax.
 """
 validate(k,rows,entry,exits,True);need(k<=len(PRIMES),'finite fixture prime table')
 out=[];restores={};groups={}
 for r in rows:groups.setdefault(r[0],[]).append(r)
 def put(s,i,op,t):out.append([s,i,op,t])
 for serial,(s,rs) in enumerate(groups.items()):
  def fresh(name):return '@'+str(serial)+':'+name
  if rs[0][2] in ('Z','P'):
   i=rs[0][1];p=PRIMES[i];targets={op:t for _,_,op,t in rs}
   put(s,1,'Z',fresh('D0'))
   for r in range(p):
    put(fresh('D'+str(r)),0,'P',fresh('d'+str(r)))
    put(fresh('d'+str(r)),0,'-',fresh('D'+str(r+1)))
    op='P' if r==0 else 'Z'
    if op in targets:
     t=targets[op];key=(t,i);restores[key]=p
     put(fresh('D'+str(r)),0,'Z','@R:'+t+':'+str(r))
   put(fresh('D'+str(p)),1,'+',fresh('Bcheck'));put(fresh('Bcheck'),1,'P',fresh('D0'))
   continue
  _,i,op,t=rs[0];p=PRIMES[i]
  if op=='0':put(s,0,'0',t);continue
  put(s,1,'Z',fresh('L'));put(fresh('L'),0,'Z',fresh('H'));put(fresh('L'),0,'P',fresh('dA'))
  put(fresh('dA'),0,'-',fresh('iB'));put(fresh('iB'),1,'+',fresh('backB'));put(fresh('backB'),1,'P',fresh('L'))
  put(fresh('H'),1,'Z',t);put(fresh('H'),1,'P',fresh('work0'))
  if op=='+':
   put(fresh('work0'),1,'-',fresh('work1'))
   for j in range(p):put(fresh('work'+str(j+1)),0,'+',fresh('work'+str(j+2)))
   put(fresh('work'+str(p+1)),0,'P',fresh('H'))
  else:
   for j in range(p):put(fresh('work'+str(j)),1,'-',fresh('work'+str(j+1)))
   put(fresh('work'+str(p)),0,'+',fresh('work'+str(p+1)));put(fresh('work'+str(p+1)),0,'P',fresh('H'))
 for (t,i),p in restores.items():
  def r(j):return '@R:'+t+':'+str(j)
  put(r(0),1,'Z',t);put(r(0),1,'P',r('dec'));put(r('dec'),1,'-',r(p))
  for j in range(1,p+1):put(r(j),0,'+',r(str(j)+'P'));put(r(str(j)+'P'),0,'P',r(j-1))
 validate(2,out,entry,exits,True);return out

def divider(d=96,a=0,b=1):
 rows=[['entry',b,'Z','L0']]
 for j in range(d):
  rows.extend([['L'+str(j),a,'P','D'+str(j)],['D'+str(j),a,'-','incB' if j==d-1 else 'L'+str(j+1)]])
 rows.extend([['incB',b,'+','backB'],['backB',b,'P','L0'],['L0',a,'Z','transfer_entry'],['transfer_entry',a,'Z','transfer'],['transfer',b,'P','decB'],['decB',b,'-','incA'],['incA',a,'+','backA'],['backA',a,'P','transfer'],['transfer',b,'Z','done']])
 return rows

def push_rows(base,digit,a,w,entry,exit,prefix):
 def q(s):return prefix+':'+s
 r=[[entry,a,'Z',q('restore')],[entry,a,'P',q('dec')],[q('dec'),a,'-',q('add0')]]
 for j in range(base):r.append([q('add'+str(j)),w,'+',entry if j==base-1 else q('add'+str(j+1))])
 r.extend([[q('restore'),w,'P',q('decW')],[q('decW'),w,'-',q('incA')],[q('incA'),a,'+',q('restore')],[q('restore'),w,'Z',exit if digit==0 else q('digit0')]])
 for j in range(digit):r.append([q('digit'+str(j)),a,'+',exit if j==digit-1 else q('digit'+str(j+1))])
 return r

def pop_rows(base,a,w,entry,prefix):
 def q(s):return prefix+':'+s
 r=[[entry,a,'0',q('R0')]];exits=[]
 for j in range(base):
  r.extend([[q('R'+str(j)),a,'P',q('dec'+str(j))],[q('dec'+str(j)),a,'-',q('incQ') if j==base-1 else q('R'+str(j+1))],[q('R'+str(j)),a,'Z',q('restore'+str(j))]])
  r.extend([[q('restore'+str(j)),w,'P',q('dW'+str(j))],[q('dW'+str(j)),w,'-',q('iA'+str(j))],[q('iA'+str(j)),a,'+',q('restore'+str(j))],[q('restore'+str(j)),w,'Z',q('exit'+str(j))]])
  exits.append(q('exit'+str(j)))
 r.append([q('incQ'),w,'+',q('R0')]);return r,exits

def unary_loader(base):
 r=[['entry',0,'0','loop'],['loop',0,'Z','done'],['loop',0,'P','consume'],['consume',0,'-','push']]
 r+=push_rows(base,1,1,2,'push','loop','unary_push');return r

def paired_unary_loader(base):
 need(base>=3,'separator digit')
 r=[['entry',0,'0','Eloop'],['Eloop',1,'Z','separator'],['Eloop',1,'P','Econsume'],['Econsume',1,'-','Epush']]
 r+=push_rows(base,1,3,4,'Epush','Eloop','pairE')
 r+=push_rows(base,2,3,4,'separator','Xloop','pairSep')
 r+=[['Xloop',0,'Z','done'],['Xloop',0,'P','Xconsume'],['Xconsume',0,'-','Xpush']]
 r+=push_rows(base,1,3,4,'Xpush','Xloop','pairX');return r

def code(values):
 n=1
 for p,e in zip(PRIMES,values):n*=p**e
 return n

def verify(paper=None):
 if paper is not None:need(sha(Path(paper).read_bytes())==PAPER_SHA,'reviewed primary PDF pin')
 counts={'prime_macro_cases':0,'prime_macro_inverse_cases':0,'full_encoded_simulations':0,'source_boundary_checks':0,'divider_cases':0,'divider_inverse_cases':0,'stack_push_cases':0,'stack_pop_cases':0,'unary_load_cases':0,'paired_unary_load_cases':0,'composed_preprocessor_cases':0,'scaled_interface_cases':0}
 macro_metadata=[]
 for i,p in enumerate(PRIMES[:5]):
  for kind in ('+','-','Z','P','both','0'):
   rows=([['in',i,'Z','zero'],['in',i,'P','positive']] if kind=='both' else [['in',i,kind,'done']]);exits={'zero','positive'} if kind=='both' else {'done'}
   compiled=prime_compile(i+1,rows,'in',exits);macro_metadata.append({'prime':p,'kind':kind,'states':len({r[j] for r in compiled for j in (0,3)}),'instructions':len(compiled),'rows_sha256':sha(json.dumps(compiled,separators=(',',':')).encode())})
   for n in range(1,65):
    got=run(compiled,'in',[n,0],exits);ok=(kind not in ('-','P','Z') or (n%p!=0 if kind=='Z' else n%p==0))
    need(got['halt']==ok,'prime guard/halting')
    if ok:
     expected=n*p if kind=='+' else n//p if kind=='-' else n;need(got['counters']==[expected,0],'macro boundary')
     if kind=='both':need(got['state']==('positive' if n%p==0 else 'zero'),'test output')
     back=run(inverse(compiled),got['state'],got['counters'],{'in'});need(back['halt'] and back['counters']==[n,0] and back['steps']==got['steps'],'macro inverse');counts['prime_macro_inverse_cases']+=1
    counts['prime_macro_cases']+=1
 # This is Morita's seven-quadruple source example, not a universal table.
 source=[['q0',1,'Z','q1'],['q1',0,'Z','halt'],['q1',0,'P','q2'],['q2',0,'-','q3'],['q3',1,'+','q4'],['q4',2,'+','q5'],['q5',1,'P','q1']]
 compiled=prime_compile(3,source,'q0',{'halt'});need(len(compiled)==93,'paper example93')
 states={r[j] for r in source for j in (0,3)};examples=[]
 for n in range(5):
  a=run(source,'q0',[n,0,0],{'halt'},boundaries=states);b=run(compiled,'q0',[2**n,0],{'halt'},boundaries=states)
  need(a['halt'] and b['halt'] and a['counters']==[0,n,n] and b['counters']==[15**n,0],'full example')
  wanted=[(q,(code(c),0)) for q,c in a['boundaries']];need(b['boundaries']==wanted,'every actual original-state boundary')
  counts['source_boundary_checks']+=len(wanted);counts['full_encoded_simulations']+=1
  examples.append({'input_exponent':n,'encoded_input':2**n,'encoded_output':15**n,'microsteps':b['steps'],'original_steps':a['steps'],'boundary_count':len(wanted)})
 for d in (1,2,3,5,96):
  rows=divider(d,0,2);validate(3,rows,'entry',{'done'},True)
  for n in range(0,201):
   sentinel=17;v=run(rows,'entry',[n,sentinel,0],{'done'});need(v['halt']==(n%d==0),'division guard')
   if v['halt']:
    need(v['counters']==[n//d,sentinel,0] and v['steps']==(2*d+6)*(n//d)+4,'division boundary/steps')
    back=run(inverse(rows),'done',v['counters'],{'entry'});need(back['halt'] and back['counters']==[n,sentinel,0],'division inverse');counts['divider_inverse_cases']+=1
   counts['divider_cases']+=1
 for base in range(2,7):
  for digit in range(base):
   rows=[['entry',0,'0','push']]+push_rows(base,digit,0,1,'push','done','push');validate(2,rows,'entry',{'done'})
   for n in range(41):
    v=run(rows,'entry',[n,0],{'done'});need(v['halt'] and v['counters']==[base*n+digit,0],'stack push');counts['stack_push_cases']+=1
  rows,exits=pop_rows(base,0,1,'entry','pop');validate(2,rows,'entry',set(exits))
  for n in range(101):
   v=run(rows,'entry',[n,0],set(exits));need(v['halt'] and v['counters']==[n//base,0] and v['state']==exits[n%base],'stack pop');counts['stack_pop_cases']+=1
  rows=unary_loader(base);validate(3,rows,'entry',{'done'})
  for n in range(7):
   v=run(rows,'entry',[n,0,0],{'done'});need(v['halt'] and v['counters']==[0,(base**n-1)//(base-1),0],'unary initialization');counts['unary_load_cases']+=1

 for base in range(3,7):
  rows=paired_unary_loader(base);validate(5,rows,'entry',{'done'})
  for x in range(3):
   for e in range(3):
    got=run(rows,'entry',[x,e,0,0,0],{'done'});want=(base**e-1)//(base-1)*base**(x+1)+2*base**x+(base**x-1)//(base-1)
    need(got['halt'] and got['counters']==[0,0,0,want,0],'paired ordinary tape input');counts['paired_unary_load_cases']+=1
 for x in range(1,4):
  for e in range(4):
   first=run(divider(96,0,2),'entry',[96*x,e,0,0,0],{'done'});need(first['halt'] and first['counters']==[x,e,0,0,0],'pre-Morita divide96 preserves program')
   second=run(paired_unary_loader(3),'entry',first['counters'],{'done'});value=second['counters'][3];word=[]
   while value:value,digit=divmod(value,3);word.append(digit)
   need(word==[1]*x+[2]+[1]*e and second['counters'][:3]==[0,0,0] and second['counters'][4]==0,'composed exact ordinary input word');counts['composed_preprocessor_cases']+=1
 for x in (1,2,3,7):
  for e in range(5):
   C=3**e;Q1=2**(96*x);valuation=96*C*Q1;prime_input=valuation//96
   need(prime_input==code([96*x,e,0,0,0]),'double exponent valuation map');counts['scaled_interface_cases']+=1
 return {'status':'PASS_PRIME_POWER_INPUT_EVIDENCE','source_sha256':sha(Path(__file__).read_bytes()),'primary':{'doi':DOI,'reviewed_pdf_url':PAPER_URL,'reviewed_pdf_sha256':PAPER_SHA,'theorem3_1_printed_page':308,'theorem4_1_printed_page':313,'macro_printed_pages':[314,315,316],'paper_pin_check':'Optional --paper checks these exact reviewed bytes; replay otherwise checks mathematics without refetching.'},'counts':counts,'prime_macros':macro_metadata,'paper_example_source':source,'paper_example_compiled_instructions':len(compiled),'paper_example_cases':examples,'divider96_states':validate(3,divider(96,0,2),'entry',{'done'},True),'divider96_instructions':len(divider(96,0,2)),'interfaces':{'per_language_reversible_input':'(2^(96*x),0)','two_layer_mass_valuations':'(96*C*2^(96*x),0)','valid_program_slice':'C=3^e; external divide96 yields prime code of(96*x,e,0,...)','ordinary_domain':'positive integer x; natural e'},'scope':'Finite macro/initialization evidence supports the separately written general source proof and cited primary theorems. No literal universal table, universal arithmetic bound, huge mass, or full native Pell witness is supplied.'}

def main():
 p=argparse.ArgumentParser();p.add_argument('--paper',type=Path);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.paper);r=json.loads(json.dumps(r))
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()
