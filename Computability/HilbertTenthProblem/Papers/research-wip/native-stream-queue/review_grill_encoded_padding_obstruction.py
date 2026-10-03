#!/usr/bin/env python3
"""Independent fixed-program/local-word/FIFO audit of the Grill padding obstruction."""
if not __debug__:raise RuntimeError('Run without -O')
import argparse,copy,hashlib,json,types
from collections import deque
from pathlib import Path
SOURCE_PIN='b7bc972967736246a7448ae7a57d9442988f3903c95718ff1ec8288a3e92fb93'
NOTE_PIN='b73de17a4dbae238860fc0f1ec106594bc4924411ac6cf11551002122f8d1dbb'
REFERENCE_PIN='66c64fc95574b4d938a3a05e443215f802825677129a17e3cd38fae4150a12f3'
RECEIPT_PIN='38fc218b4b3d9e12eda353b4ad4f97ce020bf60aa64b2ba69f6793966398e91a'

def need(v,s):
 if not v:raise ValueError(s)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def pin(p,h):need(hashlib.sha256(p.read_bytes()).hexdigest()==h,'Pinned artifact changed '+p.name)
def hashed(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def literal_instance():
 # Independent transcription of the fixed a=84, widths=(1,1), all-output-(0,0)
 # specialization; no construction or simulation function from either audited module is executed.
 g=lambda n:'0'+'10'*n
 E='0'*7+g(81)+g(7)+g(80)+'0'*242
 L='0'*81+g(7)+g(3)+g(242)
 R='0'+g(7)+g(3)+g(242)+'0'*80
 program=[0]*1176;assigned=set()
 for block in (0,588):
  for y in (0,1):
   rows=[(28*y+17,81),(28*y+19,7),(28*y+21,80),
         (28*y+97,81),(28*y+99,7),(28*y+101,80),
         (14*y+171,7),(14*y+173,3),(14*y+175,242),(14*y+177,0),
         (14*y+179,7),(14*y+181,3),(14*y+183,242)]
   for i,v in rows:
    i+=block;need(i not in assigned and 0<=i<1176,'Fixed program assignment collision');assigned.add(i);program[i]=v
 return program,E,L,R

def gen(program,word,phase):
 # Use only the one-position set, independently of the author's phase loop.
 output=''.join('0'+'10'*program[(phase+j)%len(program)] for j in range(len(word)) if word[j]=='1')
 return output,(phase+len(word))%len(program)

def fifo(program,word,steps):
 q=deque(map(int,word));trace=hashlib.sha256();phase=0
 for t in range(steps):
  need(len(q)>0,'Early halt in independent FIFO')
  bit=q.popleft()
  if bit:
   q.append(0)
   for _ in range(program[phase]):q.extend((1,0))
  phase=(phase+1)%len(program)
  trace.update((str(t+1)+':'+str(phase)+':'+''.join(map(str,q))+'\n').encode())
 need(not q,'Expected halt did not occur')
 return dict(first_halt=steps,terminal_phase=phase,full_trace_sha256=trace.hexdigest())

def run(source,reference,receipt):
 pin(source,SOURCE_PIN);pin(source.with_suffix('.md'),NOTE_PIN);pin(reference,REFERENCE_PIN);pin(receipt,RECEIPT_PIN)
 saved=json.loads(receipt.read_text());need(saved['source_sha256']==SOURCE_PIN and saved['reference_sha256']==REFERENCE_PIN,'Declared provenance')
 program,E,L,R=literal_instance();need(saved['fixed_program']==program and saved['corrected_blocks']==dict(E=E,L=L,R=R),'Independent literal reconstruction mismatch')
 need(program[:588]==program[588:] and len(E)==len(L)==len(R)==588,'Lengths and phase period')
 need(E.count('1')==168 and (L+R).count('1')==504 and E[-243:]=='0'*243 and E[-244]=='1','Independent bit support')
 local=[]
 for phase in (0,588):
  a,pa=gen(program,E,phase);b,pb=gen(program,L+R,phase)
  need(a==L+R and pa==(phase+588)%1176 and b==E+E and pb==phase,'Exact normal local identities')
  local.append(dict(phase=phase,E_to_LR=True,LR_to_EE=True,E_next_phase=pa,LR_next_phase=pb))
 need(saved['local_word_certificates']==local,'Saved four normal identities')
 erase=[]
 for phase in (6,594):
  out,after=gen(program,L+R,phase);need(out=='0'*504 and after==phase,'Exact shifted local identity')
  erase.append(dict(phase=phase,output_zeros=504,phase_preserved=True))
 need(saved['erasure_word_certificates']==erase,'Saved two erasure identities')
 # Set complement of forbidden phase differences is an independent residue census.
 ones=[i for i,c in enumerate(L+R) if c=='1'];nonzero=[i for i,n in enumerate(program) if n]
 forbidden={(i-588-j)%1176 for i in nonzero for j in ones}
 kill=[k for k in range(1176) if k not in forbidden]
 need(len(kill)==474 and kill[0]==6 and 0 not in kill,'Complete erasure support census')
 need(kill==saved['second_generation_erasing_padding_residues'],'All saved residue identities')
 families=[];fifo_steps=0
 for k in range(1,7):
  word=E*k;x=sum(1<<j for j,c in enumerate(word) if c=='1')
  need(x.bit_length()==588*(k-1)+345,'General-form bit length on finite examples')
  need(x>0 and 1<<len(word)>3*x and sum(1<<j for j,c in enumerate(word+'0'*6) if c=='1')==x,'Same ordinary input and strong cone')
  a,pa=gen(program,word+'0'*6,0);b,pb=gen(program,a,pa);c,pc=gen(program,b,pb)
  need(a==(L+R)*k and b=='0'*(504*k) and c=='','Three generation finite fixture')
  row=dict(encoded_blocks=k,ordinary_input=str(x),ordinary_input_bit_length=x.bit_length(),original_bit_length=len(word),padded_bit_length=len(word)+6,padded_first_halt=2268*k+6,second_generation_zero_count=504*k)
  if k<=2:row['literal_FIFO']=fifo(program,word+'0'*6,2268*k+6);fifo_steps+=2268*k+6
  need(row==saved['family'][k-1],'Saved family and complete FIFO trace mismatch');families.append(row)
 need(len(saved['family'])==6,'Unexpected family coverage')
 # The resolved receipt-comparison defect is checked independently of arithmetic.
 module=types.ModuleType('_review_obstruction_types');module.__file__=str(source);exec(compile(source.read_bytes(),str(source),'exec'),module.__dict__)
 altered=[]
 q=copy.deepcopy(saved);q['fixed_program'][0]=False;altered.append(q)
 q=copy.deepcopy(saved);q['local_word_certificates'][0]['E_to_LR']=1;altered.append(q)
 q=copy.deepcopy(saved);q['family'][0]['padded_first_halt']=float(q['family'][0]['padded_first_halt']);altered.append(q)
 for q in altered:need(q==saved and not module.exact(q,saved),'Typed receipt alias accepted')
 return dict(status='PASS',source_sha256=SOURCE_PIN,reference_sha256=REFERENCE_PIN,author_receipt_sha256=RECEIPT_PIN,author_note_sha256=NOTE_PIN,
  counts=dict(independently_reconstructed_program_entries=1176,independently_reconstructed_encoding_bits=1764,
   exact_local_word_identities=6,complete_padding_residues=1176,second_generation_erasures=474,finite_family_examples=6,literal_FIFO_first_halts=2,literal_FIFO_steps=fifo_steps,typed_receipt_alias_rejections=len(altered)),
  program_sha256=hashed(program),blocks_sha256=hashed(dict(E=E,L=L,R=R)),erasure_residues_sha256=hashed(kill),
  local_word_identities=local,erasure_word_identities=erase,family=families,
  proof_scope='Six exact local identities prove the infinite nonhalting doubling family and exact six-zero-padded first-halt formula for every k>=1. Finite samples do not substitute for induction. Only second-generation erasure residues are classified. This refutes the stated naive ordinary-input interpretation of the corrected fragment, not encoded Grill universality or all decoders.')

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 for name in ('source','reference','receipt','output'):p.add_argument('--'+name,type=Path,required=True)
 p.add_argument('--expect',type=Path);a=p.parse_args();r=run(a.source,a.reference,a.receipt)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Saved independent receipt mismatch')
 a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':r['status'],'counts':r['counts']},indent=2))
