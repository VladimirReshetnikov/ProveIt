#!/usr/bin/env python3
"""Complete fixed NAND DAG for the U15-derived radius-half CA marker cell.
This is a Boolean cell specification, not yet a literal ant atlas.
"""
if not __debug__:raise RuntimeError('Assertions required')
import hashlib,itertools,json,pathlib,random
ROOT=pathlib.Path(__file__).resolve().parent
PINS='0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a'
B=(ROOT/'u15_table.json').read_bytes();assert hashlib.sha256(B).hexdigest()==PINS
TM=json.loads(B);STATES='ABCDEFGHIJKLMNO';HALT=21

def g_spec(left,center,right):
 def trans(code):return TM[STATES[(code-2)//2]+str(code%2)]if code>=2 else None
 if center>=2:
  tr=trans(center);return center if tr is None else tr[0]
 for neighbor,direction in[(left,'R'),(right,'L')]:
  tr=trans(neighbor)
  if tr is not None and tr[1]==direction:return 2+2*STATES.index(tr[2])+center
 return center

def pair(a,b):return 0 if a==b==0 else 1024+32*a+b

def f_spec(left,right):
 if left<32 and right<32:return pair(left,right)
 def valid_b(x):return x==0 or 1025<=x<2048
 if valid_b(left)and valid_b(right):
  la,lb=(0,0)if left==0 else((left-1024)//32,(left-1024)%32)
  ra,rb=(0,0)if right==0 else((right-1024)//32,(right-1024)%32)
  return g_spec(la,lb,rb)if lb==ra else 0
 return 0

class DAG:
 def __init__(self,n):
  self.n=n;self.rows=[];self.cache={}
  self.ONE=self.nand(0,self.NOT(0));self.ZERO=self.NOT(self.ONE)
 def nand(self,a,b):
  key=tuple(sorted((a,b)))
  if key not in self.cache:self.cache[key]=self.n+len(self.rows);self.rows.append(list(key))
  return self.cache[key]
 def NOT(self,a):return self.nand(a,a)
 def AND(self,a,b):return self.NOT(self.nand(a,b))
 def OR(self,a,b):return self.nand(self.NOT(a),self.NOT(b))
 def ALL(self,xs):
  v=self.ONE
  for x in xs:v=self.AND(v,x)
  return v
 def ANY(self,xs):
  v=self.ZERO
  for x in xs:v=self.OR(v,x)
  return v
 def eq(self,bits,n):return self.ALL([v if(n>>i)&1 else self.NOT(v)for i,v in enumerate(bits)])
 def MUX(self,c,a,b):return self.OR(self.AND(c,a),self.AND(self.NOT(c),b))
 def eval(self,inp):
  env=list(inp)
  for a,b in self.rows:env.append(1-env[a]*env[b])
  return env

def build():
 d=DAG(24);actual=[d.NOT(i)for i in range(24)] # required first header NOT layer
 L=actual[:11];s0,s1=actual[11:13];R=actual[13:]
 L=[d.AND(v,d.NOT(s1))for v in L] # exact ignored-left boundary case
 def g(l,c,r):
  center_head=d.ANY(c[1:]);halt=d.eq(c,HALT)
  def decode(bits,direction):
   match=[];nextcode=[]
   for qi,q in enumerate(STATES):
    for bit in[0,1]:
     tr=TM[q+str(bit)]
     if tr is not None and tr[1]==direction:
      match.append(d.eq(bits,2+2*qi+bit));nextcode.append(2+2*STATES.index(tr[2]))
   return d.ANY(match),[d.ANY(v for v,n in zip(match,nextcode)if(n>>k)&1)for k in range(5)]
  fromleft,leftbits=decode(l,'R');fromright,rightbits=decode(r,'L')
  writes=d.ANY(d.eq(c,2+2*qi+bit)for qi,q in enumerate(STATES)for bit in[0,1]if TM[q+str(bit)]is not None and TM[q+str(bit)][0]==1)
  out=[d.MUX(center_head,d.MUX(halt,c[0],writes),c[0])]
  for k in range(1,5):
   arrival=d.OR(leftbits[k],d.AND(d.NOT(fromleft),rightbits[k]))
   out.append(d.OR(d.AND(halt,c[k]),d.AND(d.NOT(center_head),arrival)))
  return out
 def valid_A(bits):return d.ALL(d.NOT(v)for v in bits[5:])
 def valid_B(bits):return d.OR(d.eq(bits,0),d.AND(bits[10],d.ANY(bits[:10])))
 fa=d.AND(valid_A(L),valid_A(R))
 eqmiddle=d.ALL(d.NOT(d.OR(d.AND(a,d.NOT(b)),d.AND(d.NOT(a),b)))for a,b in zip(L[:5],R[5:10]))
 fb=d.ALL([valid_B(L),valid_B(R),eqmiddle])
 gbits=g(L[5:10],L[:5],R[:5])
 f=[d.OR(d.AND(fa,R[i]),d.AND(fb,gbits[i]))for i in range(5)]
 f +=[d.AND(fa,L[i])for i in range(5)]
 f +=[d.AND(fa,d.ANY(L+R))]
 phi=[s1]+f+f+[d.AND(s0,d.NOT(s1))]
 outputs=[d.NOT(v)for v in phi] # required final footer NOT layer
 halt=d.eq(f,HALT)
 return d,outputs,halt,f

def bits(n,width):return[(n>>i)&1 for i in range(width)]
def decode(bits):return sum(b<<i for i,b in enumerate(bits))
def main():
 d,outputs,halt,fports=build();counts={'primary_pairs':0,'consistent_pair_triples':0,'boundary_cases':0,'other_total_function_cases':0}
 def check(l,r,s0=0,s1=0):
  actual=bits(l,11)+[s0,s1]+bits(r,11)
  env=d.eval([1-b for b in actual]);raw=[env[i]for i in outputs]
  wantf=f_spec(0 if s1 else l,r)
  want=[s1]+bits(wantf,11)*2+[s0*(1-s1)]
  assert[1-b for b in raw]==want,(l,r,s0,s1)
  assert decode([env[i]for i in fports])==wantf
  assert env[halt]==int(wantf==HALT)
 for l,r in itertools.product(range(32),repeat=2):check(l,r);counts['primary_pairs']+=1
 for l,c,r in itertools.product(range(32),repeat=3):check(pair(l,c),pair(c,r));counts['consistent_pair_triples']+=1
 for r,s0,l in itertools.product(range(2048),[0,1],[0,2047]):check(l,r,s0,1);counts['boundary_cases']+=1
 rng=random.Random(20261003)
 for _ in range(4096):check(rng.randrange(2048),rng.randrange(2048),rng.randrange(2),rng.randrange(2));counts['other_total_function_cases']+=1
 # Exhaustive primary transition table and its local halt persistence.
 assert all(g_spec(l,21,r)==21 for l,r in itertools.product(range(32),repeat=2))
 packet={'status':'PASS_COMPLETE_FIXED_BOOLEAN_CA_CELL_ONLY','physical_ant_cell_emitted':False,'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
  'u15_table_sha256':PINS,'u15_program_compiler':'Not implemented; fixed machine transition table only',
  'primary_state_code':'unheaded bit a maps to a; head(q,a) maps to2+2*index(q)+a for states A..O. J1=21 is frozen on halt.',
  'radius_half_state_code':'Primary a∈[0,31] remains a; pair(a,b) is0 for a=b=0 and1024+32a+b otherwise. All remaining codes have total default behavior specified in f_spec.',
  'input_count':24,'input_order':'complemented xL[0..10],s0,s1,xR[0..10], little-endian state bits, supplied after first NOT header',
  'nand_gates':d.rows,'gate_count':len(d.rows),'complemented_phi_outputs':outputs,'halt_wire':halt,'f_outputs':fports,
  'proof_outline':'Each listed row is NAND of earlier wires. Literal helper identities define Boolean NOT/AND/OR/MUX. On primary states f emits the adjacent pair. On consistent pair states it applies the radius-one TM update to the shared center; direct enumeration covers all32768 primary triples. A zero symbol serves both phases, and f(0,0)=0. Under a unique-head well-formed tape, one primary→pair→primary cycle implements one TM step, with J1 fixed forever. Masking all left bits by not(s1) makes the boundary branch exactly f(0,xR), independent of skipped xL and s0. Duplicated f outputs and marker outputs implement phi; footer NOT recovers them. The halt bit is exactly[f=21], not an ant halt event.',
  'checks':counts,'universality_scope':'The Boolean circuit is fully explicit for the fixed U15-derived CA. Its physical ant layout, growing marker sweep, finite input map and exclusive head-port observer remain to be assembled.'}
 (ROOT/'fixed_ca_cell.json').write_text(json.dumps(packet,indent=2)+'\n')
 print(json.dumps({'status':packet['status'],'NAND_gates':len(d.rows),'checks':counts}))
if __name__=='__main__':main()
