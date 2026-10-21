#!/usr/bin/env python3
"""Owned read-only intake audit. Never imports or executes received code."""
import hashlib,json,pathlib,zipfile
P=pathlib.Path(__file__).resolve().parent
if not __debug__:raise SystemExit('Assertions must be enabled')
data=(P/'received.zip').read_bytes()
assert hashlib.sha256(data).hexdigest()=='ab3c6c40a6c8da7fe6dbbfa35a35c204df904137463c6667b3d989991ed1c2c0'
z=zipfile.ZipFile(P/'received.zip');root='Proof_Simplification_and_GC-ZC215_2026-10-21/'
def read(path):return z.read(root+path)
def js(path):return json.loads(read(path))
def sha(data):return hashlib.sha256(data).hexdigest()
manifest=js('MANIFEST.json')
for name,pin in manifest.items():
 b=read(name);assert len(b)==pin['bytes'] and sha(b)==pin['sha256'],name
names={n[len(root):] for n in z.namelist() if not n.endswith('/')}
assert names==set(manifest)|{'MANIFEST.json'}
def table(path):
 b=read(path);start=None;t={}
 for line in b.decode().splitlines():
  if line.startswith('#! start '):start=int(line.split()[-1])
  if not line or line.startswith('#'):continue
  q,r,w,d,n=line.split();q,r,w,n=map(int,(q,r,w,n));assert d in ('L','R') and r in (0,1) and w in (0,1)
  assert(q,r) not in t;t[q,r]=(w,1 if d=='R' else -1,n)
 states={q for q,r in t};assert set(t)=={(q,r) for q in states for r in [0,1]}
 terminal={n for w,d,n in t.values()}-states;assert len(terminal)==1
 return t,start,terminal.pop()
a,sa,ha=table('hybrid215/machine.native.tm');d,sd,hd=table('hybrid215/gc_zc215.canonical.tm')
hist,sh,hh=table('hybrid215/runtime_input.reference.tm')
assert len(a)==430 and sa==74 and ha==254 and sd==0 and hd==254
assert a==hist and sh==0
mapping={int(k):v for k,v in js('hybrid215/GC_ZC215_CANONICAL.json')['native_to_canonical'].items()}
assert len(mapping)==len(set(mapping.values()))==216
assert {(mapping[q],r):(w,move,mapping[n]) for(q,r),(w,move,n)in a.items()}==d
assert mapping[sa]==sd and mapping[ha]==hd
root_receipt=js('hybrid215/GC_ZC215_BLANK_ROOT.json');steps=root_receipt['steps'];assert steps==117004
q,h,ones=sa,0,set()
for _ in range(steps):
 w,move,q=a[q,int(h in ones)]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=move
assert(q,h,sorted(ones))==(root_receipt['state'],root_receipt['head'],root_receipt['ones'])
# A separate byte-array replay on the canonical table.
q2,h2=sd,steps+2;tape=bytearray(2*steps+5)
for _ in range(steps):
 w,move,q2=d[q2,tape[h2]];tape[h2]=w;h2+=move
assert q2==mapping[q] and h2-steps-2==h
assert {i-steps-2 for i,b in enumerate(tape) if b}==ones
# Independent complete frame construction using physical order W,L,T,D,A,Y,N,H,X.
regs=root_receipt['registers'];assert regs==[1,0,5,0,0,0,0,0,0]
values=[regs[i] for i in [2,8,1,4,3,7,0,5,6]]+root_receipt['spares']
header=h+64+root_receipt['gap'];expected={h-1,header}|{h+i for i,b in enumerate(root_receipt['pc']) if b=='1'}
pos=header+1
for v in values:
 expected.update(range(pos+1,pos+v+2));pos+=v+2
assert expected==ones
blank_state=q
sites=js('hybrid215/source.sites.json');oldsites=js('hybrid215/zc215.reference.sites.json')
changes=[i for i,(x,y)in enumerate(zip(oldsites,sites)) if x!=y]
assert len(sites)==len(oldsites)==4752 and changes==[46,51]
assert oldsites[46][1:]==['CD',4] and oldsites[51][1:]==['CI',4]
assert sites[46][1:]==['CD',3] and sites[51][1:]==['CI',3]
assert all(x[0:2]==y[0:2] for x,y in zip(oldsites,sites))
assert root_receipt['pc']==sites[0][0]=='000'
leaves={x[0]:tuple(x[1:]) for x in sites};seen=set()
def walk(path):
 t=('leaf',*leaves[path]) if path in leaves else ('pair',walk(path+'0'),walk(path+'1'))
 seen.add(t);return t
walk('')
# Inspect the exact local merge against the included unmerged reference.
u,su,hu=table('hybrid215/unmerged216.reference.tm')
assert len(u)==432 and hu==254
phi=lambda q:129 if q==303 else q
for (q,b),(w,m,n) in u.items():
 if q not in [129,303]:assert a[q,b]==(w,m,phi(n))
origins={str(t):[[q,b,w,m] for(q,b),(w,m,n)in u.items() if n==t] for t in [129,303]}
assert origins=={'129':[[211,1,1,1]],'303':[[135,0,0,1]]}
lengths=[]
for old,left in [(129,1),(303,0)]:
 for b in [0,1]:
  w,m,n=u[old,b];cells={-1:left,0:b};q3,h3=129,0
  for k in range(1,7):
   assert h3 in cells
   ww,mm,nn=a[q3,cells[h3]];cells[h3]=ww;h3+=mm;q3=nn
   if(q3,h3)==(phi(n),m):break
  assert(q3,h3,cells)==(phi(n),m,{-1:left,0:w})
  lengths.append([old,b,k])
rt=js('hybrid215/GC_ZC215_RUNTIME.json')
assert rt['table_sha256']==sha(read('hybrid215/runtime_input.reference.tm'))
assert rt['source_sha256']==sha(read('hybrid215/source.sites.json'))
assert rt['cases']==rt['expected_cases']==6177 and rt['row_coverage']==430
result={'status':'INDEPENDENT_FINITE_INTAKE_PASS','manifest_files':len(manifest),'received_code_executed':False,'kernel_compilation':False,'full_runtime_rederived':False,'native_sha256':sha(read('hybrid215/machine.native.tm')),'canonical_sha256':sha(read('hybrid215/gc_zc215.canonical.tm')),'source_sha256':sha(read('hybrid215/source.sites.json')),'working_states':215,'native_start':sa,'canonical_start':sd,'halt_label':254,'canonical_bijection':True,'header_only_repair':True,'blank_steps':steps,'blank_native_state':blank_state,'blank_head':h,'whole_tape_and_frame_equal':True,'one_cells':len(ones),'source_leaves':len(sites),'source_subtrees':len(seen),'max_address_depth':max(len(x[0])for x in sites),'address_sum':sum(len(x[0])for x in sites),'changed_operands':changes,'local_merge_lengths':lengths,'runtime_receipt_hash_binding':True,'runtime_receipt_cases':6177,'scope':'Finite input integrity, exact source change, finite whole-tape local merge, canonical relabeling, independently replayed complete blank prefix/frame. Does not independently rederive full primitive runtime, source compiler, ZFC calibration, or compile Lean/Rocq prototypes.'}
(P/'independent_intake_audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
