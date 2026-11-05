#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2]; P=D/'research/normalized106-rational66-lean'; O=P/'observations/attempt03'
def H(f): return hashlib.sha256(f.read_bytes()).hexdigest()
def need(v,msg):
 if not v: raise RuntimeError(msg)
pins={'Normalized106Rational66.lean':'99b0d71b27771ed5416e295f28f6d1668a4c5a7cdbf8a756a7ac19b513129f42','audit_rows.py':'3a9ae46e45d075a020339835bcd9eab6d9d0ef95aa05befc0872a5ea75d8ecc0','check03.py':'782495e146f6b69271b0c7878a2552af3c8c01442f0de045c788e3edc15cc820','build_lean.py':'59976f3ec7825211ab45a0c72ab0224272a8b49f5a24a301a368e1f40c1f3a30','observations/attempt03/result.json':'6a172e130db1dac5c48afa6f0f9256231bfa9a23c3b748e5d7b0ee448922db42','observations/attempt03/outer-terminal.json':'6d187c4da73a36eeff779373c9906bac9a593c35813baba548d0a12bc82b5a38'}
for f,h in pins.items(): need(H(P/f)==h,'pin '+f)
s=(P/'Normalized106Rational66.lean').read_text(); a=json.loads((D/'research/normalized106-rational66/polynomial.json').read_text()); b=json.loads((D/'research/fourteen-normalized-product106/polynomial.json').read_text()); need(a['witnesses']==b['witnesses'],'witness order'); aa=a['source'];bb=b['source']; need((len(aa),len(bb))==(66,67),'row count')
# Separate row parser: exact ordered operation assignments within each Lean definition.
segs={}
for name,nextname in [('head','rank66'),('rank66','rank67'),('rank67','suffix'),('suffix','value66')]:
 body=s.split('\ndef '+name+' ',1)[1].split('\ndef '+nextname+' ',1)[0]; segs[name]=body
 def cv(x): return int(x) if x.isdecimal() else x
 rows=[]
 for line in body.splitlines():
  m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line)
  if m:
   n,x,op,y=m.groups();rows.append([n,op,cv(x),cv(y)])
 if name=='head': exp=aa[:28]
 elif name=='rank66': exp=aa[28:33]
 elif name=='rank67': exp=bb[28:34]
 else: exp=aa[33:]
 need(rows==exp,'graph rows '+name)
need(aa[:28]==bb[:28] and aa[33:]==bb[34:],'shared regions')
fields=[x[0] for x in aa[:28]]
need('  ⟨'+', '.join(fields)+'⟩' in segs['head'],'head output')
for name,rows in [('head',aa[:28]),('suffix',aa[33:])]:
 used={str(v) for row in rows for v in row[2:]}
 for i,w in enumerate(a['witnesses']):
  if w in used: need(f'  let {w} := v {i}\n' in segs[name],'witness alias '+name+' '+w)
 for i,w in enumerate(['beta','K0','MC','MF']):
  if w in used: need(f'  let {w} := p {i}\n' in segs[name],'port alias '+name+' '+w)
for name,rows in [('rank66',aa[28:33]),('rank67',bb[28:34]),('suffix',aa[33:])]:
 used={str(v) for row in rows for v in row[2:]}
 for fld in fields:
  if fld in used: need(f'  let {fld} := h.{fld}\n' in segs[name],'field alias '+name+' '+fld)
need('  let R := rank\n' in segs['suffix'],'rank alias')
r=json.loads((O/'result.json').read_text()); t=json.loads((O/'outer-terminal.json').read_text()); need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'],'terminal state');need(t['session_id']==5881 and t['terminal_exit_code']==0 and t['returned_session_id'] is None,'outer exit');need(r['guards_before']==r['guards_after'],'guard stability')
for f,meta in r['guards_after'].items():
 p=Path(f.removeprefix('producer:'))
 if meta is None: need(not os.path.lexists(p),'unexpected path '+f)
 else:
  target=meta.get('realpath',meta.get('resolved')); need(p.is_file() and str(p.resolve())==target and H(p)==meta['sha256'],'current guard '+f)
  if 'link' in meta: need((os.readlink(p) if p.is_symlink() else None)==meta['link'],'link guard '+f)
need(H(O/'compile.log')==r['log_sha256']=='36548a4562d7b3a6bacacd89a2a50e273b9245866bdb25db5a5e487322614a74','log hash')
log=(O/'compile.log').read_text(); need('sorryAx' not in log and 'warning:' not in log and 'error:' not in log,'diagnostics');need(log.count('depends on axioms:')==3 and log.count('[propext, Quot.sound]')==2 and log.count('[propext]')==1,'axiom reports')
obj=Path('/tmp/normalized106-rational66-lean-priority-check03/Normalized106Rational66.olean');need(H(obj)==r['object_sha256']=='6978d8ef65c4cb77311bd9028143b4c6af95847e103a966936694eedc6890299','output object')
providers=[(k,v) for k,v in r['guards_after'].items() if k.endswith('/ModelCarrierSyntax.olean') and v is not None];need(len(providers)>=1 and all(v['sha256']=='9eaaefb9b4121df6d9c8f6f1c5feef1cc837fc38f51a831a005db072bdaaf900' for _,v in providers),'syntax object')
x=subprocess.run([sys.executable,'-I','-S','-B',str(P/'audit_rows.py')],capture_output=True,text=True);need(x.returncode==0 and x.stdout==(P/'row-audit.txt').read_text(),'author row rerun')
print(json.dumps({'status':'PASS_READ_ONLY_INDEPENDENT_REVIEW','literal_rows':[66,67],'direct_guards':len(r['guards_after']),'outer_session':5881,'outer_exit':0,'lean_child_exit':0,'author_row_check_exit':x.returncode,'scope':'Pointwise commutative ring identity under two fixed leaf equations; stage-078 historical direct provider, no Lean replay or new transitive ancestry.'},indent=2,sort_keys=True))
