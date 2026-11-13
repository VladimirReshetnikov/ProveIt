#!/usr/bin/env python3
"""Exact fixed-payload scalar boundary, not a complete graph valuation."""
from hashlib import sha256
from pathlib import Path
import gzip,json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1]
C=D/'candidates/ten-positive-qcube-product-square/coefficients'
G=D/'research/trace74-mask-coordinate-probe/candidate.json'
sha=lambda b:sha256(b).hexdigest()
pins={'beta':('07d42a69e7593ac08bcb2957c965c02f179588b0c3b232c3c640258d0aaeab04','0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d'),'MC':('71ecc4fe568471f83978d00ee7a4e03614203d6af36611c0660dbd4fd3eb2276','6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4'),'MF_source':('ea069f55029bab743997b0a79b0535d5ad558686848a03cb41d72faf596a6a6a','48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737')}
assert sha(G.read_bytes())=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'
vals={}
for n,(gzsha,rawsha) in pins.items():
 rawgz=(C/(n+'.bin.gz')).read_bytes();assert sha(rawgz)==gzsha
 raw=gzip.decompress(rawgz);assert sha(raw)==rawsha
 vals[n]=int.from_bytes(raw,'little')
beta,L,MF=vals['beta'],vals['MC'],vals['MF_source'];d=67*8807;q=beta+1;high=MF-beta
assert beta>=31 and q==1<<d and 0<=L<beta and 0<=high<beta
assert q%4==0 and L%4==2
# Exact candidate graph equations for the selected J,F,C, using only the R and c dependency cones.
rows=json.loads(G.read_text())['source'];op={row[0]:row[1:] for row in rows};assert len(op)==74
seed={'beta':beta,'K0':0,'MC':L,'MF':MF,'J':1,'F':3,'C':q-3,'w':1,'s':1,'i':1,'T':1,'n':1,'eta':1,'zeta':1}
def value(name,cache):
 if type(name) is int:return name
 if name in cache:return cache[name]
 operation,a,b=op[name];a=value(a,cache);b=value(b,cache)
 r=a+b if operation=='+' else a-b if operation=='-' else a*b
 cache[name]=r;return r
cache=dict(seed);R=value('R',cache);expectedG=(q-1)*(q-3)
assert value('G',cache)==expectedG and seed['F']+seed['C']==q
assert R==q**4-4*q**3+3*q*q+3*q+L-3+q*high
assert R%4==3 and 3*q<R and R+q**3+q+1<q**4
# General rank-window margin, valid for every q>=32 and L,high<=q-2.
margin=q**4-(R+q**3+q+1)
assert margin==3*q**3-3*q*q-4*q+2-L-q*high
assert margin>=3*q**3-4*q*q-5*q+4>0
# Choose a positive s only for the independent scalar c-size bound.
seed['s']=R+1;cache=dict(seed);c=value('c',cache);Y=value('Y',cache)
assert Y==q**3*(R+1) and c==2*Y+1 and 2*R<c
assert R>=d
print(json.dumps({'status':'PASS_SCALAR_ONLY','ports_source':'pinned beta/MC/MF_source coefficient payloads; K0 does not occur in rank or c cone','q_exponent':d,'q_bits':q.bit_length(),'rank_bits':R.bit_length(),'q_mod_4':q%4,'MC_mod_4':L%4,'rank_mod_4':R%4,'J':1,'F':3,'C':'q-3','guard':'F+C=q','rank_gt_3q':True,'rank_plus_q3_q_1_lt_q4':True,'c_gt_2rank':True,'s':'R+1','eta':1,'zeta':1,'graph_sha256':sha(G.read_bytes()),'scope':'exact fixed payload scalar assignment and selected candidate graph cones only; no full graph output, Pell condition, fixed-port zero, iPRA or external Lean/file binding'},sort_keys=True))
