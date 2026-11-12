#!/usr/bin/env python3
"""Independent exact graph/degree checks, not an internal or Lean proof."""
import gzip, hashlib, json, math
from pathlib import Path
D=Path(__file__).resolve().parents[2]
PARENT='ordinary14-natural-forced-gamma80'; PARENT_HASH='136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5'
CHILD='ordinary14-natural-forced-w79'; CHILD_HASH='0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'
DEGREE=107; LEADER=419359493; SHIFTED=False
def load(path,digest):
    data=path.read_bytes(); assert hashlib.sha256(data).hexdigest()==digest, path
    return json.loads(data)
p=load(D/'research'/PARENT/'candidate.json', PARENT_HASH)
c=load(D/'research'/CHILD/'candidate.json', CHILD_HASH)
assert p['domain']==c['domain']=='nonnegative integers'
assert p['witnesses']==c['witnesses'] and p['fixed_numerals']==c['fixed_numerals']
assert len(c['witnesses'])==14 and len(c['fixed_numerals'])==4
old={row[0]:row[1:] for row in p['source']}; new={row[0]:row[1:] for row in c['source']}
assert len(old)==79+1 and len(new)==79
assert old['w']==['+','n_w',1] and set(old)-set(new)=={'w'} and set(new)<=set(old)
for name,row in new.items():
    op,left,right=old[name]
    assert row==[op,'n_w' if left=='w' else left,'n_w' if right=='w' else right], name
# Confirm exact DAG shapes for J=0 and w=0, unit extraction and main norm.
shape={
 'alpha':['+','n_alpha',1], 's':['+','n_s',1], 'qm':['*','n_J','beta'],
 'q':['+',1,'qm'], 'X':['*','q','n_w'], 'q2':['*','q','q'],
 'q3':['*','q','q2'], 'Y':['*','q3','s'], 'U':['*','Y','q2'],
 'qF':['-','qm','n_F'], 'C':['-','qF','alpha'], 'E':['*','X','Y'],
 'kY':['*','Y','k'], 'a':['+','E','Y'], 'g15':['*',4,'a'],
 'H':['+',3,'g15'], 'g17':['*','a','a'], 'Delta':['+','H','g17'],
 'ell':['*','E','kY'], 'g26':['+','X','K0'], 'g27':['*','C','g26'],
 'guard_base':['-','g27','n_F'], 'bt_quotient':['*','qm','n_h'],
 'guard':['-','guard_base','bt_quotient'], 'g19':['*','a','c'],
 'b0':['+','X','g19'], 'g58':['*','U','b0'], 'g59':['*','H','shift'],
 'Dstar':['+','g58','g59'], 'g61':['*','Dstar','Dstar'],
 'g62':['*','U','U'], 'c2':['*','c','c'], 'g63':['*','Delta','c2'],
 'g64':['+',1,'g63'], 'g65':['*','g62','g64'], 'A1':['-','g61','g65'],
 'F1':['+',1,'A1'], 'f2':['*','n_f','n_f'], 'rho':['-','f2',1],
 'Q':['*','Delta','rho'], 'I':['*','c2','i'], 'g71':['*','I','I'],
 'g72':['-','g71','Q'], 'Fs':['+',1,'g72'], 'y2':['*','n_y','n_y'],
 'V2':['*','V','V'], 'g81':['-','y2','V2'], 'g82':['*','Q','g81'],
 'Fa':['-','y2','g82'], 'P01':['*','F0','F1'],
 'P012':['*','P01','Fa'], 'P0123':['*','P012','Fs'],
 'P01234':['*','P0123','guard'], 'out':['-','P01234',1]}
if SHIFTED:
    shape.update({'t2':['*','n_t','n_t'],'twot':['*',2,'n_t'],
      'twot_minus_k':['-','twot','k'],'ell_times':['*','ell','twot_minus_k'],
      'F0':['+','t2','ell_times']})
else:
    shape.update({'g30':['+','ell','k'],'g38':['*','n_r','n_r'],
      'g40':['*','ell','g30'],'F0':['-','g38','g40']})
assert all(new.get(n)==row for n,row in shape.items())
known=set(c['witnesses']+c['fixed_numerals']); assert len(known)==18
for name,op,x,y in c['source']:
    assert name not in known and op in ('+','-','*')
    assert all(type(z) is int or z in known for z in (x,y))
    known.add(name)
live={'out'}
for name,op,x,y in reversed(c['source']):
    if name in live: live.update(z for z in (x,y) if isinstance(z,str))
assert all(r[0] in live for r in c['source']) and set(c['witnesses']+c['fixed_numerals'])<=live
# Exhaust all residues relevant to the three fixed sign exclusions.
for a in range(4):
    delta=(a*a+4*a+3)%4; assert delta in (0,3)
    for f in range(4):
        Q=delta*(f*f-1)%4; assert Q in (0,1)
        for y in range(4):
            for v in range(4): assert (y*y-Q*(y*y-v*v))%4 != 3
        for i in range(4): assert (1+i*i-Q)%4 != 3
        for cc in range(4):
            for u in range(4):
                for d in range(4): assert (1+d*d-u*u*(1+delta*cc*cc))%4 != 3
# Authenticate fixed raw/gzip bytes from both pinned manifest records.
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind=load(root/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
sync=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
H=lambda b:hashlib.sha256(b).hexdigest()
ports={}
for n,meta in bind['ports'].items():
    assert sync['ports'][n]['sha256_raw']==meta['sha256_raw']
    assert sync['ports'][n]['sha256_gzip']==meta['sha256_gzip']
    raw_gz=(root/meta['path']).read_bytes(); assert H(raw_gz)==meta['sha256_gzip']
    raw=gzip.decompress(raw_gz)
    assert len(raw)==meta['raw_bytes'] and H(raw)==meta['sha256_raw']
    ports[n]=int.from_bytes(raw,'little')
assert set(ports)==set(c['fixed_numerals']) and ports['beta']>0 and ports['K0']>=0
prime=1000000007
def evaluate(x):
    e={n:x for n in c['witnesses']}
    if SHIFTED: e['n_t']=2*x
    e.update({n:v%prime for n,v in ports.items()})
    for name,op,a,b in c['source']:
        a=a if type(a) is int else e[a]; b=b if type(b) is int else e[b]
        e[name]=(a+b if op=='+' else a-b if op=='-' else a*b)%prime
    return e['out']
row=[evaluate(x) for x in range(DEGREE+1)]
for _ in range(DEGREE): row=[(b-a)%prime for a,b in zip(row,row[1:])]
leader=row[0]*pow(math.factorial(DEGREE),-1,prime)%prime
assert leader==LEADER
print(json.dumps({'scope':'independent structural, residue and degree lower-bound checks; unbounded arithmetic and Lean proofs not mechanically checked',
 'inputs':14,'operations':79,'parent_operations':79+1,
 'checked_factor_rows':len(shape),'prime':prime,'degree_lower_bound':DEGREE,
 'leading_coefficient':leader,'ray_method':'finite differences',
 'port_beta_positive':True,'port_K0_nonnegative':True},sort_keys=True,indent=2))
