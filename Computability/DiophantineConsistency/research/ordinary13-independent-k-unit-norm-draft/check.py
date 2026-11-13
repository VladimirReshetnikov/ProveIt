from pathlib import Path
from hashlib import sha256
import json,sys,subprocess,itertools,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-unit-norm-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():
 assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(D/'generate.py')])==(D/'generator-receipt.json').read_bytes()
parent=Path('research/ordinary13-eta-zeta-natural-unit-norm-draft/EtaZetaNaturalUnitBridge.lean.src').read_text()
expected=(parent.replace('import EtaZetaNaturalUnitGraph','import IndependentKUnitGraph').replace('EtaZetaNaturalUnitBridgeDraft','IndependentKUnitBridgeDraft').replace('EtaZetaNaturalUnitGraphDraft','IndependentKUnitGraphDraft').replace('exact eta/zeta-natural\nprototype','exact independent-k\nchild candidate'))
assert (D/'IndependentKUnitBridge.lean.src').read_text()==expected
for theorem in ('first_ne','first_pattern','main_pattern','aux_pattern','strong_pattern',
                'output_eq','factor_units','residuals_zero','first_shape','main_shape',
                'strong_shape','aux_shape','signed_norms'):
 assert ('theorem '+theorem+' ') in expected or ('theorem '+theorem+'\n') in expected,theorem
assert '(hz : InternalZero (graph p).output v)' in expected
assert 'let k := (graph p).k.evalRing e' in expected
assert 'import DiophantineConsistency.Compact44.FreeJ13' in expected
G=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text())
assert len(G['source'])==84 and G['witnesses'][9:11]==['n_eta','n_k']
parentGraph=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
rows=[['n_k' if x=='kbase' else x for x in row] for row in parentGraph['source'] if row!=['kbase','+','n_eta','n_zeta']]
assert rows==G['source'] and parentGraph['witnesses'][10]=='n_zeta'
# Exact ordered syntax trees: these are structural checks, not ring normalization.
def plus(a,b):return ('+',a,b)
def minus(a,b):return ('-',a,b)
def times(a,b):return ('*',a,b)
def node(op,a,b):return {'+':plus,'-':minus,'*':times}[op](a,b)
d={name:('var',i) for i,name in enumerate(G['witnesses'])}; d.update({name:('port',i) for i,name in enumerate(G['fixed_numerals'])})
for n,op,l,r in G['source']:
 x=d[l] if isinstance(l,str) else l;y=d[r] if isinstance(r,str) else r;d[n]=node(op,x,y)
b,z,x,s,k=(d[n] for n in ('qm','Z','X','s','n_k'));q=plus(1,b);Y=times(times(q,times(q,q)),s);ell=times(times(x,Y),times(Y,k))
first=plus(1,minus(times(z,z),times(times(b,b),plus(1,times(ell,plus(ell,k))))))
a,c,U,dstar,f,y,v,I=(d[n] for n in ('a','c','U','Dstar','n_f','n_y','V','I'))
delta=plus(plus(3,times(4,a)),times(a,a));Q=times(delta,minus(times(f,f),1))
main=plus(1,minus(times(dstar,dstar),times(times(U,U),plus(1,times(delta,times(c,c))))))
aux=minus(times(y,y),times(Q,minus(times(y,y),times(v,v))))
strong=plus(1,minus(times(I,I),Q))
assert first==plus(1,d['A0']) and main==plus(1,d['A1']) and aux==d['Fa'] and strong==d['Fs']
assert d['out']==minus(times(times(times(plus(1,d['A0']),plus(1,d['A1'])),d['Fa']),d['Fs']),1)
for b0,z0,x0,s0,k0 in itertools.product(range(4),repeat=5):
 q0=1+b0;y0=q0**3*s0;e=x0*y0*y0*k0
 assert (1+z0*z0-b0*b0*(1+e*(e+k0)))%4!=3
rng=random.Random(20261112)
for _ in range(300):
 vals=[rng.randrange(8) for i in range(13)];p=[rng.randrange(-4,8) for i in range(4)]
 z=dict(zip(G['witnesses'],vals));z.update(zip(G['fixed_numerals'],p))
 for n,op,l,r in G['source']:
  a0=z[l] if isinstance(l,str) else l;b0=z[r] if isinstance(r,str) else r
  z[n]={'+':lambda:a0+b0,'-':lambda:a0-b0,'*':lambda:a0*b0}[op]()
 ell=z['X']*z['Y']*z['Y']*z['n_k']; delta=z['Delta']; Q=delta*(z['n_f']**2-1)
 assert z['A0']==z['Z']**2-z['qm']**2*(1+ell*(ell+z['n_k']))
 assert z['A1']==z['Dstar']**2-z['U']**2*(1+delta*z['c']**2)
 assert z['g72']==z['I']**2-Q and z['Fa']==z['n_y']**2-Q*(z['n_y']**2-z['V']**2)
print(json.dumps({'literal_generated_exact_child_rows':84,'child_slot10':'n_k','parent_to_child_rows_exact':True,'factor_pattern_ordered_trees':4,'exact_output_tree':True,'first_mod4_controls':1024,'signed_port_graph_controls':300,'lean_executed':False,'factor_extraction_elaborated':False},indent=2,sort_keys=True))
