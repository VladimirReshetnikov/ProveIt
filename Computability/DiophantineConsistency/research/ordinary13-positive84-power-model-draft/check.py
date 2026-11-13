from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
PINS={'research/ordinary13-qcube-unscale84/candidate.json': '2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77', 'research/ordinary13-positive84-division-model-draft/Positive84Division.lean.src': '20840eedc6993eaea993d7dc6cdec7b1b3643a0331d51c64f4ea2febadb530ac', 'research/ordinary13-residue-signfree-power-model-draft/ResidueSignFreePower.lean.src': '1c6935eda3ce9ae05d257957d7e2d8f5f3786386aaf618d5a480036113c8bb92', 'research/ordinary13-residue-qbalance-graph-draft/ResidueQBalance.lean.src': 'a1369553c520dc5db2839f36fb9181f5434bad0f196bbb04399ef4c3b2f7e344', 'research/ordinary13-residue-three-projection-model-draft/ResidueThreeProjection.lean.src': 'd4c30dc20ef93cbcad180d4ba350d77d0c0534e8ef485254509a9c1604026cf2', 'research/ordinary13-residue-compact-qbound-model-draft/ResidueCompactQBound.lean.src': '79fb9cc240fa5f24c4a89bbce7c10773e2986c53b677320514009fe964bf622c', 'research/ordinary13-eta-zero-growth-model-draft/EtaZeroGrowth.lean.src': '8f7f61c667d87c2e302e92a893dab01839cb5c5f5a8c1be26b08bf3a74360ab2', 'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean': '636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390', 'Lean/DiophantineConsistency/Compact44/FreeJPowerFinish.lean': 'e4b2e84586b6232b9accc7775f094d4e1047453f1e8337f6241d39a6657d8816', 'research/ordinary13-positive84-power-model-draft/Positive84OrientedPower.lean.src': '49ae009647c5db4aef715b8b2cb266ea99892f3cce070eb49d1c4fa3a630b37f', 'research/ordinary13-positive84-power-model-draft/Positive84Power.lean.src': '565b28f2fcecbbc0b0f53d827a3dffc7fe8cd1f5090a8a80375e03242cf60a23'}
for p,h in PINS.items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
f=list(PINS);g=json.loads(Path(f[0]).read_text());r={x[0]:x for x in g['source']}
assert len(g['source'])==84 and g['witnesses'][6:8]==['X','s']
for row in [['q','+',1,'qm'],['q3','*','q','q2'],['Y','*','q3','s'],['U','*','Y','q2'],['E','*','X','Y'],['g55','*','E','q'],['g56','+','g54','g55'],['shift','-','g56','r0'],['g44','*','qF','qm'],['G','+','alpha','g44'],['g47','*','G','g46'],['g50','*','J','g49'],['R','+','g47','g50']]:assert r[row[0]]==row
s=[Path(x).read_text() for x in f]
assert 'theorem q_balance' in s[3] and 'theorem power_bound' in s[7]
assert 'theorem power_of_oriented_balance' in s[2] and 'theorem power_of_oriented_balance' in s[9]
body=s[2].split('theorem power_of_oriented_balance ',1)[1].split('\nend DiophantineConsistency.ResidueSignFreePowerDraft',1)[0]
copy=s[9].split('theorem power_of_oriented_balance ',1)[1].split('\nend DiophantineConsistency.Positive84OrientedPowerDraft',1)[0]
assert body==copy
assert all(x in s[10] for x in ['def ExactPowerFacts','R=rank84 p v','2*n=R+1','xcoord R','ycoord R','v 6*Y84 p v*q84 p v','theorem powerGraphCut','theorem divCut'])
assert 'omega' not in s[10].replace('an omega call','an ignored call')
for q in range(46,100):
 for X in range(1,90):
  if 3*X%q==0:assert X>=16
count=0
for q in range(1,7):
 for X in range(1,5):
  for ss in range(1,4):
   for w in range(4):
    for main in range(4):
     Y=q**3*ss;U=Y*q*q;W=4*X*q*ss*w; a=X*Y+Y; H=3+4*a
     R=7;gamma=2;c=3;k=R+1+4*X*Y*Y*w
     assert 4*X*Y*Y*w==U*W
     root=U*main+H*k-U*(X+a*c)-H*(U*gamma+X*Y*q+R+1)
     qbal=q*(main+H*W)-q*(X+a*c+H*gamma)-H*X
     assert root==q*Y*qbal;count+=1
print(json.dumps({'sha256':PINS,'graph_extra_term_and_rank_rows_checked':True,'copied_oriented_power_body_identical':True,'q_balance_integer_controls':count,'lean_executed':False,'status':'Unelaborated fact client; exact 84 graph witness extraction and provider validation remain open.'},sort_keys=True,indent=2))
