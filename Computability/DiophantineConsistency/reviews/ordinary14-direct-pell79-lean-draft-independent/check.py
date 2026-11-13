#!/usr/bin/env python3
"""Independent source comparison and route inventory; does not invoke Lean."""
import hashlib, json, re, subprocess, sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D = Path(__file__).resolve().parents[2]
P = D / 'research/ordinary14-direct-pell79-lean-draft'
Q = D / 'reviews/ordinary14-direct-pell79-math-independent'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
pins = {
 P/'README.md':'7a41fb86ae3cdd03dd037751deb75ee89cb054845a4a176885466b7dd44bd283',
 P/'make_graph.py':'073ab06601853542f309fe228dbcb6572411d5b5f7478bf442ab334830e19b6d',
 P/'P79DirectPell.lean':'e5b138f7ea6b5782d66fde5016726e01c9045bf5ba13858dad1d923ca9622cdb',
 P/'observation.json':'ec128b825a19717c64b560235837da75e18c4e63142b73adb32ffbc0ee7d148b',
 Q/'check.py':'1ebee8cc29957fb9f044510bbc80efc80951ec2e9430ef294fafac78b293d1fe',
 Q/'result.json':'056877679b6a9d7fcc2cc04747d80344fcb14956914a3affb0caa824fde42555',
 D/'research/ordinary14-direct-pell79/candidate.json':'5c5e2c089d0f10450374219e9d74883235fd0ef3b10d31d6df09a7dc498e2507',
 D/'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean':'ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d',
}
for p,h in pins.items(): assert sha(p)==h, p
rd=(P/'README.md').read_bytes();tail=b'\nIndependent source review is recorded in\n`../../reviews/ordinary14-direct-pell79-lean-draft-independent/`.\n'
assert rd.endswith(tail) and hashlib.sha256(rd[:-len(tail)]).hexdigest()=='a6e1409ab27d5988259a6e1e7973e1fdf8e55aed6bb93420cdc055ecca6ef44c'
def replay(script, expected, timeout):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script),'--check'] if script.name=='make_graph.py' else [sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=timeout,check=True)
 assert not r.stderr and r.stdout==expected.read_bytes()
replay(P/'make_graph.py',P/'observation.json',30)
replay(Q/'check.py',Q/'result.json',180)
g=json.loads((D/'research/ordinary14-direct-pell79/candidate.json').read_text())
s=(P/'P79DirectPell.lean').read_text()
block=s.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0]
rows=[]
for line in block.splitlines():
 m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line); assert m,line
 n,a,op,b=m.groups();rows.append([n,op,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
assert len(rows)==79 and rows==g['source']
for i,n in enumerate(g['witnesses']): assert f'let {n} : Expr (Fin 14) := .var {i}' in s
for i,n in enumerate(g['fixed_numerals']): assert f'let {n} : Expr (Fin 14) := .constant (p {i})' in s
assert g['witnesses'][8]=='r' and g['fixed_numerals']==['beta','K0','MC','MF']
assert '⟨A0, A1, Fa, g72, guard, guarded_out⟩' in s and 'by rfl' in s
r={x[0]:x for x in rows}
for n,x in {'g38':['g38','*','r','r'],'g41':['g41','+',1,'g40'],'A0':['A0','-','g38','g41'],'guarded_out':['guarded_out','+','out','guard2']}.items(): assert r[n]==x
assert sum('r' in row[2:] for row in rows)==1
ss=(D/'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean').read_text()
for name in ('def magnitude','theorem magnitude_of_add','theorem magnitude_multiply','def Equivalent'): assert name in ss
print(json.dumps({'status':'PASS_SOURCE_ONLY','literal_rows':79,'generator_observation_reproduced':True,'external_math_review_reproduced':True,'scope':'uncompiled graph; model evaluation, signed magnitude, both witness maps, provider closure and endpoints remain open; no Lean'},indent=2))
