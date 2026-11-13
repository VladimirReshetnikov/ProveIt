#!/usr/bin/env python3
"""Source-only 87-row and arbitrary-model obligation review; no Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-shifted-guard87-lean-draft';Q=D/'reviews/ordinary14-shifted-guard87-calibration-decoder-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','1e347c4996dd47ea5c4dc241a82ec5ce6129581eadc6c33c83b51e1ef06fe28c'),(P/'make_graph.py','c7e16996f42c529b78708b642778b10dd7d83d015f1c5bebb6d9aa49b69c47b2'),(P/'P87ShiftedGuardGraph.lean','d6fef15cc23f89125d7d8720b81567e05bb71fd18e83f925e307f4b428e9c279'),(P/'observation.json','8c030f4a5a259605bcdaa592591d215c9251c7bc3dfe2d55d59451829e349933'),(Q/'check.py','3e3b490dee0502f592d960a7192947674bac02d70101f1e89bc982ea4cb93163'),(Q/'result.json','d58c405d5d1e0d9dd02847419d5c01b8a1f4d0a4d3b2f8e0866dc8948c01ba1e')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent source review is recorded in\n`../../reviews/ordinary14-shifted-guard87-lean-draft-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='229ad6b70f5e42e8feafb377f026f13d67fda73ff307cb5e533448ae4944ffbe'
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'make_graph.py'),'--check'],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=30);assert not r.stderr and r.stdout==(P/'observation.json').read_bytes()
r=subprocess.run([sys.executable,'-I','-S','-B',str(Q/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(Q/'result.json').read_bytes()
gp=D/'research/ordinary14-shifted-guard87-probe/candidate.json';assert sha(gp)=='405dbed5bf465dacac2246e6e8b2c53bcb3dda9b4b13ba277f4a18cdd43ae210';g=json.loads(gp.read_text());s=(P/'P87ShiftedGuardGraph.lean').read_text();block=s.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0];rows=[]
for line in block.splitlines():
 m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line);assert m,line
 n,a,op,b=m.groups();rows.append([n,op,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
assert rows==g['source'] and len(rows)==87
for i,n in enumerate(g['witnesses']):assert f'let {n} : Expr (Fin 14) := .var {i}' in s
for i,n in enumerate(g['fixed_numerals']):assert f'let {n} : Expr (Fin 14) := .constant (p {i})' in s
assert '⟨A0, A1, Fa, g72, guard, guarded_out⟩' in s and '(graph p).guardResidual * (graph p).guardResidual' in s and 'by rfl' in s
rd={row[0]:row for row in rows}
for n,row in {'g31':['g31','-','g30','r'],'Z':['Z','+','g32','g33'],'guard_base':['guard_base','-','g27','F'],'bt_quotient':['bt_quotient','*','qm','omega'],'guard':['guard','-','guard_base','bt_quotient'],'guarded_out':['guarded_out','+','out','guard2']}.items():assert rd[n]==row
base=D/'Lean/DiophantineConsistency';src={'ArithmeticAdaptiveFactorThree2011.lean':'7679b8e5b0adb93464ca4489c1e24b288718830470764e2c4058c4cd736a64ce','Compact44/FreeJPowerProjection.lean':'fee95da196452c374b5d6aeaf2b3bb330e8d690224ad8dab523760df79da2749','Compact44/FreeJPowerFinish.lean':'e4b2e84586b6232b9accc7775f094d4e1047453f1e8337f6241d39a6657d8816'}
t={}
for n,h in src.items():assert sha(base/n)==h;t[n]=(base/n).read_text()
assert '(hY : q^3∣Y)' in t['ArithmeticAdaptiveFactorThree2011.lean'] and '(hd : q^5∣(3+4*Y*(X+1))*t) : q^4∣t' in t['ArithmeticAdaptiveFactorThree2011.lean']
for n in ('Compact44/FreeJPowerProjection.lean','Compact44/FreeJPowerFinish.lean'):assert 'freej_first_factor_transport' in t[n] and 'InternalZero (literal' in t[n]
print(json.dumps({'status':'PASS_SOURCE_ONLY','literal_rows':len(rows),'corrected_decoder_review_reproduced':True,'generator_observation_reproduced':True,'scope':'uncompiled source; signed-root, fact-level decoder, arbitrary-model bridge, provider routes and endpoints remain open; no Lean'},indent=2))
