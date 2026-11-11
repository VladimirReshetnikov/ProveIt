#!/usr/bin/env python3
"""84-row source and model-route ingredients only; no Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-qcube84-lean-draft';Q=D/'reviews/ordinary14-qcube84-probe-independent';T=D/'reviews/ordinary14-shifted-guard87-fact-lemmas-draft-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','902157971535736f16e02958b80c1e359b92724359926dcc0f80ad7d0c89ff8a'),(P/'make_graph.py','bf2392942c176b05676c322197dc20b897f6d81259cb0c7ab48fd120ed86938a'),(P/'P84QcubeGraph.lean','552fa737fa0c36a58220053be90c4cdb35785d1fae53bc1c30bc15f8404104e9'),(P/'observation.json','8259aaa144047ad0e94a9a7938efe8e1701c3a697dcd84f726041d602c338484'),(Q/'check.py','88f5c911e5f3840ab51d19e8c597845a068ea880ec73e8d24e214a510ec4417c'),(Q/'result.json','7f7fabbb30be535db0bc79cd3449b261ee81786d8a9333ffba497148dc4b22b9'),(T/'check.py','6a9887c635ff45cb4cd2f28c109a3235e6778206ec33edf62ba36a18afe99615'),(T/'result.json','21ba07da6d28d3f5ac28ffc7af07f6977f5dba9695678db583587b92a2808976')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent source review is recorded in\n`../../reviews/ordinary14-qcube84-lean-draft-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='cb3db0895e0eabbad38c809147b0d45d881ede0cdd0777eec9171302117a5f24'
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'make_graph.py'),'--check'],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=30);assert not r.stderr and r.stdout==(P/'observation.json').read_bytes()
for p in (Q,T):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
gp=D/'research/ordinary14-qcube84-probe/candidate.json';assert sha(gp)=='cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61';g=json.loads(gp.read_text());s=(P/'P84QcubeGraph.lean').read_text();block=s.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0];rows=[]
for line in block.splitlines():
 m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line);assert m,line
 n,a,op,b=m.groups();rows.append([n,op,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
assert rows==g['source'] and len(rows)==84
for i,n in enumerate(g['witnesses']):assert f'let {n} : Expr (Fin 14) := .var {i}' in s
for i,n in enumerate(g['fixed_numerals']):assert f'let {n} : Expr (Fin 14) := .constant (p {i})' in s
rd={r[0]:r for r in rows}
for n,row in {'X':['X','*','q','w'],'Y':['Y','*','q3','s'],'shift':['shift','-','g54','r0'],'guarded_out':['guarded_out','+','out','guard2']}.items():assert rd[n]==row
assert '⟨A0, A1, Fa, g72, guard, guarded_out⟩' in s and '(graph p).guardResidual * (graph p).guardResidual' in s and 'by rfl' in s
L=D/'Lean/DiophantineConsistency';ms=L/'ArithmeticAdaptiveMersenne2011.lean';ps=L/'ArithmeticPellPowerRecovery.lean';assert sha(ms)=='c8a132e1b28bd1cf1ed76d80e953d5568ff0c77f566ad7b2b66715c8be9641ef' and sha(ps)=='636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390'
mt=ms.read_text();pt=ps.read_text();assert 'theorem cancel_three (d R q J : V) (hd : 4≤d)' in mt and '(hdiv : q∣3*Exp.exp R) : q∣Exp.exp R' in mt
projection=pt.split('theorem projection_quotient',1)[1].split(':= by',1)[0];assert '∃ z : V' in projection and 'Exp.exp t+a*ycoord t a+(4*a+3)*z' in projection and '≤z' not in projection
print(json.dumps({'status':'PASS_SOURCE_ONLY','literal_rows':len(rows),'generator_observation_reproduced':True,'84_and_fact_review_receipts_reproduced':True,'scope':'uncompiled source; modified balance, model maps, projection lower bound, providers and endpoints remain open; no Lean'},indent=2))
