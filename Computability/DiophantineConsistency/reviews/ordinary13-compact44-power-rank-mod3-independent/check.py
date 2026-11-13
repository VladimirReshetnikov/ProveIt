#!/usr/bin/env python3
import gzip,hashlib,itertools,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-compact44-power-rank-mod3'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'check.py':'168f0a27d8e44b62db41e065b83e73dfad3e668b830217516e1249ae0ef15137','result.json':'22b474eb3957b9fa0db78ba4c9907a86c6f5ee4632b6c272c399af390fbe4e25'}.items():assert sha(p/n)==h
# The post-review link alone is stripped in memory; the final and
# originally reviewed README bytes are both separately pinned.
readme=(p/'README.md').read_bytes()
assert hashlib.sha256(readme).hexdigest()=='00e0bbd7e4698776e36c1322ea4b339911edc7138b9a00a26a9f58ec759510be'
tail=(b'\nIndependent external review is recorded in\n'
      b'`../../reviews/ordinary13-compact44-power-rank-mod3-independent/`.\n')
assert readme.endswith(tail)
assert hashlib.sha256(readme[:-len(tail)]).hexdigest()=='158aecc3ae48500911d43444353b26e870e73dbd104a5c5a3f6610c62932d112'
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
graph=base/'research/ordinary13-four-square88-30/candidate.json';p72=base/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';binding=p72/'ACTIVE_BINDING.json';p115=base/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json'
for q,h in [(graph,'daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'),(binding,'6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'),(p115,'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')]:assert sha(q)==h
B=json.loads(binding.read_text());C=json.loads(p115.read_text());assert set(B['ports'])==set(C['ports'])=={'beta','K0','MC','MF'};ports={};residues={}
for n,m in B['ports'].items():
 assert C['ports'][n]['sha256_raw']==m['sha256_raw'] and C['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=(p72/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(z);assert hashlib.sha256(raw).hexdigest()==m['sha256_raw'] and len(raw)==m['raw_bytes'];ports[n]=int.from_bytes(raw,'little');assert ports[n]>0 and ports[n].bit_length()==m['bits'];residues[n]=sum(raw)%3;assert residues[n]==ports[n]%3
assert ports['beta']==(1<<590069)-1 and all(residues[n]==1 for n in ('beta','MC','MF'))
g=json.loads(graph.read_text());rows={r[0]:r for r in g['source']}
for row in [['qm','*','J','beta'],['q','+',1,'qm'],['q2','*','q','q'],['qF','-','q','F'],['g44','*','qF','qm'],['G','+','alpha','g44'],['g46','-','q2',1],['g47','*','G','g46'],['g48','*','MF','q'],['g49','+','MC','g48'],['g50','*','J','g49'],['R','+','g47','g50']]:assert rows[row[0]]==row
# All possible input residues under the pinned coefficients, with no
# positivity or zero assumption. q=2^t always has nonzero residue mod 3.
nonzero_cases=0;zero_witness=None
for J,F,alpha in itertools.product(range(3),repeat=3):
 q=(1+J*residues['beta'])%3;G=(J*residues['beta']*(q-F)+alpha)%3;R=(G*(q*q-1)+J*(residues['MC']+q*residues['MF']))%3
 if q in (1,2):assert R==0;nonzero_cases+=1
 if (J,F,alpha)==(2,0,0):assert q==0 and R==2;zero_witness=(J,F,alpha)
assert nonzero_cases==18 and zero_witness==(2,0,0)
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','author_receipt_reproduced':True,'compact44_beta_bits':ports['beta'].bit_length(),'beta_MC_MF_mod3':[residues[n] for n in ('beta','MC','MF')],'nonzero_q_residue_cases_checked':nonzero_cases,'q_zero_mod3_control_rank':2,'scope':'External compact44 rank restriction when q is a power of 2; no Lean theorem or full-zero/existence claim.'},indent=2))
