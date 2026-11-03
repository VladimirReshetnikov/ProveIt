#!/usr/bin/env python3
"""Read-only independent structural, payload and receipt review; no Lean replay."""
import collections,gzip,hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2]
P=D/'research/trace75-mask-coordinate-ring-probe'; C=D/'research/trace74-mask-coordinate-probe/candidate.json'
O=D/'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(C)=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353' and sha(O)=='8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9','JSON pins')
c=json.loads(C.read_text());o=json.loads(O.read_text());src=P/'Trace74Mask.lean';s=src.read_text().split('def value74 ',1)[1].split('\ndef core ',1)[0]
names=['J','F','C','i','T','w','s','n','eta','zeta']; ports=['beta','K0','MC','MF']
need(c['witnesses']==names and c['fixed_numerals']==o['fixed_numerals']==ports,'input names')
inputs=re.findall(r'^  let (\w+) : R := ([vp]) (\d+)$',s,re.M)
need(inputs==[(n,'v',str(i)) for i,n in enumerate(names)]+[(n,'p',str(i)) for i,n in enumerate(ports)],'slots')
rows=re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',s,re.M)
def norm(x):return '4Am1' if x=='fourAm1' else int(x) if x.isdigit() else x
actual=[[norm(n),op,norm(a),norm(b)] for n,a,op,b in rows]
need(actual==c['source'] and len(actual)==c['operations']==74 and s.rstrip().endswith('N') and c['output']=='N','Lean rows/output')
need(collections.Counter(r[1] for r in actual)=={'*':44,'+':16,'-':14},'operations')
parent={r[0]:r for r in o['source']};new={r[0]:r for r in c['source']}
need(len(o['source'])==75 and [r[0] for r in c['source']]==[r[0] for r in o['source'] if r[0]!='C'],'old order')
need(parent['C']==['C','-','qmF','alpha'] and parent['G1']==['G1','*','bJ','qmF'] and parent['G']==['G','+','G1','alpha'],'old rows')
need(new['G1']==['G1','*','q','qmF'] and new['G']==['G','-','G1','C'] and all(new[n]==r for n,r in parent.items() if n not in ('C','G1','G')),'changed rows')
need([r[0] for r in o['source'] if 'alpha' in r[2:]]==['C','G'] and [r[0] for r in o['source'] if 'G1' in r[2:]]==['G'],'private uses')
need(c['coefficient_binding']==o['coefficient_binding'],'tuple metadata')
coeff=D/'candidates/ten-positive-qcube-product-square/coefficients';values={};raw_hash={}
for name,x in c['coefficient_binding']['ports'].items():
 path=coeff/x['file'];raw=gzip.decompress(path.read_bytes()); digest=hashlib.sha256(raw).hexdigest()
 need(sha(path)==x['parent_gzip_sha256'] and digest==x['raw_sha256'],'payload '+name)
 values[name]=int.from_bytes(raw,'little');need(values[name].bit_length()==x['bits'],'bits');raw_hash[name]=digest
need(raw_hash['K0']=='0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f','K0')
need(values['beta']>=31 and values['beta']%2==1 and values['K0']>0 and 0<values['MC']<values['beta']<values['MF']<2*values['beta'],'bounds')
def receipt(attempt,source,runner,module,obj,log):
 obs=P/'observations'/attempt;t=json.loads((obs/'terminal.json').read_text()); root=pathlib.Path(t['output_root'])
 need(t['exit']==0 and t['reason'] is None and sha(P/runner)==t['runner_sha256'],'exit/runner')
 need(sha(source)==sha(obs/'source.txt')==sha(root/module.replace('.','/').__add__('.lean')),'source')
 need(sha(root/(module.replace('.','/')+'.olean'))==t['object_sha256']==obj,'object')
 need(sha(obs/'stdout')==t['stdout_sha256'] and sha(obs/'stderr')==t['stderr_sha256'] and (obs/'stdout').read_text()==log and (obs/'stderr').read_text()=='','logs')
 for path,h in t['inputs'].items():need(sha(path)==h,'input '+path)
 imports=re.findall(r'^import\s+([\w.]+)\s*$',source.read_text(),re.M); selected=[]
 for imp in imports:
  rel=imp.replace('.','/')+'.olean'; first=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
  need(first and str(first) in t['inputs'] and sha(first)==t['inputs'][str(first)],'direct import '+imp)
  selected.append({'module':imp,'path':str(first),'sha256':sha(first)})
 return selected
prov=receipt('provider-attempt01',D/'Lean/DiophantineConsistency/TenPositiveTrace75.lean','run-provider.py','DiophantineConsistency.TenPositiveTrace75','1ae82441c7023e9675c5cc532d4026da6a3ee77e906996d67c315e4f693b079c','')
ring=receipt('ring-attempt02',src,'run-ring-v2.py','Trace74Mask','181b53fe5c5a52127a56ab25af95d0b7fda3d9842098850a70c8afc70659861e',"'Trace74Mask.coordinate_identity' depends on axioms: [propext, Quot.sound]\n")
need(len(prov)==2 and len(ring)==1 and ring[0]['sha256']=='1ae82441c7023e9675c5cc532d4026da6a3ee77e906996d67c315e4f693b079c','import count/provider')
print(json.dumps({'status':'PASS','rows':len(rows),'inputs':14,'raw_coefficient_sha256':raw_hash,'provider_imports':prov,'ring_imports':ring,'lean_replayed':False},indent=2,sort_keys=True))
