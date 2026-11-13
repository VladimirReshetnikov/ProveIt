#!/usr/bin/env python3
"""Independently check all 84 JSON/Lean rows and the paired iPRA suffix."""
import collections,hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/thirteen84-model-binding';GRAPH=BASE/'research/thirteen-first-norm-correction92/polynomial.json';OUT=Path('/tmp/ipra-thirteen84-binding-pair-01');PARENT=Path('/tmp/ipra-thirteen-lowdegree-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');AUDIT=BASE/'reviews/thirteen-model-lowdegree-suffix-independent-audit';DEGREE=BASE/'reviews/thirteen84-degree2011-independent-audit'
RECEIPT='7c3181cdc7e7592a13f903925f26302e3d824fbbc10e829c06cb1b19566a5023';NAMES=('Thirteen84Nodes','Thirteen84Cuts','Model84DagIPRADraft');SHAS=('9ad192ad0eef32251dfcec5bff2aceb85d797dbf43ed9ebeb89d3d32c3876691','c704d072422977eac95d725efb570eb880428cfcba35c9f3b8335e3df4b04864','3396813063c7aa3d2e0534db3c69c281a7a6de6e7aeec465b589693d8a3d8b38')
REPORTS={'Thirteen84Nodes':[('Thirteen84Nodes.eval_literal',{'propext'})],'Thirteen84Cuts':[('Thirteen84Cuts.shifted_zero_equal',{'propext','Classical.choice','Quot.sound'}),('Thirteen84Cuts.literal_expression',{'propext','Quot.sound'}),('Thirteen84Cuts.scalar_eq',{'propext','Quot.sound'})],'Model84DagIPRADraft':[(f'Model84DagIPRADraft.{n}',{'propext','Classical.choice','Quot.sound'}) for n in ('sameNoZeroDag','bridgeDag','native_equivalenceDag','standard_equivalenceDag','reference_equivalenceDag','standard_translated_consistencyDag')]}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    prefix=PKG.relative_to(ROOT).as_posix()+'/';names=subprocess.run(['git','ls-tree','-r','--name-only','8bfd8dee9a','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines();need(len(names)==14,'packet inventory')
    for name in names:
        p=ROOT/name;b=subprocess.run(['git','show','8bfd8dee9a:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(b).hexdigest()==sha(p),'committed evidence '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes());need(obs['session']==11845 and obs['actual_exit_code']==0 and obs['receipt_sha256']==RECEIPT and obs['final_stdout']=='PASS_PAIRED_THIRTEEN84_DAG_IPRA '+RECEIPT and obs['child_count']==6 and obs['child_exits']==[0]*6,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt');r=json.loads((PKG/'replay-receipt.json').read_bytes());need(r['status']=='PASS_PAIRED_THIRTEEN84_DAG_IPRA' and len(r['rows'])==6 and json.loads((OUT/'progress.json').read_bytes())==r['rows'],'rows')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    need(sha(PKG/'replay.py')==r['driver_sha256'] and sha(GRAPH)=='a214fc19ea776e4e3880e13a7cd92260e76e71588c8c6b391669007a180ab3be','driver/graph')
    g=json.loads(GRAPH.read_bytes());source=(PKG/'Thirteen84Nodes.lean').read_text();variables=g['witnesses'];ports=g['fixed_numerals'];pattern=re.compile(r'^def node_([A-Za-z0-9_]+) \(p : Fin 4 → R\) \(v : Fin 13 → R\) : R := (.+?) ([+*\-]) (.+)$',re.M)
    def parse(t):
        defs=pattern.findall(t);need(len(defs)==84 and len(re.findall(r'^def node_',t,re.M))==84,'node definition count')
        def decode(s):
            if s.isdecimal():return int(s)
            m=re.fullmatch(r'\(v (\d+)\)',s)
            if m:need(int(m.group(1))<len(variables),'variable index');return variables[int(m.group(1))]
            m=re.fullmatch(r'\(p (\d+)\)',s)
            if m:need(int(m.group(1))<len(ports),'port index');return ports[int(m.group(1))]
            m=re.fullmatch(r'\(node_([A-Za-z0-9_]+) p v\)',s)
            if m:return m.group(1)
            raise ValueError('unrecognized node term '+s)
        return [[n,op,decode(a),decode(b)] for n,a,op,b in defs]
    need(parse(source)==g['source'],'ordered graph/source rows')
    need('def literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=\n  node_polynomial (fun j => Expr.constant (p j)) Expr.var' in source,'literal output mapping')
    for before,after in [('(p 0) * (v 0)','(p 1) * (v 0)'),('(node_q p v) * (node_q p v)','(node_q p v) + (node_q p v)')]:
        changed=source.replace(before,after,1);need(changed!=source and parse(changed)!=g['source'],'row mutation control')
    found=pattern.findall(source);a,b=found[0],found[1];lines=source.splitlines();i=next(i for i,x in enumerate(lines) if x.startswith('def node_'+a[0]+' '));j=next(i for i,x in enumerate(lines) if x.startswith('def node_'+b[0]+' '));lines[i],lines[j]=lines[j],lines[i];need(parse('\n'.join(lines))!=g['source'],'row order control')
    cuts=(PKG/'Thirteen84Cuts.lean').read_text();client=(PKG/'Model84DagIPRADraft.lean').read_text();need('def currentLiteral : Expr (Fin 13) := positiveShift (literal CurrentWindowCarry2011.ports)' in cuts,'current fixed-port positive shift')
    need('SameNoZero Thirteen84Cuts.currentLiteral' in client and 'positiveShift (ModelThirteenSquares.expressionAt84 CurrentWindowCarry2011.ports)' in client and '(Semiformula.lMap embedding sourceSentence)ᴺ' in client,'iPRA statement scope')
    degree=json.loads((DEGREE/'CHECK.json').read_bytes());need(sha(DEGREE/'CHECK.json')=='53af5499d9f02e21f426db70167ded0b9e4f59daac315fe5094b73c4eaeaca84' and degree['graph_sha256']==sha(GRAPH) and degree['status']=='PASS_INDEPENDENT_2011_84_DEGREE_92','fixed-port degree receipt')
    q=subprocess.run([sys.executable,'-I','-S','-B',str(DEGREE/'audit.py')],capture_output=True,timeout=60);need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==degree,'degree audit rerun')
    import os
    for key,v in r['direct_guards'].items():
        p=Path(key)
        if v is None:need(not os.path.lexists(p),'unexpected companion '+key)
        else:need(p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],'companion '+key)
    results=[]
    for si,side in enumerate(('author','peer')):
        lib=OUT/side/'lib';base=PARENT/side/'lib';pfiles={p.relative_to(base) for p in base.rglob('*.olean')};files={p.relative_to(lib) for p in lib.rglob('*.olean')};extra={Path('DiophantineConsistency')/(n+'.olean') for n in NAMES}
        need(files==pfiles|extra and not(pfiles&extra),'overlay inventory '+side)
        for rel in pfiles:need((lib/rel).is_symlink() and (lib/rel).resolve()==(base/rel).resolve() and sha(lib/rel)==sha(base/rel),'parent overlay '+str(rel))
        for ix,name in enumerate(NAMES):
            row=r['rows'][3*si+ix];src=OUT/'src/DiophantineConsistency'/(name+'.lean');obj=lib/'DiophantineConsistency'/(name+'.olean');log=OUT/side/(name+'.log')
            need(row['side']==side and row['module']==name and row['exit']==row['deps_exit']==0 and row['stop_reason'] is None,'child '+name)
            need(sha(src)==sha(PKG/(name+'.lean'))==row['source_sha256']==SHAS[ix] and obj.is_file() and not obj.is_symlink() and sha(obj)==row['object_sha256'],'source/object '+name)
            need(Path(row['log'])==log and sha(log)==sha(PKG/'logs'/side/(name+'.log'))==row['log_sha256'],'log '+name)
            cmd=row['command'];need(cmd[1:4]==['-M4000','-j1','-DElab.async=false'] and cmd[4]=='--root='+str(OUT/'src') and cmd[-3:]==[str(src),'-o',str(obj)],'command '+name)
            ds=(('ModelDifferenceRing',) if ix==0 else ('Thirteen84Nodes','ModelThirteenSquares') if ix==1 else ('Thirteen84Cuts','IPRABoundedRhoZFC'))
            deps={str(PACKAGE/'Init.olean')}|{str(lib/'DiophantineConsistency'/(d+'.olean')) for d in ds};need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'direct deps '+name)
            text=log.read_text();need(not re.search(r'warning:|error:|\bsorryAx\b|\bsorry\b',text),'warning/admission '+name)
            found=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M);want=REPORTS[name]
            need([list(x) for x in found]==row['axiom_reports'] and [n for n,_ in found]==[n for n,_ in want] and all({v.strip() for v in a.split(',') if v.strip()}==ex for (_,a),(_,ex) in zip(found,want)),'exact axiom reports '+name)
        results.append({'side':side,'rows':3,'parent_project_objects':len(pfiles),'axiom_reports':10,'warnings':0})
    for i in range(3):need(all(r['rows'][i][k]==r['rows'][i+3][k] for k in ('source_sha256','object_sha256','log_sha256')),'sibling hashes')
    parent=json.loads((AUDIT/'CHECK.json').read_bytes());need(r['parent_audit']==parent and sha(AUDIT/'CHECK.json')=='01b4f92fd866c2d34b1954527664c94df22f118dd3d5fee010bb71b7853daa83','parent receipt')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,timeout=900);need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==parent,'parent audit rerun')
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN84_DAG_IPRA_AUDIT','source_commit':'8bfd8dee9a','author_receipt_sha256':RECEIPT,'recorded_outer_session':11845,'recorded_outer_exit':0,'parent_audit_rerun_exit':p.returncode,'degree_audit_rerun_exit':q.returncode,'graph_sha256':sha(GRAPH),'exact_graph_rows':84,'row_mutation_controls':['port','operator','order'],'degree_audit_sha256':sha(DEGREE/'CHECK.json'),'direct_guard_paths':len(r['direct_guards']),'runs':results,'scope':'External exact 84-row JSON/Lean mapping, paired fixed-2011 positiveShift DAG iPRA client and independently checked fixed-tuple degree 92; no global minimality, other tuple calibration, formal PDF semantics or complete dynamic/provider ancestry.'},indent=2))
if __name__=='__main__':main()
