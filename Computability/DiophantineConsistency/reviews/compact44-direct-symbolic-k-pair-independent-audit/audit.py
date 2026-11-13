#!/usr/bin/env python3
"""Read-only independent audit of the paired direct symbolic-K graph client."""
import hashlib, importlib.util, json, os, re, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke with python3 -I -S -B, without optimization')
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
R=BASE/'research/ordinary12-ipra-bridge'
PKG=R/'compact44-direct-symbolic-k-pair-prototype'
PLAN=R/'compact44-direct-symbolic-k-closure-plan'
OUT=Path('/tmp/ipra-direct-symbolic-k-pair-01')
PARENT=Path('/tmp/ipra-compact-graph-derived-radix-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PARENT_AUDIT=BASE/'reviews/compact44-graph-derived-radix-independent-audit'
CLOSURE=BASE/'reviews/compact44-direct-symbolic-k-closure-independent-audit'
PRE=BASE/'reviews/compact44-selector-direct-k-prelaunch-independent-audit'
RECEIPT='3b3bc7ce75dfe06e2f0dfc58ce36d08efc73e5d9cc44ab0e6882efed1a0ab1d6'
HEAD='438e874a18e5e21189fa5160b8b6448a1304a492'
DRIVER='dc56ea8855a5a332e2481509e40f28813f17dc6f3f60056e70c09d355b2b8d2c'
PRECHECK='0671b2d30f7cdea0f468b0c5436170b7b5ccab7679149bf83c863bacb64532df'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def need(ok,msg):
    if not ok:raise ValueError(msg)
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def runcheck(path,expected,limit=1800):
    r=subprocess.run([sys.executable,'-I','-S','-B',str(path/'audit.py')],capture_output=True,timeout=limit)
    need(r.returncode==0 and not r.stderr and json.loads(r.stdout)==expected,('audit rerun',str(path),r.returncode,r.stderr[-2000:]))
    return r.returncode
def main():
    # All retained evidence is checked against its original commit.
    prefix=(PKG/'evidence').relative_to(ROOT).as_posix()+'/'
    names=subprocess.run(['git','ls-tree','-r','--name-only','83b99cc8b2','--',prefix],cwd=ROOT,check=True,capture_output=True,text=True,timeout=30).stdout.splitlines()
    need(len([n for n in names if n.endswith('.log')])==14 and len(names)==17,'retained evidence inventory')
    for name in names:
        blob=subprocess.run(['git','show','83b99cc8b2:'+name],cwd=ROOT,check=True,capture_output=True,timeout=30).stdout
        need(hashlib.sha256(blob).hexdigest()==H(ROOT/name),('committed evidence bytes',name))
    need(H(PKG/'evidence/receipt.json')==H(OUT/'receipt.json')==RECEIPT,'receipt mismatch')
    need(H(PKG/'evidence/progress.json')==H(OUT/'progress.json'),'progress mismatch')
    obs=json.loads((PKG/'evidence/terminal-observation.json').read_bytes())
    need(obs=={'session_id':67371,'observed_exit':0,'protected_head':HEAD,'receipt_sha256':RECEIPT,'lean_processes_remaining':False},'terminal observation')
    rec=json.loads((OUT/'receipt.json').read_bytes());need(rec['status']=='PASS_PAIRED_DIRECT_SYMBOLIC_K' and rec['protected_head']==HEAD and len(rec['runs'])==2,'paired receipt')
    need(H(PKG/'replay.py')==rec['driver_sha256']==DRIVER,'driver hash')
    need(H(PRE/'CHECK.json')==PRECHECK and json.loads((PRE/'CHECK.json').read_bytes())['status']=='PASS_INDEPENDENT_SELECTOR_DIRECT_K_PRELAUNCH','prelaunch review')
    for name,h in rec['fixed_pins'].items():need(Path(name).is_file() and H(name)==h,('fixed input',name))
    need(H(PARENT_AUDIT/'CHECK.json')=='2a71f758002a114db6e02b406755cb8ce5da4f4e6309ff3683aac4d681a15fdc','parent receipt pin')
    need(H(CLOSURE/'CHECK.json')=='7b9ad372987d93358ae364875f92632605444b34a43fa59c2429ce3113a84c2b','closure receipt pin')
    parent=json.loads((PARENT_AUDIT/'CHECK.json').read_bytes());closure=json.loads((CLOSURE/'CHECK.json').read_bytes())
    need(parent==rec['parent_audit'] and parent['status']=='PASS_INDEPENDENT_COMPACT44_GRAPH_DERIVED_RADIX_AUDIT','parent receipt')
    need(closure['status']=='PASS_INDEPENDENT_DIRECT_SYMBOLIC_K_CLOSURE' and len(closure['author_exploratory_reports'])==17,'closure receipt')
    need(runcheck(CLOSURE,closure,180)==0,'closure rerun')
    need(runcheck(PARENT_AUDIT,parent)==0,'parent rerun')
    scan=json.loads((PLAN/'scan.json').read_bytes());rows=scan['source_order'];need(len(rows)==7,'source count')
    expected_reports={item['name']:set(item['axioms']) for item in closure['author_exploratory_reports']}
    need(len(expected_reports)==17,'independent expected report names')
    expected_guards=set()
    for side,run in zip(('author','peer'),rec['runs']):
        need(run['side']==side and len(run['steps'])==7,('row count',side))
        lib=OUT/side/'lib';base=PARENT/side/'lib'
        orig={p.relative_to(base) for p in base.rglob('*.olean') if p.is_file()}
        actual={p.relative_to(lib) for p in lib.rglob('*.olean') if p.is_file()}
        extra={Path(*row['module'].split('.')).with_suffix('.olean') for row in rows}
        need(len(orig)==143 and not (orig&extra) and actual==orig|extra,('overlay inventory',side,len(orig),len(actual)))
        for rel in orig:
            need((lib/rel).resolve()==(base/rel).resolve() and H(lib/rel)==H(base/rel),('inherited object',side,str(rel)))
        for row,step in zip(rows,run['steps']):
            name=row['module'];src=Path(row['source']);frozen=(OUT/'frozen'/Path(*name.split('.'))).with_suffix('.lean');obj=(lib/Path(*name.split('.'))).with_suffix('.olean');log=OUT/side/(name.replace('.','_')+'.log');kept=PKG/'evidence'/side/log.name
            sourceblob=subprocess.run(['git','show',row['source_commit']+':'+src.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True,timeout=30).stdout
            need(name==step['module'] and src.is_file() and not frozen.is_symlink() and H(src)==H(frozen)==hashlib.sha256(sourceblob).hexdigest()==row['source_sha256']==step['source_sha256'],('source',side,name))
            need(obj.is_file() and not obj.is_symlink() and H(obj)==step['object_sha256'],('object',side,name))
            need(log.is_file() and not log.is_symlink() and H(log)==H(kept)==step['log_sha256'] and log.read_text()==step['stdout'],('log',side,name))
            need(type(step['compiler_exit']) is int and step['compiler_exit']==0 and type(step['deps_exit']) is int and step['deps_exit']==0 and step['stop_reason'] is None,('compiler/deps exits',side,name))
            cmd=step['command'];need(cmd==['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M3000','-j1','-DElab.async=false','--root='+str(OUT/'frozen'),str(frozen),'-o',str(obj)],('compiler command',side,name))
            imports=[line[7:] for line in src.read_text().splitlines() if line.startswith('import ')];need(imports==row['imports'],('declared imports',side,name))
            deps={str(PACKAGE/'Init.olean')}|{str((lib/Path(*imp.split('.'))).with_suffix('.olean')) for imp in imports}
            lines=step['deps_stdout'].splitlines();need(set(lines)==deps and 1<=lines.count(str(PACKAGE/'Init.olean'))<=2 and all(lines.count(x)==1 for x in deps if x!=str(PACKAGE/'Init.olean')),('direct deps',side,name))
            for path in deps|{str(obj)}:
                need(Path(path).is_file(),('required direct/output object',side,path));stem=path[:-6]
                expected_guards.update(stem+s for s in SUFFIXES)
            out=log.read_text();need(not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',out),('log diagnostics',side,name))
            reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",out,re.M)
            declared=re.findall(r'^#print axioms\s+(\S+)',src.read_text(),re.M)
            need([n for n,_ in reports]==declared and [[n,a] for n,a in reports]==step['axiom_reports'],('exact report names',side,name))
            for n,a in reports:need(n in expected_reports and {z.strip() for z in a.split(',') if z.strip()}==expected_reports[n],('axiom set',side,n))
        # Verify the actual displayed statement, not merely its report label.
        target=Path(rows[-1]['source']).read_text()
        need('def directK : ℕ := CompactSymbolicKernelOpaque.paramKernel CompactSymbolicKernel.rho' in target and 'theorem direct_graph_digits (v : Fin 12 → V) (hv : ∀ j,0<v j)' in target and 'InternalZero (literal' in target and '∃ N : V, 0<N' in target and 'v 0=rep (67*8807) N' in target and 'dig 67 C 0=1 ∧ ∀ k < 8807*N, dig 67 C k≤3' in target,'direct theorem scope')
    need(len(rec['guards'])==210 and set(rec['guards'])==expected_guards,'guard inventory')
    for name,prior in rec['guards'].items():
        p=Path(name)
        if prior is None:need(not os.path.lexists(p),('unexpected companion',name))
        else:need(p.is_file() and str(p.resolve())==prior['realpath'] and H(p)==prior['sha256'],('guard drift',name))
    strip=lambda z:{k:v for k,v in z.items() if k not in ('command','deps_stdout','sampled_peak_rss_bytes')}
    need([strip(z) for z in rec['runs'][0]['steps']]==[strip(z) for z in rec['runs'][1]['steps']],'paired output mismatch')
    progress=json.loads((OUT/'progress.json').read_bytes());need(progress=={'completed':[rec['runs'][0]],'current':rec['runs'][1]},'progress content')
    print(json.dumps({'status':'PASS_INDEPENDENT_DIRECT_SYMBOLIC_K_PAIR_AUDIT','evidence_commit':'83b99cc8b2','recorded_outer_session':67371,'recorded_outer_exit':0,'protected_head':HEAD,'receipt_sha256':RECEIPT,'compiler_steps_per_side':7,'inherited_objects_per_side':143,'direct_and_output_guard_slots':len(expected_guards),'named_axiom_reports_per_side':len(expected_reports),'closure_audit_rerun_exit':0,'parent_audit_rerun_exit':0,'lean_launched':False,'scope':'Model theorem for a distinct direct symbolic K and symbolic masks, assuming positive graph coordinates and internal graph zero. Retained-byte/displayed-coefficient binding, graph-weighted decoder, machine simulation and internal iPRA endpoint remain open. Provider/package/transitive/dynamic ancestry, sampled resources and point-in-time guard boundaries remain.'},indent=2))
if __name__=='__main__':main()
