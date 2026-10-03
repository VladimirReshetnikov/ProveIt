#!/usr/bin/env python3
"""Independent data-only checks of the canonical-height theorem's interfaces.

Reads the two frozen packets, imports no packet code, and writes only the
explicitly requested audit receipt. These finite tests do not construct native
Pell witnesses or replace the proof in CANONICAL-HEIGHT-PROOF-AUDIT.md.
"""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import json

CANDIDATE = Path(__file__).resolve().parent.parent
BASE = CANDIDATE/'reference/base'
FOLD = CANDIDATE/'reference/folded'
PINS = {'base':'1bf1225aa950ad1d4f842c8bf098e1935925cd1d52c90453b7696c1321648f95',
        'folded':'774a4498984ebccf8216897e21bf597084e70b148557ba4fa12b597bba44ba91'}

def need(value, message):
    if not value:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def manifest(root, label, complete=False):
    manifest_sha=sha(root/'MANIFEST.json')
    need(manifest_sha==PINS[label], 'Pinned '+label+' manifest')
    obj = json.loads((root/'MANIFEST.json').read_text())
    names=list(obj['files']) if complete else [str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and p.name!='MANIFEST.json']
    for name in names:
        need(name in obj['files'], 'Listed frozen reference: '+name)
        spec=obj['files'][name];data = (root/name).read_bytes()
        need(len(data) == spec['bytes'], 'Frozen byte length: '+name)
        need(hashlib.sha256(data).hexdigest() == spec['sha256'], 'Frozen hash: '+name)
    return dict(sha256=manifest_sha, manifest_entries=len(obj['files']), authenticated_files=len(names))

def step(spec, state, N):
    if state == 'h':
        return None
    choices = []
    for src, dst, op, counter in spec['instructions']:
        if src != state:
            continue
        p = (2,3)[counter]
        if op in ('dec','positive') and N % p:
            continue
        if op == 'zero' and N % p == 0:
            continue
        new = N*p if op == 'inc' else N//p if op == 'dec' else N
        tau = 8 + (108*N+96*new if op == 'inc' else 96*N+108*new if op == 'dec' else 192*N)
        choices.append((dst,new,tau))
    need(len(choices) <= 1, 'Deterministic source')
    return choices[0] if choices else None

def execute_outer(packet, values):
    env = dict(values)
    for name, op, a, b in packet['source']:
        if name.startswith(('native__', 'clean_sos')):
            continue
        aa,bb = (env[a] if isinstance(a,str) else a), (env[b] if isinstance(b,str) else b)
        env[name] = aa+bb if op=='+' else aa-bb if op=='-' else aa*bb
    return env

def check_interfaces(packet, counts):
    native = {a for a in packet['auxiliaries'] if a.startswith('native__')}
    need(len(native) == 22, 'Exactly 22 retained native coordinates')
    is_canonical='canonical_height_slack' in packet['auxiliaries']
    need(len(packet['comparisons']) == (21 if is_canonical else 20), 'Complete comparison list')
    deps = {v:{v} for v in packet['parameters']+packet['auxiliaries']}
    for name,op,a,b in packet['source']:
        deps[name] = (deps[a] if isinstance(a,str) else set()) | (deps[b] if isinstance(b,str) else set())
    for i in ((0,1,18,19,20) if is_canonical else (0,1,18,19)):
        a,b = packet['comparisons'][i]
        used = (deps[a] if isinstance(a,str) else set()) | (deps[b] if isinstance(b,str) else set())
        need(not used & native, 'Outer row independent of native witnesses')
        counts['outer_row_native_independence'] += 1
    native_rows = packet['comparisons'][2:18]
    need(all(all(isinstance(x,str) and x.startswith('native__') for x in row) for row in native_rows), 'All 16 native rows retained')
    producers = {r[0]:r for r in packet['source']}
    external_to_native = set()
    for name,op,a,b in packet['source']:
        if name.startswith('native__'):
            external_to_native.update(x for x in (a,b) if isinstance(x,str) and not x.startswith('native__'))
    expected = {producers[x][3] for x in ('native__q','native__scaled_A','native__scaled_B','native__scaled_Z')}
    need(external_to_native == expected, 'Native core has exactly intended joined-port/scale boundary')
    counts['literal_native_interfaces'] += 1
    if is_canonical:
        need(packet['comparisons'][20]==['canonical_slack_sum','canonical_sum_plus_one'], 'Actual canonical comparison')
        need(producers['canonical_slack_sum']==['canonical_slack_sum','+','height_slack','canonical_height_slack'], 'Actual positive slack sum')
        need(producers['canonical_sum_plus_one']==['canonical_sum_plus_one','+','canonical_endpoint_clock_sum',1], 'Actual S plus one')
        need('native__' not in ''.join(str(x) for x in producers['canonical_endpoint_clock_sum']), 'Canonical S outside native block')
        counts['actual_canonical_interfaces'] += 1
    return native,producers

def check_path(packet, N0, counts, samples):
    states=[('s',N0)]; ticks=[];false_halt=False
    while states[-1][0] != 'h':
        hit=step(packet['source_machine'], *states[-1])
        if hit is None:
            counts['stuck_source_inputs'] += 1
            # Build the deliberately false one-step target with genuine unchanged
            # payload clock. Every outer constraint except transport must hold.
            states=[('s',N0),('h',N0)];ticks=[192*N0+8];false_halt=True
            break
        need(len(ticks)<8, 'Fixture has its documented short history')
        dst,N,tau=hit
        need(tau >= 132*states[-1][1]+8, 'Sharp uniform current-payload lower bound')
        states.append((dst,N));ticks.append(tau)
    mp=packet['mapping']; K,m=mp['K'],mp['modulus']
    path=[K*(N-1)+mp['codes'][q] for q,N in states]
    theta=sum(ticks);S=path[0]+path[-1]+theta;h=1 << S.bit_length()
    eta=h-S;kappa=S+1-eta
    need(eta>0 and kappa>0 and eta+kappa==S+1, 'Positive canonical cap')
    need(S<h<=2*S, 'Strict lower and weak upper boundary')
    B=131072*h*h;t=len(ticks);P=B**t;J=(P-1)//(B-1)
    qs,rs=zip(*(divmod(n-1,m) for n in path[:-1]))
    for q,(_,N) in zip(qs,states[:-1]):
        need(q==(N-1)//6 and q<N<=theta<h, 'Actual payload controls every quotient')
        counts['quotient_bound_instances'] += 1
    pack=lambda ds:sum(d*B**i for i,d in enumerate(ds))
    W=pack(qs);slopes=sorted({a for a,d in mp['table']});classes=slopes[1:]
    E=[pack([int(r==j) for r in rs]) for j in range(m)]
    Z=[pack([q if mp['table'][r][0]==a else 0 for q,r in zip(qs,rs)]) for a in classes]
    g=len(Z);beta=(B-2)*J-W-sum(Z)-g
    Ctau=pack(ticks);cq=1+(Ctau-theta)//(B-1)
    need(sum(Z)<=W<=(h-1)*J, 'Disjoint selected quotient and range bounds')
    need(beta>=(B-2*h)*J-g>0, 'Strict global slack at canonical height')
    need(Ctau>=theta and (Ctau-theta)%(B-1)==0 and cq>0, 'Positive exact clock quotient')
    need(theta<=2384*m*h*h<B-1 and theta<h, 'Strict no-wrap')
    vals=dict(x=N0-1,Tclean=packet['physical_clock_factor']*(2*theta+192*(N0+states[-1][1])+16),
              theta_positive=theta,final_positive=states[-1][1],height_slack=eta,global_slack=beta,
              quotient_hat=W+1,clock_quotient_hat=cq)
    vals.update({f'edge{i}_hat':e+1 for i,e in enumerate(E)})
    vals.update({f'product{i}_hat':z+1 for i,z in enumerate(Z)})
    is_canonical='canonical_height_slack' in packet['auxiliaries']
    if is_canonical:vals['canonical_height_slack']=kappa
    need(all(vals[a]>0 for a in packet['auxiliaries'] if not a.startswith('native__')), 'All actual supplied outer coordinates strictly positive')
    env=execute_outer(packet,vals)
    outer_indices=(0,1,18,19,20) if is_canonical else (0,1,18,19)
    for i in outer_indices:
        a,b=packet['comparisons'][i]
        need((env[a]!=env[b]) if false_halt and i==1 else (env[a]==env[b]), 'Literal complete outer equality or isolated false-halt transport failure')
    if is_canonical:
        need(env['canonical_endpoint_clock_sum']==S, 'Actual S wire is semantic endpoint-plus-native-clock sum')
    if W==0 and not false_halt:counts['zero_quotient_word_histories']+=1
    prods={r[0]:r for r in packet['source']}
    H,M,A=(env[prods[n][3]] for n in ('native__scaled_A','native__scaled_B','native__scaled_Z'))
    Q=env[prods['native__q'][3]]
    need(H&M==A, 'Complete joined AND')
    need(all(0<=n<Q for n in (H,M,A)), 'Strict port bounds')
    need(all(0<a<16*Q for a in (16*H+12,16*M+10,16*A+8)), 'Actual padded port bounds')
    need(Q>0 and Q&(Q-1)==0, 'Prescribed scale dyadic')
    # The cap excludes every larger dyadic at this fixed accepted semantic S.
    for hh in (h*2,h*4,h*8):
        need(S+1-(hh-S)<=0, 'Larger height lacks positive kappa')
        counts['larger_height_exclusions']+=1
    need(S+1-((h//2)-S)>0 and h//2<=S, 'Previous dyadic violates eta positivity')
    counts['smaller_height_domain_rejections']+=1
    if false_halt:
        counts['false_halt_transport_rejections']+=1
        return
    for wrong_U in (0, vals['Tclean']-1, vals['Tclean']+1):
        wrong=dict(vals,Tclean=wrong_U); e=execute_outer(packet,wrong)
        need(e[packet['comparisons'][19][0]]!=e[packet['comparisons'][19][1]], 'Wrong clean time rejected')
        need(all(e[packet['comparisons'][i][0]]==e[packet['comparisons'][i][1]] for i in outer_indices if i!=19), 'Wrong clean time isolates clean comparison')
        counts['wrong_clean_time_rejections']+=1
        if packet['physical_clock_factor']==4 and wrong_U%4:
            counts['nonzero_phase_time_rejections']+=1
    if is_canonical:
        # Repack this genuine history at twice its canonical height. All old
        # outer rows and the full joined AND survive, but no positive kappa
        # can solve the actual new cap. Test the minimal positive kappa=1.
        hh=2*h;bb=131072*hh*hh;pp=bb**t;jj=(pp-1)//(bb-1)
        word=lambda ds:sum(d*bb**i for i,d in enumerate(ds))
        ww=word(qs);ee=[word([int(r==j) for r in rs]) for j in range(m)]
        zz=[word([q if mp['table'][r][0]==a else 0 for q,r in zip(qs,rs)]) for a in classes]
        larger=dict(vals,height_slack=hh-S,canonical_height_slack=1,quotient_hat=ww+1,
                    global_slack=(bb-2)*jj-ww-sum(zz)-g,clock_quotient_hat=1+(word(ticks)-theta)//(bb-1))
        larger.update({f'edge{i}_hat':v+1 for i,v in enumerate(ee)})
        larger.update({f'product{i}_hat':v+1 for i,v in enumerate(zz)})
        e=execute_outer(packet,larger)
        need(all(larger[a]>0 for a in packet['auxiliaries'] if not a.startswith('native__')), 'Larger-height candidate outer coordinates positive')
        need(all(e[packet['comparisons'][i][0]]==e[packet['comparisons'][i][1]] for i in (0,1,18,19)), 'Repacked larger height satisfies every old outer row')
        need(e['canonical_slack_sum']>e['canonical_sum_plus_one'], 'Minimal positive kappa already exceeds cap at larger dyadic')
        hhport,mmport,aaport=(e[prods[n][3]] for n in ('native__scaled_A','native__scaled_B','native__scaled_Z'))
        need(hhport&mmport==aaport, 'Larger-height joined AND remains genuine')
        counts['actual_larger_height_cap_rejections']+=1
        for delta in (-1,1):
            wrong=dict(vals,canonical_height_slack=kappa+delta); e=execute_outer(packet,wrong)
            need(e['canonical_slack_sum']!=e['canonical_sum_plus_one'], 'Changed kappa rejected by cap')
            counts['kappa_mutation_rejections']+=1
        counts['actual_canonical_full_outer_histories']+=1
    counts['canonical_full_outer_histories']+=1
    if N0 in (1,3,5):
        samples.append(dict(fixture=packet['fixture'],model=packet['model'],N0=N0,S=S,h=h,eta=eta,kappa=kappa,
                            theta=theta,steps=t,beta_positive=beta>0,native_witnesses_materialized=False))

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path);parser.add_argument('--expect',type=Path)
    parser.add_argument('--check-live-base',type=Path);parser.add_argument('--check-live-folded',type=Path);args=parser.parse_args()
    live_paths={label:path for label,path in [('base',args.check_live_base),('folded',args.check_live_folded)] if path is not None}
    live_before={label:manifest(path,label,complete=True) for label,path in live_paths.items()}
    before={label:manifest(path,label) for label,path in [('base',BASE),('folded',FOLD)]};counts=Counter();samples=[];interfaces=[]
    # Test the exact scalar boundary independently of whether these short
    # fixtures happen to produce power-of-two S values.
    for S in range(1,32769):
        h=1 << S.bit_length();eta=h-S;kappa=2*S+1-h
        candidates=[1<<k for k in range(S.bit_length()+2) if S<(1<<k)<=2*S]
        need(candidates==[h] and eta>=1 and kappa>=1, 'Unique strict-next dyadic')
        if S&(S-1)==0:
            need(h==2*S and eta==S and kappa==1, 'Power-of-two S boundary')
            counts['exact_power_of_two_boundaries']+=1
        counts['scalar_height_lemma_cases']+=1
    for K in (1,2,5,7,11):
        for N in range(1,257):
            for qstate in range(1,K+1):
                need((K*(N-1)+qstate-1)//(6*K)==(N-1)//6, 'Control-independent residue quotient identity')
                counts['residue_quotient_identity_cases']+=1
    for p in (2,3):
        for N in range(1,257):
            for op in ('inc','dec','nop','positive','zero'):
                if op in ('dec','positive') and N%p:continue
                if op=='zero' and N%p==0:continue
                new=N*p if op=='inc' else N//p if op=='dec' else N
                tau=8+(108*N+96*new if op=='inc' else 96*N+108*new if op=='dec' else 192*N)
                need(tau>=132*N+8, 'Primitive lower bound')
                counts['primitive_tick_lower_bound_cases']+=1
    candidate_files=sorted((CANDIDATE/'circuits').glob('*-canonical.json'))
    need(len(candidate_files)==8, 'Eight actual emitted canonical circuits')
    for file in sorted((FOLD/'circuits').glob('*.json'))+candidate_files:
        packet=json.loads(file.read_text());native,prods=check_interfaces(packet,counts)
        interfaces.append(dict(file=str(file.relative_to(CANDIDATE)),sha256=sha(file),native_auxiliaries=sorted(native),native_comparisons=len(packet['comparisons'][2:18])))
        if file in candidate_files:
            parent=json.loads((FOLD/'circuits'/file.name.replace('-canonical.json','-folded.json')).read_text())
            need([r for r in packet['source'] if r[0].startswith('native__')]==[r for r in parent['source'] if r[0].startswith('native__')], 'Native source literally preserved')
            need(packet['comparisons'][:20]==parent['comparisons'], 'All old comparison operands literally preserved')
            need(packet['auxiliaries']==parent['auxiliaries']+['canonical_height_slack'], 'Only one positive auxiliary added')
            need(packet['parameters']==parent['parameters'], 'Natural input ports preserved')
            counts['actual_native_blocks_identical']+=1
        for N in range(1,257):check_path(packet,N,counts,samples)
    for file in sorted((BASE/'circuits').glob('zero-step*.json')):
        packet=json.loads(file.read_text())
        need(packet['auxiliaries']==[], 'Separate zero-step remains witness-free')
        for x in range(65):
            U=packet['physical_clock_factor']*(384*x+400)
            for delta in (-1,0,1):
                e=dict(x=x,Tclean=U+delta)
                for name,op,a,b in packet['source']:
                    aa=e[a] if isinstance(a,str) else a;bb=e[b] if isinstance(b,str) else b
                    e[name]=aa+bb if op=='+' else aa-bb if op=='-' else aa*bb
                need(e[packet['output']]==delta*delta, 'Separate zero-step exact polynomial')
                counts['zero_step_exact_evaluations']+=1
    after={label:manifest(path,label) for label,path in [('base',BASE),('folded',FOLD)]};need(before==after,'Frozen reference inputs unchanged')
    live_after={label:manifest(path,label,complete=True) for label,path in live_paths.items()}
    need(live_before==live_after, 'Live frozen inputs unchanged')
    result=dict(status='PASS',scope='Canonical-height proof lemmas, literal inherited native block preservation, and actual canonical outer semantics; not full candidate ledger/degree/SOS audit and no native Pell witness materialization',
                checker_sha256=sha(Path(__file__)),frozen_reference_manifests=before,counts=dict(sorted(counts.items())),interfaces=interfaces,samples=samples)
    if args.expect:need(result==json.loads(args.expect.read_text()),'Reproducible receipt')
    if args.output:args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',counts=result['counts']),sort_keys=True))
if __name__=='__main__':main()
