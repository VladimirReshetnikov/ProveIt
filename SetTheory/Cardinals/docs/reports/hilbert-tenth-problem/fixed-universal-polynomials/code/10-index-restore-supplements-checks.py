"""Separate supplement stdlib-only, bounded checks. Load only after verify.py's identity gate.

Pinned source schedules are compared as JSON data, never evaluated or imported.
No assertions: every condition is checked in ordinary and optimized Python.
"""
import hashlib
import json
from math import gcd, lcm, prod

COMMIT = '2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff'
PROOF_SHA256 = 'b109e2fd1142cdad84a5b519acc5dc5055160f1d8e7617d648a561538fd956cd'

class CheckFailure(Exception):
    pass

def require(condition, message):
    if condition is not True:
        raise CheckFailure(message)

def exact(a, b):
    """Recursive JSON equality with no bool/int or int/float coercion."""
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if type(a) is list:
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise CheckFailure('Duplicate JSON key: ' + key)
        result[key] = value
    return result

def reject_constant(value):
    raise CheckFailure('Non-finite JSON constant: ' + value)

def read_json(raw):
    return json.loads(raw.decode('utf-8'), object_pairs_hook=unique_object,
                      parse_constant=reject_constant)

def canonical(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True,
                       allow_nan=False) + '\n').encode('utf-8')

def sha256(raw):
    return hashlib.sha256(raw).hexdigest()

def provenance(files):
    manifest=read_json(files['source_manifest.json'])
    require(type(manifest) is list and len(manifest)==21,'21 source receipts')
    names=set()
    for row in manifest:
        name=row['file']
        require(type(name) is str and '/' not in name and name not in names,'source basename')
        names.add(name)
        raw=files['sources/'+name]
        require(sha256(raw)==row['sha256'],'source SHA256: '+name)
        blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(blob==row['git_blob'] and len(raw)==row['bytes'],'source blob/size: '+name)
        require(row['url'].startswith('https://github.com/VladimirReshetnikov/ProveIt/blob/'+COMMIT+'/'),'source commit')
    additional=read_json(files['additional_source_manifest.json'])
    for row in additional:
        raw=files['sources/'+row['path']]
        require(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==row['sha'],
                'additional source blob')
    bindings={
      'evidence/GENERALIZED-COMPILER-SUPPLEMENT.md':'69f64c16aed4f9b962ec82553186ffc25cae79cb6808bfe0a3e6136797c0ae60',
      'evidence/GENERALIZED-SUPPLEMENT-AUDIT.md':'a47c5dcb49947e3580c0ef79a3e3bb9bc292a7d994546f4d363cbd8c13e97b26',
      'evidence/RAW-POSITIVE-REDUCTION.snapshot.md':'0ae2f56e7db3177f3100198ae503c950d2f11d30d3d6d55d51f399dbdbeb48a9',
      'evidence/INDEPENDENT-REVIEW.md':'a82ee544ea93efae25ff8b4e60c3cbe01136d5db2273b82e8eee994f222b6656',
      'evidence/MAIN-PROOF.snapshot.md':PROOF_SHA256,
      'evidence/BOOTSTRAP.snapshot.md':'581e2192aa156dd82ad3450bd8ce85444cf4bf06c0a4814a88b867f964eeb033',
      'evidence/BOOTSTRAP-REVIEW.snapshot.md':'958c27cba7ad0e0c8121dd66b4ae66e86c84fd6b0756f8316a9ada8b2053a9d5'}
    for path,expected in bindings.items():
        require(sha256(files[path])==expected,'evidence version: '+path)
    ga=files['evidence/GENERALIZED-SUPPLEMENT-AUDIT.md'].decode()
    ra=files['evidence/INDEPENDENT-REVIEW.md'].decode()
    require('**PASS.**' in ga and bindings['evidence/GENERALIZED-COMPILER-SUPPLEMENT.md'] in ga,'general audit binding')
    require('**PASS for the stated necessary-condition reduction' in ra,'raw audit verdict')
    evidence=read_json(files['evidence/provenance.json'])
    for row in evidence['files']:
        require(exact(row['byte_identical'],True),'evidence exact byte flag')
        require(sha256(files[row['packaged_path']])==row['original_sha256']==row['packaged_sha256'],'evidence original bytes')
    # Two source receipt fields now have their matching upstream .py caches.
    for stem in ['complete74_factored_first_norm','complete74_nonlinear_index_projection_scout']:
        packet=read_json(files['sources/'+stem+'.json'])
        require(packet['source_sha256']==sha256(files['sources/'+stem+'.py']),'JSON-to-source receipt')
    return {'source_files':21,'sha256_matches':21,'git_blob_matches':21,
            'additional_git_blob_matches':len(additional),'json_source_receipt_matches':2,
            'commit':COMMIT,'proof_audit_bindings':bindings,
            'source_programs_or_schedules_executed':False,'evidence_files':len(evidence['files'])}

def exponent_selection():
    records=[]
    for t in range(1,513):
        t0=t
        for prime in [2,3]:
            while t0%prime==0: t0//=prime
        require(gcd(t0,12)==1,'initial exponent CRT coprimality')
        p0=7 if t0==1 else 7+12*((-6*pow(12,-1,t0))%t0)
        period=12*t0
        if p0<=3*t: p0+=((3*t+1-p0+period-1)//period)*period
        require(p0>3*t and p0%12==7 and (p0-1)%t0==0,'exponent CRT residues')
        require(gcd(p0,2*t)==1 and p0%4==3 and p0%6==1,'exponent consequences')
        q=1<<t
        X=1<<p0
        Q=q*q-1
        require(gcd(X+1,Q)==3 and (X+1)%9==3,'binary gcd and sole factor three')
        require((4*q**3*(X+1))%3==0,'D0 integer')
        D0=4*q**3*(X+1)//3
        require(gcd(D0,Q)==1 and D0%3==(-1)**t%3,'general parity D0')
        allowed=1 if t%2==0 else 2
        require(allowed%3!=0 and (1+D0*allowed)%3==2,'local allowed residue modulo three')
        require((1<<(p0-3*t))*q**3==X,'positive X scale')
        records.append({'t':t,'t0':t0,'p0':p0,'D0_mod_3':D0%3})
    reps=[]
    for d in range(1,17):
        for x in range(1,9):
            B=1<<d
            N=1
            while B**N<=2*d*x+1: N+=1
            q=B**N
            require((q-1)%(B-1)==0,'repunit integer')
            J=(q-1)//(B-1)
            require(J>0 and q==(B-1)*J+1 and q-1-2*d*x>0,'positive repunit input context')
            for b in [1,3,101]:
                u=2*d*x+b
                require(u>=3 and u%2==1,'general positive odd input index')
            reps.append({'d':d,'x':x,'N':N})
    return {'exponent_crt_cases':len(records),'t_range':[1,512],
            'even_t_cases':256,'odd_t_cases':256,'repunit_input_cases':len(reps),
            'exact_fixture_sha256':sha256(canonical(records)),
            'repunit_fixture_sha256':sha256(canonical(reps)),
            'scope':'Initial exponent/gcd lemma only; no prime or density search'}

def raw_bounds():
    cases=0
    for q in range(16,65):
        for w in range(1,5):
            X=w*q**3
            K=q*q-1
            for C in range(1,q):
                # Clear the only rational denominator; all inequalities remain strict.
                require(C*q**3*(q*(X+K)+1)<X*q**5,'sharpened bound cleared denominator')
                require(q*K+1<q**3<=X,'K0+1/q < X/q')
                cases+=1
            for s in [1,4]:
                Y=s*q**3
                A=Y*(X+1)+2
                Delta=A*A-1
                require(A*A>2*X*q**4 and A**12>2*X*q**4,'Pell growth comparison')
                require(Delta>X*q**4,'input index discriminant upper bound')
    outer=negative=positive=0
    for q in range(16,33):
        Q=q*q-1
        for w in [1,2]:
            X=w*q**3
            K=q*q-1
            for C in [2,q//2,q-1]:
                base=(K+X)*C
                for multiplier in [0,1,2,q]:
                    F=1+(base-1)%(q-1)+(q-1)*multiplier
                    require((base-F)%(q-1)==0,'toy transport z integrality')
                    z=(base-F)//(q-1)
                    require(z>0 and base==F+z*(q-1),'toy transport equality')
                    for Z in [1,C-1]:
                        for Tp in [1,Q-1]:
                            S=Z+q*F-1
                            R=(q*q-S)*Q+Tp
                            require(0<Tp<Q and R!=0 and R<q**4,'shifted packing range')
                            require(abs(R)<X*q**4,'restoration absolute bound')
                            if R<0:
                                require(F>=q and (F!=q or Z>=2),'negative packing necessary F boundary')
                                negative+=1
                            else: positive+=1
                            outer+=1
    parity=0
    for B in [16,32,64]:
        for J in [2,4,6,8]:
            q=(B-1)*J+1
            require(q%2==1,'odd-q fixture')
            for Z,F,MC,MF in [(1,2,3,4),(3,5,7,11),(8,13,17,19)]:
                R=(q*q-Z-q*F)*(q*q-1)+(MC+q*MF)*J
                require(R%2==0,'odd-q restoration parity obstruction')
                parity+=1
    # Exact-representative argument checked on bounded abstract rank-congruence data.
    representatives=0
    for c in range(27,90):
        for p in range(13,(c-1)//2+1,2):
            for R in range(-((c-1)//2),(c-1)//2+1):
                if (R-p)%c==0 or (R+p)%c==0:
                    require(abs(2*R)<c and 2*p<c and R in [p,-p],'unique rank representative')
                    representatives+=1
    windows=0
    for q in [16,18,32]:
        for w in [1,2]:
            X=w*q**3
            for s in [1,q,2*q,3*q-1]:
                E=X*s*q**3
                for wrap in [1,2,3]:
                    p=(wrap*E+2)//3+1
                    if p%2==0:p+=1
                    n=(wrap*E-p+1)//2
                    if 2*n<p+1 or n>p-1 or p>=X*q**4:continue
                    require(2*n+p-1==wrap*E,'negative window first-index congruence')
                    require(2*p<=wrap*E<=3*p-3,'negative first-index interval')
                    require(3*p>=E+3 and s<3*q and wrap*s<3*q,'negative window consequences')
                    windows+=1
    return {'sharpened_estimate_cases':cases,'toy_outer_cases':outer,
            'negative_toy_outer_cases':negative,'positive_toy_outer_cases':positive,
            'odd_q_parity_cases':parity,'abstract_rank_representative_hits':representatives,
            'conditional_negative_window_cases':windows,
            'scope':'Necessary arithmetic implications; no full raw29/positive21 zero or compiler export'}

def input_dichotomy():
    congruences=odd_hits=even_hits=0
    for A in range(4,80,2):
        Delta=A*A-1
        previous,current=0,1
        for v in range(1,Delta):
            expected=v if v%2 else v*A
            require(current==expected%Delta,'input discriminant congruence')
            if 0<current<A-1 and current%2==1:
                u=current
                require(0<u<Delta and 0<u*A<Delta,'input representative bounds')
                require(v==(u if v%2 else u*A),'exact input dichotomy')
                if v%2:odd_hits+=1
                else:even_hits+=1
            previous,current=current,(2*A*current-previous)%Delta
            congruences+=1
    require(odd_hits==even_hits==741,'input fixture hit counts')
    return {'A_even_range':[4,78],'discriminant_congruence_cases':congruences,
            'odd_branch_hits':odd_hits,'even_branch_hits':even_hits,
            'total_dichotomy_hits':odd_hits+even_hits,
            'scope':'Both possible branches retained; neither exponent no-wrap nor R positivity follows'}

def run(files):
    require(not exact(True,1) and not exact(1,1.0) and
            not exact({'x':[False]},{'x':[0]}),'exact nested JSON type comparison')
    return {'schema':'research-report33-supplement-checks-v1','status':'PASS',
            'provenance':provenance(files),'generalized':exponent_selection(),
            'raw_positive':raw_bounds(),'input_dichotomy':input_dichotomy(),
            'semantics':{'bool_int_distinguished':True,'int_float_distinguished':True,
                         'assert_statements_used':False},
            'limitations':[
              'Finite checks corroborate arithmetic only; mathematical audits prove the stated quantified results.',
              'No Dirichlet or irrational-rotation argument is replaced by a numerical search.',
              'Raw29/positive21 negative-zero existence and restored-index positivity remain unresolved.',
              'The sign-free bootstrap/rank theorem is an imported proved lemma, not re-proved by this checker.',
              'Historical audit_results.json is preserved evidence, not a claim that its old checker was replayed.',
              'No upstream source, historical checker, or JSON schedule is executed or imported.'
            ]}
