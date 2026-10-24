#!/usr/bin/env python3
"""Independent ordinary/source peer of the76-predicate factorial-radius proof.

No author module, optimizer, source builder or emitter is imported. Exact
source identities are replayed by our frozen77 peer into scratch; this
review verifies that its early proof premises survive, and checks the new
unbounded residue/margin algebra and positive coefficient certificates.
"""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
AUTHOR = ROOT/'research/factorial-radius-guard'
PINS = {
    'PROOF.md':'5d9b65a4841151e200be6537373c403deea76b3943698097992176ee4c233e37',
    'README.md':'67eafdc8a8c7b95f089ddcad086548d954d448c7325a505b206b9eb000535b31',
    'SOURCE_PINS.json':'b1df3de2d214af35729f3c044c3aa0b7eedc56fbd67ecd3d7f8f991a2784d82f',
    'check.py':'96e08e4224081064778c35d770457df1d2521482f8a947586542fa872e20ca28',
    'MANIFEST.json':'0ea24533f7459155070dee3e18b67d4b8ae68500a85481778f6151cd6213557a',
}

def need(ok,message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_bytes())

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    for name,h in PINS.items():
        need(sha(AUTHOR/name) == h, 'complete frozen author file '+name)
    for name,h in load(AUTHOR/'MANIFEST.json')['files'].items():
        need(sha(AUTHOR/name) == h, 'whole declared author inventory member '+name)
    pins = load(AUTHOR/'SOURCE_PINS.json')
    for name,h in pins['files'].items():
        need(sha(ROOT/name) == h, 'whole frozen dependency '+name)
    prior = load(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    old = load(ROOT/'candidates/projected-radius-comparison-base/domain_certificate.json')
    original = {g['raw_variable'] for g in old['guards']}
    removed = {674,711,779,861,1214}
    kept = original-removed
    need(len(original) == 78 and len(kept) == 73 and 694 in kept
         and set(prior['prefix_proof']['initial_semantic_guard_indices']) <= kept,
         'all61 early sign premises and base0.T remain after both new omissions')
    need(pins['removed_original_predicates'] == sorted(removed)
         and pins['new_predicates'] == [dict(kind='at_least',raw_variable=656,lower=1),
         dict(kind='nonnegative_product',raw_variables=[674,861]),
         dict(kind='at_least',raw_variable=87,lower=2)], 'the precise76 predicates')
    # Prove the inherited ordered prefix uses no removed private guard, rather
    # than treating the later77-power interpretations as available in domain76.
    prefix = prior['prefix_proof']
    prefix_steps = list(prefix['preliminary_t_n_bounds'])+list(prefix['five_stages'])
    for step in prefix_steps:
        for term in step['row_combination']:
            need(all(v < 643 for c,m in term['multiplier'] for v in m), 'prefix multiplier uses no private value')
    peer77 = ROOT/'reviews/paired-index-guards-peer.py'
    need(sha(peer77) == 'd9c6bd3dd4b14c5400d80d8e9a4b18b76451320b0578ddbbf6cce0625b21dcc8',
         'frozen independent77 source/prefix verifier')
    helper = ROOT/'reviews/main-root-modulus-signs-peer.py'
    spec = importlib.util.spec_from_file_location('radius76_peer_sparse',helper)
    p = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(p)
    P,C,V,add,mul,product = p.P,p.C,p.V,p.plus,p.times,p.product
    A,n,m,W = [V(i) for i in range(4)]
    T = add(add(mul(C(2),mul(A,n)),mul(n,n),-1),C(-1))
    expected = {(1,1):add(n,m,-1),(-1,1):add(add(mul(C(-2),A),n),m,-1),
                (1,-1):add(add(mul(C(2),A),n,-1),m,-1),(-1,-1):mul(C(-1),add(n,m))}
    for (sx,sy),want in expected.items():
        residual = add(add(mul(C(sx),A),mul(add(A,n,-1),C(sy)),-1),m,-1)
        need(residual == want, 'all four complete small-ordinate source residuals')
    margin = add(add(T,add(mul(C(2),A),add(n,m)),-1),add(mul(C(2),A),mul(W,W),-1),-1)
    certificate = add(add(mul(mul(C(2),A),add(n,C(-2))),
        mul(add(add(W,n,-1),C(-1)),add(W,n))),add(add(W,m,-1),C(-1)))
    need(margin == certificate, 'unbounded modulus margin as explicit nonnegative terms')
    need(add(mul(C(2),add(A,W,-1)),add(add(W,n,-1),add(W,m,-1)))
         == add(mul(C(2),A),add(n,m),-1), 'strict lower bound for2A-n-m')
    # Two explicit positive-coefficient certificates after f=F+2,K=J+3.
    f,K = V(0),V(1)
    d = mul(f,mul(K,K))
    radix_gap = add(mul(add(f,C(1)),add(d,C(2))),add(K,d),-1)
    both_collapsed_gap = add(add(d,C(1)),f,-1)
    def shifted(q):
        out = {}
        for monomial,c in q.items():
            out = add(out,product([C(c)]+[add(V(v),C(2 if v == 0 else 3)) for v in monomial]))
        need(all(c > 0 for c in out.values()) and out.get((),0) > 0,
             'complete positive coefficient lower-bound certificate')
        return [[c,list(m)] for m,c in sorted(out.items())]
    radix_certificate = shifted(radix_gap)
    collapsed_certificate = shifted(both_collapsed_gap)
    need(dict((tuple(m),c) for c,m in radix_certificate)[()] == 39
         and dict((tuple(m),c) for c,m in collapsed_certificate)[()] == 17,
         'strict minimum f2/K3 cases')
    # The large-denominator h=1 obstruction has a positive polynomial margin
    # b^3-b-1=(b-3)^3+9(b-3)^2+26(b-3)+23, and b^K>=b^3.
    B = V(0)
    positive_b = add(add(add(mul(mul(B,B),B),mul(C(9),mul(B,B))),mul(C(26),B)),C(23))
    b = add(B,C(3))
    need(positive_b == add(add(mul(mul(b,b),b),b,-1),C(-1)), 'collapsed-shift denominator margin')
    diagnostic_cases = 0
    for radix in range(3,9):
        for K0 in range(3,7):
            need(radix+1 < radix**K0, 'large-denominator collapsed shift diagnostic')
            q,u = divmod(radix+1,radix)
            need(q == u == 1, 'two collapsed seeds give the unique digit C1')
            diagnostic_cases += 1
    reports = {}
    with tempfile.TemporaryDirectory(prefix='radius76-independent-peer-') as tmp:
        for optimized in (False,True):
            mode = 'optimized' if optimized else 'normal'
            for label,script in [('author',AUTHOR/'check.py'),('independent77',peer77)]:
                output = Path(tmp)/(label+'-'+mode+'.json')
                command = [sys.executable,'-B']+(['-O'] if optimized else [])
                command += [str(script),'--output',str(output)]
                proc = subprocess.run(command,capture_output=True,text=True)
                need(proc.returncode == 0, label+' scratch replay: '+proc.stderr)
                report = load(output)
                need(report['status'] == 'PASS' and report['optimized_python'] == optimized,
                     label+' replay status and mode')
                reports[label+'_'+mode] = report
    for label in ('author','independent77'):
        normal,optimized = deepcopy(reports[label+'_normal']),deepcopy(reports[label+'_optimized'])
        normal.pop('optimized_python');optimized.pop('optimized_python')
        need(normal == optimized, 'byte-equivalent semantic receipts except mode '+label)
    # The reused source verifier explicitly recollects only source identities
    # and ordered prefix/constructor signs. Its later ordinary77 power claim
    # is used for the converse from77, never for soundness from76.
    replay77 = reports['independent77_normal']
    need(replay77['independent_exact_prefix_sign_steps'] == 575
         and replay77['independent_positive_constructor_steps'] == 431
         and replay77['independent_collected_original_row_identities'] == 77,
         'complete inherited source/dependency replay')
    paths = [str((AUTHOR/name).relative_to(ROOT)) for name in PINS]
    paths += list(pins['files'])+[str(peer77.relative_to(ROOT)),str(Path(__file__).relative_to(ROOT))]
    result = dict(status='PASS',optimized_python=bool(sys.flags.optimize),source_predicates=76,
        source_pins={name:sha(ROOT/name) for name in sorted(set(paths))},
        ordinary_review='PASS: signed-ordinate dichotomy, four smallY branches, two collapsed digit contradictions, unchanged-body existence maps',
        unbounded_free_polynomial_identities=7,
        shifted_radix_gap_positive_coefficients=radix_certificate,
        shifted_both_collapsed_gap_positive_coefficients=collapsed_certificate,
        small_denominator_diagnostics=diagnostic_cases,
        author_normal_and_optimized_replays={k:v for k,v in reports.items() if k.startswith('author_')},
        independent77_source_replay=dict(status='PASS',normal_and_optimized=True,
            source_sign_steps=575,positive_constructor_steps=431,complete_source_identities=77,
            normal_receipt_sha256=sha256(json.dumps(reports['independent77_normal'],sort_keys=True).encode()).hexdigest()),
        source_builder_optimizer_or_emitter_executed=False,author_packet_modified=False,
        projected_equation_or_metrics_claimed=False,
        scope='Ordinary source-level76-predicate equivalence only. The77 factorial theorem is used in the converse from77; no full21-power theorem is used before restoring the missing bounds in76. No Lean/internal-ZFC result.')
    output = args.output or Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:result[k] for k in ('status','source_predicates','unbounded_free_polynomial_identities',
        'projected_equation_or_metrics_claimed')},indent=2))

if __name__ == '__main__':
    main()
