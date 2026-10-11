#!/usr/bin/env python3
"""Numerical diagnostics with different integral/series representations."""
import argparse,json,time
from pathlib import Path
from multishift import *
parser=argparse.ArgumentParser();parser.add_argument('--dps',type=int,default=45)
args=parser.parse_args()
if args.dps<30: raise SystemExit('Use at least 30 working digits.')
mp.mp.dps=args.dps; start=time.time(); rows=[]
tolerance=mp.mpf(10)**(-(args.dps//2-3));D=mp.mpf

def record(name,left,right,negative=False):
    err=abs(left-right)/(1+abs(left)+abs(right))
    ok=err>mp.mpf('1e-5') if negative else err<tolerance
    rows.append({'name':name,'left':str(left),'right':str(right),'normalized_residual':str(err),
                 'negative_control':negative,'passed':bool(ok)})
    print(name,'PASS' if ok else 'FAIL',mp.nstr(err,5),flush=True)
    if not ok: raise AssertionError(name)

for i,(R,ss,aa) in enumerate([
 ('1.3',['.2','-.3'],['.2','.8']),('2',['.15','.2'],['.2','.35']),
 ('1.7',['.15','.12','-.4'],['.24','.36','1.1']),
 ('1.25',['.2','.15'],['.3','.3']),('2.2',['.3','-.25'],['.7','1.2'])]):
 R=D(R);s=list(map(D,ss));a=list(map(D,aa))
 record('branch_completion_'+str(i),master(R,s,a),central(R,s,a)+cut(R,s,a))
s=[mp.mpc('.15','.1'),mp.mpc('-.1','.07')];a=[D('.27'),D('.85')]
record('complex_order_completion',master(mp.mpc('1.4','.2'),s,a),central(mp.mpc('1.4','.2'),s,a)+cut(mp.mpc('1.4','.2'),s,a))
for same_height in [False,True]:
 a=[mp.mpc('.25','.2'),mp.mpc('.35','.2' if same_height else '-.1'),mp.mpc('.9','.3')]
 R=mp.mpc('1.5','.2');orders=[mp.mpc('.12','.1'),D('.15'),D('-.1')]
 record('complex_shift_completion_'+str(same_height),master(R,orders,a),central_complex(R,orders,a)+cut_complex(R,orders,a))
 qs=[1,1,1]
 record('complex_shift_log_jet_'+str(same_height),raw_logs(R,qs,a,D('.9')),central_complex(R,[0]*3,a,qs)-cut_complex(R,[0]*3,a,qs))
for atext in ['.25','.5','.8','1.2']:
 a=D(atext)
 for q in [1,2,3,4]:
  record('stieltjes_'+atext+'_'+str(q),completed_logs(2,[q],[a]),-q*mp.stieltjes(q-1,a))
for i,(qs,aa,R) in enumerate([
 ([1,1],['.2','.35'],'1.3'),([1,1,1],['.2','.3','.4'],'2'),
 ([2,1],['.24','.8'],'1.7'),([1,2,1],['.2','.2','.75'],'2.3')]):
 a=list(map(D,aa));R=D(R);c=(1+max(D('.5'),1-min(a)))/2
 record('mixed_logs_'+str(i),completed_logs(R,qs,a),raw_logs(R,qs,a,c))
a=D('.25')
record('NEG_missing_cut',raw_logs(2,[1],[a]),mp.digamma(a),True)
record('missing_cut_exact_size',raw_logs(2,[1],[a])-mp.digamma(a),mp.pi)
raw=raw_logs(2,[3],[a]);lo=D('.5');hi=1-a
pairwise=mp.quad(lambda x:g(x)**2*3*mp.log(hi-x)**2,[lo,(lo+hi)/2,hi])
record('NEG_missing_cubic_overlap',raw-pairwise,-3*mp.stieltjes(2,a),True)
record('cubic_overlap_exact_size',raw-pairwise+3*mp.stieltjes(2,a),-mp.pi**3/mp.tan(mp.pi*a))
for R,a,N in [(D('1.4'),D('.3'),1),(D('1.4'),D('.3'),2),(D('1.4'),D('.3'),3),(D('2.2'),D('.7'),4)]:
 rhs=mp.diff(lambda p:g(p)**R,1-a,N-1)/mp.factorial(N-1)
 record('hermite_'+str(R)+'_'+str(N),master(R,[N],[a])-(-1)**N*master(R,[N],[1-a]),rhs)
a=[D('.2'),D('.45'),D('.8')];R=D('1.6')
rhs=sum(g(1-a[j])**R/mp.fprod(a[k]-a[j] for k in range(3) if k!=j) for j in range(3))
record('three_distinct_hermite',master(R,[1]*3,a)+master(R,[1]*3,[1-v for v in a]),rhs)
record('centered_half_residue',master(D('1.7'),[1],[D('.5')]),mp.pi**D('1.7')/2)
record('NEG_missing_half_residue',master(D('1.7'),[1],[D('.5')]),0,True)
a=D('.8');h=D('.15');b=a+h
cross=-2*mp.stieltjes(1,a)+sum((-h)**k*(mp.zeta(k+1,a,1)+mp.zeta(k+1,a)/k) for k in range(1,80))
record('mixed_log_stieltjes_series',completed_logs(2,[1,1],[a,b]),cross)
for q in [1,2,3]:
 lhs=realquad(lambda t:weight(2,t)*mp.log((b-D('.5')+1j*t)/(a-D('.5')+1j*t))**q)
 rhs=q*h*mp.nsum(lambda n:mp.log((n+b)/(n+a))**(q-1)/((n+a)*(n+b)),[0,mp.inf])
 record('balanced_log_ratio_'+str(q),lhs,rhs)
s=mp.mpc('.3','.2')
record('balanced_generating_function',master(2,[s,-s],[a,b]),1+s*h*mp.nsum(lambda n:(n+b)**(s-1)/(n+a)**(s+1),[0,mp.inf]))
hrhs=2*sum((-h)**k*mp.harmonic(k-1)*mp.zeta(k+1,a) for k in range(2,80))
record('harmonic_quadratic',realquad(lambda t:weight(2,t)*mp.log((b-D('.5')+1j*t)/(a-D('.5')+1j*t))**2),hrhs)
for R in [1,2]:
 for w in [1,2,3,4]:
  for q in [0,1,2]:
   record('resonance_'+str(R)+'_'+str(w)+'_'+str(q),centered_jet(R,w,q),reflected_jet(R,w,q))
def V(z):return z*(mp.log(z)-1) if z else 0
def B(a):return mp.log(mp.sin(mp.pi*a)) if a<D('.5') else 0
for a,A in [(D('.25'),D('.9')),(D('.5'),D('.75')),(D('1.3'),D('.2'))]:
 lhs=realquad(lambda t:weight(2,t)*(V(a-D('.5')+1j*t)-V(A-D('.5')+1j*t)))-B(a)+B(A)
 record('gamma_primitive_'+str(a),lhs,mp.loggamma(a)-mp.loggamma(A))
def polyodd(s,x):
 z=mp.exp(-x/2)
 return (mp.polylog(s,1j*z)-mp.polylog(s,-1j*z))/1j
for R,s in [(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]:
 def f(x):
  G=mp.gamma(D(R)/2+1j*x/(2*mp.pi))*mp.gamma(D(R)/2-1j*x/(2*mp.pi))
  return G*polyodd(s,x)
 T=D(6*args.dps+40)
 lhs=mp.quad(f,[-T,-20,-2,0,2,20,T])
 if R==1:rhs=4*mp.pi if s==0 else 4*mp.pi*s*(2-D(2)**(-s))*mp.zeta(s+1)
 else:
  beta=lambda w:D(4)**(-w)*(mp.zeta(w,D('.25'))-mp.zeta(w,D('.75'))) if w!=1 else mp.pi/4
  rhs=4*s*(s+1)*beta(s+2)+mp.pi**2*beta(s)
 record('gamma_polylog_'+str(R)+'_'+str(s),lhs,rhs)
report={'status':'PASS','working_decimal_digits':args.dps,'tolerance':str(tolerance),
 'positive_comparisons':sum(not r['negative_control'] for r in rows),
 'negative_controls':sum(r['negative_control'] for r in rows),
 'largest_positive_residual':str(max(mp.mpf(r['normalized_residual']) for r in rows if not r['negative_control'])),
 'elapsed_seconds':time.time()-start,'mpmath_version':mp.__version__,
 'arithmetic':'ordinary arbitrary-precision floating point; not rigorous intervals',
 'finite_series_terms':79,'polylog_integration_cutoff':6*args.dps+40,'records':rows}
root=Path(__file__).resolve().parents[1]
(root/f'data/numeric_{args.dps}.json').write_text(json.dumps(report,indent=2)+'\n')
print({k:v for k,v in report.items() if k!='records'})
