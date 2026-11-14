// Local quotient synthesis with a two-cell displacement of the removed state.
// Discovery only: every survivor requires full source and blank-start checks.
#include <bits/stdc++.h>
using namespace std;
struct A {int w,d,n;};
struct Test {int old,p;};
int main(int argc,char**argv){
 if(argc<5){cerr<<"table patterns radius bound [offset] [start]\n";return 2;}
 int K=stoi(argv[3]),BOUND=stoi(argv[4]),delta=argc>5?stoi(argv[5]):-2,start=argc>6?stoi(argv[6]):74;
 int N=1<<(2*K+1),MASK=N-1;
 map<int,array<A,2>> rows;vector<int>states;
 ifstream in(argv[1]);string line;int q,b,w,n;char dr;
 while(getline(in,line)){istringstream s(line);if(!(s>>q>>b>>w>>dr>>n))continue;if(!rows.count(q))states.push_back(q);rows[q][b]={w,dr=='R'?1:-1,n};}
 set<int> box={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198};
 map<int,set<int>> pats;ifstream pi(argv[2]);int p;while(pi>>q>>p)pats[q].insert(p);
 // Exact finite startup prefix, including every row used before the source seed.
 set<long> ones;long h=0;int sq=start;long startup_steps=0;
 for(;startup_steps<100000;startup_steps++){
  int pat=0;for(int z=-K;z<=K;z++)if(ones.count(h+z))pat|=1<<(z+K);pats[sq].insert(pat);
  if(!rows.count(sq))break;
  A a=rows[sq][ones.count(h)?1:0];if(a.w)ones.insert(h);else ones.erase(h);h+=a.d;sq=a.n;
 }
 // Box states are excluded from merging. No guessed context omission allowed.
 for(int q:states)if(!pats.count(q))for(int p=0;p<N;p++)pats[q].insert(p);
 long long pairs=0,trials=0,combos=0,hits=0;auto began=chrono::steady_clock::now();
 for(int remove:states){if(box.count(remove)||remove==84)continue;
  for(int keep:states){if(keep==remove||box.count(keep)||keep==84)continue;if(delta==0&&remove>keep)continue;
   bool admissible=true;
   for(auto&[q,rs]:rows)if(q!=remove&&q!=keep)for(auto a:rs)if(a.n==remove){if(abs(a.d+delta)!=1||(delta&&box.count(q)))admissible=false;}
   if(!admissible)continue;pairs++;
   vector<Test>tests[2];
   for(int q:{remove,keep})for(int p:pats[q]){int sh=q==remove?delta:0;tests[p>>(K+sh)&1].push_back({q,p});}
   for(int bit:{0,1})sort(tests[bit].begin(),tests[bit].end(),[](auto x,auto y){return x.p<y.p || (x.p==y.p&&x.old<y.old);});
   array<A,2> acts;int known;
   auto check=[&](Test tc)->int{
    int ob=tc.p>>K&1;A old=rows[tc.old][ob];
    bool halt=!rows.count(old.n);
    int tq=old.n==remove?keep:old.n,th=old.d+(old.n==remove?delta:0),tt=(tc.p&~(1<<K))|(old.w<<K);
    int q=keep,h=tc.old==remove?delta:0,t=tc.p;
    for(int st=0;st<=BOUND;st++){
     if(st&&((halt&&!rows.count(q))||(!halt&&q==tq&&h==th&&t==tt)))return 1;
     if(st==BOUND||h<-K||h>K||!rows.count(q))return 0;
     int bit=t>>(h+K)&1;A op;
     if(q==keep){if(!(known>>bit&1))return 2;op=acts[bit];}
     else{op=rows[q][bit];if(op.n==remove){op.d+=delta;op.n=keep;}}
     if(abs(op.d)!=1)return 0;
     t=(t&~(1<<(h+K)))|(op.w<<(h+K));h+=op.d;q=op.n;
    }return 0;
   };
   vector<A>choices[2];bool possible=true;vector<int>targets=states;targets.push_back(254);
   for(int bit:{0,1}){
    known=1<<bit;
    for(int target:targets){if(target==remove)continue;for(int wr:{0,1})for(int dir:{-1,1}){trials++;acts[bit]={wr,dir,target};bool ok=true;
     for(auto tc:tests[bit])if(!check(tc)){ok=false;break;}if(ok)choices[bit].push_back(acts[bit]);
    }}
    if(choices[bit].empty()){possible=false;break;}
   }
   if(!possible)continue;
   known=3;for(A z:choices[0])for(A o:choices[1]){combos++;acts={z,o};bool ok=true;
    for(int bit:{0,1}){for(auto tc:tests[bit])if(check(tc)!=1){ok=false;break;}if(!ok)break;}
    if(ok){hits++;cout<<"{\"remove\":"<<remove<<",\"keep\":"<<keep<<",\"offset\":"<<delta<<",\"actions\":[["<<z.w<<','<<z.d<<','<<z.n<<"],["<<o.w<<','<<o.d<<','<<o.n<<"]]}"<<endl;}
   }
  }
 }
 cerr<<"DONE offset "<<delta<<" pairs "<<pairs<<" trials "<<trials<<" combos "<<combos<<" hits "<<hits<<" startup "<<startup_steps<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<endl;
}
