// General three-control replacement of two disjoint two-control history pairs.
// Finite exact-tape synthesis; exterior of the tested window remains arbitrary.
#include <bits/stdc++.h>
using namespace std;
struct A {int w,d,n;bool operator==(A const&o)const{return w==o.w&&d==o.d&&n==o.n;}};
struct P {int l,r,e;};
struct Test {int old,p,history,bit;};
int main(int argc,char**argv){
 if(argc<5){cerr<<"shared_selector_search table pairs radius bound output_dir\n";return 2;}
 int K=stoi(argv[3]),BOUND=stoi(argv[4]),N=1<<(2*K+1);string out=argc>5?argv[5]:"shared_selector_hits";
 array<A,2> old[3000],rows[3000];bool exists[3000]={};vector<int>states;
 ifstream in(argv[1]);string line;int q,b,w,n;char d;
 while(getline(in,line)){istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;if(!exists[q])states.push_back(q);exists[q]=true;old[q][b]={w,d=='R'?1:-1,n};}
 vector<P>pairs;ifstream ip(argv[2]);int np;ip>>np;for(int i=0;i<np;i++){P p;ip>>p.l>>p.r>>p.e;pairs.push_back(p);}
 long long pair_count=0,configs=0,proposals=0,combinations=0,hits=0;auto start=chrono::steady_clock::now();
 for(int i=0;i<np;i++)for(int j=i+1;j<np;j++){
  P pa=pairs[i],pb=pairs[j];set<int>four={pa.l,pa.r,pb.l,pb.r};if(four.size()!=4)continue;pair_count++;
  for(int ka:{pa.l,pa.r})for(int kb:{pb.l,pb.r}){
   int sa=ka==pa.l?pa.r:pa.l,sb=kb==pb.l?pb.r:pb.l;
   auto rho=[&](int x){if(x==pa.l||x==pa.r)return ka;if(x==pb.l||x==pb.r)return kb;return x;};
   for(int sel:{sa,sb}){int removed=sel==sa?sb:sa;
    vector<int>targets;for(int s:states)if(s!=removed)targets.push_back(s);targets.push_back(254);
    for(int ta:{0,1})for(int tb:{0,1}){configs++;
     for(int s:states)for(int z:{0,1}){A a=old[s][z];a.n=rho(a.n);rows[s][z]=a;}
     rows[ka][pa.e]={ta,-1,sel};rows[kb][pb.e]={tb,-1,sel};
     vector<Test>tests[2];
     for(P pair:{pa,pb})for(int h:{0,1})for(int p=0;p<N;p++)if(((p>>(K-1))&1)==h&&((p>>K)&1)==pair.e)tests[h].push_back({h?pair.r:pair.l,p,h,pair.e});
     array<A,2>acts;int known=0;
     auto check=[&](Test const&tc)->int{
      A oa=old[tc.old][tc.bit];int tq=rho(oa.n),th=oa.d,tt=(tc.p&~(1<<K))|(oa.w<<K);
      int q=rho(tc.old),h=0,t=tc.p;
      for(int st=0;st<=BOUND;st++){
       if(st&&q==tq&&((tq==254)||(h==th&&t==tt)))return 1;
       if(st==BOUND||h< -K||h>K||q<0||q>=3000||!exists[q]||q==removed)return 0;
       int z=(t>>(h+K))&1;A a;
       if(q==sel){if(!(known>>z&1))return 2;a=acts[z];}else a=rows[q][z];
       t=(t&~(1<<(h+K)))|(a.w<<(h+K));h+=a.d;q=a.n;
      }return 0;
     };
     vector<A>choices[2];bool possible=true;
     for(int bit:{0,1}){known=1<<bit;for(int target:targets)for(int wr:{0,1})for(int dir:{-1,1}){
       proposals++;acts[bit]={wr,dir,target};bool ok=true;
       for(auto&tc:tests[bit])if(!check(tc)){ok=false;break;}
       if(ok)choices[bit].push_back(acts[bit]);
      }
      if(choices[bit].empty()){possible=false;break;}
     }
     if(!possible)continue;
     known=3;for(A a:choices[0])for(A b:choices[1]){combinations++;acts={a,b};bool ok=true;
      for(int bit:{0,1}){for(auto&tc:tests[bit])if(check(tc)!=1){ok=false;break;}if(!ok)break;}
      if(!ok)continue;
      hits++;cout<<"{\"pair_a\":["<<pa.l<<','<<pa.r<<','<<pa.e<<"],\"pair_b\":["<<pb.l<<','<<pb.r<<','<<pb.e<<"],\"keep\":["<<ka<<','<<kb<<"],\"selector\":"<<sel<<",\"remove\":"<<removed<<",\"tags\":["<<ta<<','<<tb<<"],\"actions\":[["<<a.w<<','<<a.d<<','<<a.n<<"],["<<b.w<<','<<b.d<<','<<b.n<<"]]}"<<endl;
      filesystem::create_directories(out);ofstream f(out+"/candidate_"+to_string(hits)+".native.tm");
      rows[sel]=acts;for(int s:states)if(s!=removed)for(int z:{0,1}){A v=rows[s][z];f<<s<<' '<<z<<' '<<v.w<<' '<<(v.d==1?'R':'L')<<' '<<v.n<<'\n';}
     }
    }
   }
  }
  cerr<<"PAIR "<<i<<' '<<j<<" configs "<<configs<<" proposals "<<proposals<<" combinations "<<combinations<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
 }
 cerr<<"DONE pairs "<<pair_count<<" configurations "<<configs<<" proposals "<<proposals<<" combinations "<<combinations<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
