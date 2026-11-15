// Permute physical register selectors and synthesize previous-bit reader folds.
// Broadens the source compiler's eligible set to all non-arithmetic controls
// whose incoming edges uniformly preserve one known history bit.
#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;bool operator==(const A&o)const{return w==o.w&&d==o.d&&n==o.n;}};
struct Op{int a,b;array<A,2> acts;};
long long code(A a){return((a.w*2+(a.d==1))*4096+a.n);}
int main(int argc,char**argv){if(argc<3)return 2;map<int,array<A,2>>base;vector<int>qs;ifstream fi(argv[1]);int q,b,w,n;char d;while(fi>>q>>b>>w>>d>>n){if(!base.count(q))qs.push_back(q);base[q][b]={w,d=='R'?1:-1,n};}
 int threshold=stoi(argv[2]);bool onlyshape=argc>3&&stoi(argv[3]);bool fixed=argc<5||stoi(argv[4]);
 set<int>box={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198};vector<int>sk={51,36,25,48,32,33,22,55,60};
 struct E{int q,b,r;};vector<E>edits;for(auto&[q,rs]:base)if(!box.count(q))for(int b:{0,1}){int i=find(sk.begin(),sk.end(),rs[b].n)-sk.begin();if(i<9)edits.push_back({q,b,i});}
 vector<int>perm={0,1,2,3,4,5,6,7,8};int count=0,best=0,hits=0;map<int,int>hist;auto began=chrono::steady_clock::now();
 do{
  if(fixed&&perm[6]!=6)continue;count++;auto rows=base;for(E e:edits)rows[e.q][e.b].n=sk[perm[e.r]];
  map<int,int>tags;for(auto&[q,rs]:rows)for(int b:{0,1}){A a=rs[b];if(a.w==b&&a.d==1)tags[a.n]|=1<<b;else tags[a.n]|=4;}
  vector<int>left,right;for(int q:qs)if(q!=74&&!box.count(q)&&(!onlyshape||q>=2000)){if(tags[q]==1)left.push_back(q);if(tags[q]==2)right.push_back(q);}
  array<unordered_map<long long,vector<array<int,3>>>,2>prov;
  for(int h:qs){A a=rows[h][0],b=rows[h][1];if(a.w||b.w!=1||a.d!=1||b.d!=1||!rows.count(a.n)||!rows.count(b.n))continue;
   for(int bit:{0,1}){long long key=(code(rows[a.n][bit])<<16)|code(rows[b.n][bit]);prov[bit][key].push_back({h,a.n,b.n});}
  }
  map<pair<int,int>,Op>ops;map<int,vector<int>>adj;
  for(int a:left)for(int b:right){Op op;op.a=a;op.b=b;bool good=true;
   for(int bit:{0,1}){
    if(rows[a][bit]==rows[b][bit]){op.acts[bit]=rows[a][bit];continue;}
    long long key=(code(rows[a][bit])<<16)|code(rows[b][bit]);auto it=prov[bit].find(key);bool found=false;
    if(it!=prov[bit].end())for(auto p:it->second){bool ok=true;for(int q:p)if(q==a||q==b)ok=false;if(ok){op.acts[bit]={bit,-1,p[0]};found=true;break;}}
    if(!found){good=false;break;}
   }
   if(good){ops[{a,b}]=op;adj[a].push_back(b);}
  }
  map<int,int>match;function<bool(int,set<int>&)>augment=[&](int a,set<int>&seen){for(int b:adj[a]){if(!seen.insert(b).second)continue;if(!match.count(b)||augment(match[b],seen)){match[b]=a;return true;}}return false;};
  for(int a:left){set<int>seen;augment(a,seen);}int score=match.size();hist[score]++;best=max(best,score);
  if(score>=threshold){hits++;cout<<"{\"permutation\":[";for(int i=0;i<9;i++){if(i)cout<<',';cout<<perm[i];}cout<<"],\"fold_count\":"<<score<<",\"folds\":[";bool sep=false;for(auto[b,a]:match){if(sep)cout<<',';sep=true;auto op=ops[{a,b}];cout<<'['<<a<<','<<b<<",[";for(int j=0;j<2;j++){if(j)cout<<',';A v=op.acts[j];cout<<'['<<v.w<<','<<(v.d==1?"true":"false")<<','<<v.n<<']';}cout<<"]]";}cout<<"]}"<<endl;}
  if(count%5000==0)cerr<<"PROGRESS "<<count<<" best "<<best<<" hits "<<hits<<endl;
 }while(next_permutation(perm.begin(),perm.end()));
 cerr<<"DONE layouts "<<count<<" best_folds "<<best<<" hits "<<hits<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<endl;for(auto[s,n]:hist)cerr<<"HIST "<<s<<' '<<n<<endl;
}
