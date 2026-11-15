#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>
using namespace std;
struct Act{int w,d,n;};
int main(int argc,char**argv){
 if(argc!=3)return 2;
 ifstream f(argv[1]);map<pair<int,int>,Act> native;
 int q,b,w,n;char d;while(f>>q>>b>>w>>d>>n)native[{q,b}]={w,d=='R'?1:-1,n};
 map<int,int> ix;vector<int> qs;for(auto [k,a]:native)if(!ix.count(k.first)){ix[k.first]=qs.size();qs.push_back(k.first);}
 const int Q=qs.size(), halt=Q;ix[254]=halt;
 vector<array<Act,2>> base(Q),rows(Q);for(auto [k,a]:native)base[ix[k.first]][k.second]={a.w,a.d,ix[a.n]};
 set<int> boxes={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198};
 vector<int> sk={51,36,25,48,32,33,22,55,60};
 vector<array<int,3>> edits;for(auto [k,a]:native)if(!boxes.count(k.first)){
   auto it=find(sk.begin(),sk.end(),a.n);if(it!=sk.end())edits.push_back({ix[k.first],k.second,int(it-sk.begin())});
 }
 string path;ifstream pf(argv[2]);pf>>path;
 constexpr int ORIGIN=512,SIZE=2048;array<unsigned char,SIZE> expected{},tape{};
 expected[ORIGIN-3]=expected[ORIGIN+46]=1;for(int i=0;i<(int)path.size();i++)if(path[i]=='1')expected[ORIGIN-2+i]=1;
 int p=ORIGIN+47;vector<int>values(35,1);fill(values.begin(),values.begin()+9,0);values[6]=2;
 for(int v:values){p++;for(int i=0;i<=v;i++)expected[p++]=1;}
 vector<int> rest={0,1,2,3,4,5,7,8};long long total=0;int count=0,fail=0,best=1000000,worst=0;
 do{
   vector<int> perm(9);perm[6]=6;for(int i=0,j=0;i<9;i++)if(i!=6)perm[i]=rest[j++];
   rows=base;for(auto e:edits)rows[e[0]][e[1]].n=ix[sk[perm[e[2]]]];
   tape.fill(0);int head=ORIGIN,state=ix[74],step;
   for(step=1;step<=100000;step++){
    if(head<0||head>=SIZE||state==halt)break;
    auto a=rows[state][tape[head]];tape[head]=a.w;head+=a.d;state=a.n;
    if(state==ix[84]&&head==ORIGIN-2&&tape==expected)break;
   }
   count++;if(step>100000||state!=ix[84]||head!=ORIGIN-2||tape!=expected){fail++;continue;}
   total+=step;worst=max(worst,step);
   cout<<"HIT "<<step<<" perm";for(int x:perm)cout<<' '<<x;cout<<'\n';
   if(step<best){best=step;cout<<"BEST "<<best<<" perm";for(int x:perm)cout<<' '<<x;cout<<'\n'<<flush;}
 }while(next_permutation(rest.begin(),rest.end()));
 cout<<"SUMMARY "<<count<<" failures "<<fail<<" min "<<best<<" max "<<worst<<" total_steps "<<total<<'\n';
}
