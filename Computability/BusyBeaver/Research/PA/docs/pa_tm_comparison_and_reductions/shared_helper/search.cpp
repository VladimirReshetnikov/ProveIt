#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>
using namespace std;
struct Act {int w,d,n; bool operator==(const Act&)const=default;};
struct Pair {int a,b,bit;};
array<array<Act,2>,196> rows;
array<int,196> tag;
constexpr int HALT=196,HELP=197;
vector<Pair> pairs;
struct Patch {
  array<int,2> drop,keep,bit;int h0,h1,count;
  int pi(int q)const {for(int i=0;i<count;i++)if(q==drop[i])return keep[i];return q;}
  Act step(int q,int b)const {
    if(q==HELP)return{b,1,pi(b?h1:h0)};
    for(int i=0;i<count;i++)if(q==keep[i]&&b==bit[i])return{b,-1,HELP};
    auto a=rows[q][b];a.n=pi(a.n);return a;
  }
  int block(int q,int b)const {
    int state=pi(q),head=0;array<int,2> tape={tag[q],b};
    auto a=rows[q][b];int target=pi(a.n);
    for(int n=1;n<=64;n++){
      if(state==HALT||head< -1||head>0)return 0;
      bool deleted=false;for(int i=0;i<count;i++)deleted|=state==drop[i];
      if(deleted)return 0;
      auto c=step(state,tape[head+1]);tape[head+1]=c.w;head+=c.d;state=c.n;
      if(state==target&&head==a.d&&tape[0]==tag[q]&&tape[1]==a.w)return n;
    }
    return 0;
  }
  bool valid(array<int,8>& steps)const {
    for(int i=0;i<count;i++){
      // Test the changed read first for early rejection.
      for(int j=0;j<2;j++)for(int s=0;s<2;s++){
        int q=s?keep[i]:drop[i],b=j?1-bit[i]:bit[i];
        int n=block(q,b);if(!n)return false;steps[4*i+2*j+s]=n;
      }
    }
    return true;
  }
};
int main(int argc,char**argv){
  if(argc!=3){cerr<<"usage: search input.tm output.json\n";return 2;}
  ifstream in(argv[1]);int q,b,w,n;string d;int count=0;
  array<array<bool,2>,196> seen{};
  while(in>>q>>b>>w>>d>>n){
    if(q<0||q>=196||b<0||b>1||w<0||w>1||n<0||n>196||(d!="L"&&d!="R"))return 3;
    if(seen[q][b])return 3;seen[q][b]=true;
    rows[q][b]={w,d=="R"?1:-1,n};count++;
  }
  if(count!=392)return 4;
  tag.fill(-1);
  for(q=1;q<196;q++){
    set<int> ws;bool okay=true;int inc=0;
    for(int p=0;p<196;p++)for(b=0;b<2;b++)if(rows[p][b].n==q){inc++;ws.insert(rows[p][b].w);okay&=rows[p][b].d==1;}
    if(inc&&okay&&ws.size()==1)tag[q]=*ws.begin();
  }
  for(int a=1;a<196;a++)for(int z=1;z<196;z++)if(tag[a]==0&&tag[z]==1)
    for(b=0;b<2;b++)if(rows[a][1-b]==rows[z][1-b]&&!(rows[a][b]==rows[z][b]))pairs.push_back({a,z,b});
  cout<<"eligible pairs "<<pairs.size()<<endl;
  auto started=chrono::steady_clock::now();
  long long tested=0,one=0,groups=0;vector<Patch> survivors;
  array<int,8> steps;
  vector<int> targets;for(q=0;q<196;q++)targets.push_back(q);targets.push_back(HELP);
  // Full paired search; individual acceptance is not required, so a second
  // fold may repair an internal visit that failed in an isolated fold.
  for(int i=0;i<(int)pairs.size();i++)for(int j=i+1;j<(int)pairs.size();j++){
    auto x=pairs[i],y=pairs[j];set<int>s={x.a,x.b,y.a,y.b};if(s.size()!=4)continue;
    groups++;
    for(int flip=0;flip<4;flip++){
      Patch p;p.count=2;p.drop={flip&1?x.b:x.a,flip&2?y.b:y.a};p.keep={flip&1?x.a:x.b,flip&2?y.a:y.b};p.bit={x.bit,y.bit};
      for(int a:targets)for(int z:targets){
        p.h0=a;p.h1=z;tested++;
        if(!p.valid(steps))continue;
        survivors.push_back(p);cout<<"SURVIVOR "<<p.drop[0]<<"->"<<p.keep[0]<<" bit"<<p.bit[0]<<" "<<p.drop[1]<<"->"<<p.keep[1]<<" bit"<<p.bit[1]<<" helper "<<a<<","<<z<<endl;
      }
    }
  }
  double seconds=chrono::duration<double>(chrono::steady_clock::now()-started).count();
  ofstream out(argv[2]);
  out<<"{\n  \"working_states_reference\":196,\n  \"eligible_pairs\":"<<pairs.size()<<",\n  \"disjoint_pair_choices\":"<<groups<<",\n  \"patches_tested\":"<<tested<<",\n  \"helper_target_choices_each\":"<<targets.size()<<",\n  \"maximum_block_steps\":64,\n  \"seconds\":"<<seconds<<",\n  \"survivors\":[";
  bool first=true;
  for(auto p:survivors){if(!first)out<<",";first=false;out<<"{\"drop\":["<<p.drop[0]<<","<<p.drop[1]<<"],\"keep\":["<<p.keep[0]<<","<<p.keep[1]<<"],\"read\":["<<p.bit[0]<<","<<p.bit[1]<<"],\"helper_targets\":["<<p.h0<<","<<p.h1<<"]}";}
  out<<"]\n}\n";
  cout<<"tested "<<tested<<" survivors "<<survivors.size()<<" seconds "<<seconds<<endl;
}
