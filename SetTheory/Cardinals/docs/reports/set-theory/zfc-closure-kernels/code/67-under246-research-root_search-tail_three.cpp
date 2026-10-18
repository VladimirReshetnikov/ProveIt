#include <array>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <string>
#include <algorithm>
struct A { int w,d,q; };
using T=std::array<std::array<A,2>,256>;
struct Case {int q,target;std::array<unsigned char,200> tape{};std::vector<int> want;bool inc;};
std::vector<int> block(std::vector<int> v) {std::vector<int>b;for(int n:v){b.push_back(0);for(int i=0;i<=n;i++)b.push_back(1);}return b;}
Case make(std::vector<int>v,int r,bool inc){
 Case c;c.inc=inc;c.q=inc?73:95;c.target=inc?48:112;
 if(!inc)v[r]=0;
 auto b=block(v);int p=0;for(int i=0;i<r;i++)p+=v[i]+2;b[p+1]=0;
 for(int i=0;i<(int)b.size();i++)c.tape[20+i]=b[i];
 for(int d:{2,4,7,8})c.tape[20-d]=1;
 if(inc)v[r]++;c.want=block(v);return c;
}
bool run(const T&tab,const Case&c){
 auto tape=c.tape;int h=20,q=c.q;
 for(int t=0;t<500;t++){
  if(t&&q==c.target&&h==19){
   for(int i=0;i<20;i++)if(tape[i]!=c.tape[i])return false;
   int p=20;for(int b:c.want)if(tape[p++]!=b)return false;
   if(c.inc)while(p<198){
    bool any=false;for(int i=p;i<200;i++)if(tape[i]){any=true;break;}
    if(!any)return true;
    if(tape[p]||!tape[p+1])return false;
    p++;while(p<200&&tape[p])p++;
   }
   for(;p<200;p++)if(tape[p])return false;
   return true;
  }
  if(h<20||h>170||q==254||q==255)return false;
  auto a=tab[q][tape[h]];tape[h]=a.w;h+=a.d;q=a.q;
 }
 return false;
}
int main(int argc,char**argv){
 T tab;std::vector<int>states;std::ifstream in(argv[1]);std::string l;
 while(std::getline(in,l)){if(l.empty()||l[0]=='#')continue;std::istringstream s(l);int q,b,w,t;char d;s>>q>>b>>w>>d>>t;tab[q][b]={w,d=='R'?1:-1,t};if(b==0&&q!=255)states.push_back(q);}
 std::vector<Case>cs;for(auto v:std::vector<std::vector<int>>{{0,0},{1,0},{0,1},{1,0,2},{2,3,0,0},{0,0,1,0},{4,3,2,0},{0,2,0,3}}){for(int r=0;r<(int)v.size()-1;r++)for(bool inc:{false,true})cs.push_back(make(v,r,inc));}
 long long n=0,n1=0,n2=0;int found=0;
 std::vector<int>targets{2,4,6,7,20,42,48,63,73,75,83,95,109,112,131};
 for(int qa:targets)for(int da:{-1,1})for(int wa:{0,1}){
 tab[109][0]={wa,da,qa};
 for(int q:targets)for(int d:{-1,1})for(int w:{0,1}){
  tab[75][0]={w,d,q};
  for(int q2:targets)for(int d2:{-1,1})for(int w2:{0,1}){
   tab[131][0]={w2,d2,q2};n++;
   if(!run(tab,cs[0]))continue;n1++;
   if(!run(tab,cs[1]))continue;n2++;
   bool ok=true;for(auto c:cs)if(!run(tab,c)){ok=false;break;}
   if(ok){std::cout<<"FOUND 109/0="<<wa<<","<<da<<","<<qa<<" 75/0="<<w<<","<<d<<","<<q<<" 131/0="<<w2<<","<<d2<<","<<q2<<std::endl;found++;}
  }
 }
 }
 std::cout<<"DONE candidates="<<n<<" first="<<n1<<" second="<<n2<<" found="<<found<<std::endl;
}
