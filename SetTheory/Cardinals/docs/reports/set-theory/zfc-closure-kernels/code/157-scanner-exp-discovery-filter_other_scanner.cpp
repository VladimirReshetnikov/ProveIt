#include <array>
#include <bitset>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
using namespace std;
struct A{int w,d,z;};array<array<A,2>,500>T,U;
struct Case{int index,pos,h;bitset<768>initial,expected;};vector<Case>cases;
int run(Case const&c,int drop){bitset<768>tape=c.initial;int q=84,h=256;for(int k=0;k<5000;k++){if(k&&((c.h==999&&q==254)||(q==84&&h==256+c.h&&tape==c.expected)))return k;if(q==254||h<0||h>=768||q==drop)return -1;A t=U[q][tape[h]];if(!t.d)return -1;tape[h]=t.w;h+=t.d;q=t.z;}return -1;}
int main(int argc,char**argv){ifstream f(argv[1]);string line;while(getline(f,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,z;char d;istringstream s(line);s>>q>>b>>w>>d>>z;T[q][b]={w,d=='R'?1:-1,z};}
ifstream cf(argv[2]);int n;cf>>n;for(int k=0;k<n;k++){Case c;int na,nb,x;cf>>c.index>>c.pos>>c.h>>na>>nb;for(int j=0;j<na;j++){cf>>x;c.initial.set(x+256);}for(int j=0;j<nb;j++){cf>>x;c.expected.set(x+256);}cases.push_back(c);}
ifstream hf(argv[3]);int nh;hf>>nh;int best=0,hits=0;for(int j=0;j<nh;j++){int id,drop,entry,q,b;A e,p;hf>>id>>drop>>entry>>e.w>>e.d>>e.z>>q>>b>>p.w>>p.d>>p.z;U=T;U[entry][0]=e;U[q][b]=p;int passed=0;for(auto const&c:cases){if(run(c,drop)<0)break;passed++;}if(passed>best){best=passed;cerr<<"best "<<id<<" drop "<<drop<<" count "<<passed<<"\n";}if(passed==(int)cases.size()){hits++;cout<<"{\"id\":"<<id<<",\"drop\":"<<drop<<",\"entry_state\":"<<entry<<",\"entry\":["<<e.w<<","<<e.d<<","<<e.z<<"],\"patch\":["<<q<<","<<b<<","<<p.w<<","<<p.d<<","<<p.z<<"],\"checked\":"<<passed<<"}"<<endl;}else cout<<"{\"id\":"<<id<<",\"checked\":"<<passed<<",\"fail\":["<<cases[passed].index<<","<<cases[passed].pos<<"]}"<<endl;}cerr<<"all "<<nh<<" hits "<<hits<<" best "<<best<<"\n";}
