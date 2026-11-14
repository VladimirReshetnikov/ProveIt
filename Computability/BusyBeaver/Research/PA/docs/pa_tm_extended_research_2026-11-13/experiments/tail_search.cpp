#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <random>
using namespace std;
struct A{int w,d,n;};
array<array<A,2>,196> base, rows;
struct Test{vector<int> tape,want;int start,finish,pos,r,kind;};
vector<Test> tests;
int labels[197];
int ix(int native){return int(find(labels,labels+197,native)-labels);}
int aliasq(int q,int a,int b){return q==a?b:q;}
bool run(const Test &t,int a,int b){
 const int off=80,sz=4096;array<unsigned char,sz> tape{};
 // An arbitrary left tag, separated from the file by twenty zeros.
 tape[off-23]=1;tape[off-21]=1;
 for(int i=0;i<int(t.tape.size());i++)tape[off+i]=t.tape[i];
 int q=aliasq(t.start,a,b),p=off,finish=aliasq(t.finish,a,b);
 for(int k=0;k<8000;k++){
   if(k && q==finish && p==off+t.pos){
      if(tape[off-23]!=1 || tape[off-21]!=1)return false;
      for(int j=off-20;j<off;j++)if(tape[j])return false;
      if(t.pos==0 && tape[off]!=1)return false;
      int j=off+(t.pos==0?1:0);
      // The returned head for positive decrement is at the old file start,
      // while the new file starts one cell farther to the right.
      for(int reg=0;reg<int(t.want.size());reg++){
        int want=t.want[reg];
        if(tape[j++])return false;
        if(t.kind==3 && reg==t.r){if(tape[j++])return false;want--;}
        int count=0;while(j<sz && tape[j]){count++;j++;}
        if(count!=want+1)return false;
      }
      // Require at least one well-formed spare register; its value can vary.
      if(tape[j++] || !tape[j])return false;
      return true;
   }
   if(q>=196 || p<2 || p>=sz-2)return false;
   A x=rows[q][tape[p]];tape[p]=x.w;p+=x.d;q=x.n;
 }
 return false;
}
int main(int argc,char**argv){
 ifstream f("tail_input.txt");for(int&i:labels)f>>i;
 for(int q=0;q<196;q++)for(int b=0;b<2;b++)f>>base[q][b].w>>base[q][b].d>>base[q][b].n;
 mt19937 rng(20261113);
 int sk[9]={51,36,25,48,32,33,22,55,60};
 for(int trial=0;trial<25;trial++)for(int r=0;r<9;r++)for(int kind=0;kind<4;kind++){
   vector<int> vs(10+trial%4);for(int&i:vs)i=trial==0?0:(trial==1?1:rng()%7);
   if(kind==1)vs[r]=0;if(kind==2)vs[r]=max(1,vs[r]);
   Test t;t.start=ix(kind==3?sk[r]:(kind==0?64:0));t.finish=ix(kind==3?(r==0?1:3):(kind==1?97:40));t.pos=kind==2?0:-1;t.r=r;t.kind=kind;
   for(int i=0;i<int(vs.size());i++){
     t.tape.push_back(0);t.tape.push_back(i==r && kind!=3?0:1);
     for(int j=0;j<vs[i];j++)t.tape.push_back(1);
   }
   t.want=vector<int>(vs.begin(),vs.begin()+9);if(kind==0)t.want[r]++;if(kind==2)t.want[r]--;
   tests.push_back(t);
 }
 rows=base;
 for(int i=0;i<int(tests.size());i++)if(!run(tests[i],-1,-1)){cerr<<"baseline failure "<<i<<" kind "<<tests[i].kind<<" r "<<tests[i].r<<endl;return 2;}
 cout<<"baseline passed "<<tests.size()<<endl;
 vector<int> engine={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198};
 int checks=0,survivors=0;
 for(int an:engine){int a=ix(an);
  for(int b=0;b<196;b++)if(a!=b){
   for(int choice=0;choice<4;choice++){
    rows=base;
    for(int z=0;z<2;z++)rows[b][z]=base[(choice>>z&1)?a:b][z];
    for(auto&row:rows)for(auto&x:row)x.n=aliasq(x.n,a,b);
    bool ok=true;checks++;
    for(const Test&t:tests)if(!run(t,a,b)){ok=false;break;}
    if(ok){cout<<"SURVIVOR "<<an<<" -> "<<labels[b]<<" choice "<<choice<<endl;survivors++;}
   }
  }
 }
 cout<<"finished "<<checks<<" survivors "<<survivors<<endl;
}
