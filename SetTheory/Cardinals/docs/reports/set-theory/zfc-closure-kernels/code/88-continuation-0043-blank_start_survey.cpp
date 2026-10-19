#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

// Adapted from the attributed context246/search/seed_search.cpp.
// Finite initialization discovery only. The supplied table is never edited.
struct Action {int write=0,move=0,target=-1;};
using Table=std::array<std::array<Action,2>,256>;
constexpr int LO=-131070,HI=131070,OFFSET=131072;
struct Result {
  bool pass=false; int64_t steps=0; int head=0,header=0,state=0;
  std::string reason;std::vector<int> values,ones;
};

Result run(const Table& table,int start,int64_t limit) {
  std::vector<uint8_t> mem(262145,0);
  auto at=[&](int p)->uint8_t&{return mem[p+OFFSET];};
  int state=start,head=0,left=0,right=-1;
  for(int64_t step=0;step<=limit;step++) {
    if(state==254)return {false,step,head,0,state,"halt",{}, {}};
    if(state==96 && left==head-1 && at(head-1)) {
      int header=head;
      while(header<=right && !at(header))header++;
      if(header>=head+64 && header<=right) {
        int pos=header+1;std::vector<int> values;
        while(pos<right && !at(pos) && at(pos+1)) {
          int begin=++pos;while(pos<=right && at(pos))pos++;
          values.push_back(pos-begin-1);
        }
        // Physical indices 2,7,0 are logical T,H,W respectively.
        if(pos>right && values.size()>=10 && values[0]==0 && values[2]==0 && values[7]==0) {
          std::vector<int> ones;
          for(int i=left;i<=right;i++)if(at(i))ones.push_back(i);
          return {true,step,head,header,state,"safe_empty_pc_frame",values,ones};
        }
      }
    }
    if(step==limit)return {false,step,head,0,state,"fuel",{}, {}};
    Action action=table[state][at(head)];
    if(action.target<0)return {false,step,head,0,state,"undefined",{}, {}};
    at(head)=action.write;
    if(action.write) {
      if(right<left)left=right=head;
      else {left=std::min(left,head);right=std::max(right,head);}
    } else if(right>=left) {
      if(head==left)while(left<=right && !at(left))left++;
      if(head==right)while(right>=left && !at(right))right--;
    }
    head+=action.move;state=action.target;
    if(head<LO || head>HI)return {false,step+1,head,0,state,"window",{}, {}};
  }
  return {};
}

int main(int argc,char**argv) {
  if(argc!=3){std::cerr<<"usage: blank_start_survey table.tm limit\n";return 2;}
  Table table{};std::array<std::array<bool,2>,256> present{};
  std::vector<int> states;std::ifstream input(argv[1]);std::string line;
  if(!input){std::cerr<<"cannot read table\n";return 2;}
  while(std::getline(input,line)) {
    if(line.empty() || line[0]=='#')continue;
    std::istringstream stream(line);int q,b,w,target;char direction;
    if(!(stream>>q>>b>>w>>direction>>target) || q<0 || q>=256 || q==254 || b<0 || b>1 || w<0 || w>1 || target<0 || target>=256 || (direction!='R' && direction!='L') || present[q][b])return 3;
    present[q][b]=true;table[q][b]={w,direction=='R'?1:-1,target};
    if(b==0)states.push_back(q);
  }
  for(int q=0;q<256;q++)if(present[q][0]!=present[q][1])return 3;
  for(int q:states)for(int b=0;b<2;b++) {
    int target=table[q][b].target;
    if(!present[q][b] || (target!=254 && (!present[target][0] || !present[target][1])))return 3;
  }
  const int64_t limit=std::stoll(argv[2]);if(limit<0)return 3;
  int passes=0;int64_t total=0;
  for(int start:states) {
    Result result=run(table,start,limit);total+=result.steps;
    std::cout<<"{\"start\":"<<start<<",\"pass\":"<<(result.pass?"true":"false")
      <<",\"steps\":"<<result.steps<<",\"head\":"<<result.head<<",\"state\":"<<result.state
      <<",\"reason\":\""<<result.reason<<"\"";
    if(result.pass) {
      passes++;
      std::cout<<",\"header\":"<<result.header<<",\"values\":[";
      for(size_t i=0;i<result.values.size();i++)std::cout<<(i?",":"")<<result.values[i];
      std::cout<<"],\"ones\":[";
      for(size_t i=0;i<result.ones.size();i++)std::cout<<(i?",":"")<<result.ones[i];
      std::cout<<"]";
    }
    std::cout<<"}\n";
  }
  std::cerr<<"DONE starts="<<states.size()<<" passes="<<passes<<" per_start_limit="<<limit
    <<" total_transitions="<<total<<" head_window=["<<LO<<","<<HI<<"]\n";
}
