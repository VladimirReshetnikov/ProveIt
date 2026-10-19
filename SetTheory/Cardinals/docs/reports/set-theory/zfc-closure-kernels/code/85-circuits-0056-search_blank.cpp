#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

// Dynamic-state, finite blank search.  Acceptance is a complete clean frame,
// with the logical Safe premise certified by safe_start_proof.tex.  Exhaustion
// of fuel is not a nonhalting result.  No altered table is generated here.
struct Action { int write = 0, move = 0, target = -1; };
struct Result {
    std::string outcome;
    int64_t steps = 0;
    int head = 0, header = 0, state = 0;
    std::vector<int> values;
};

std::pair<int,int> unpair(int z) {
    int diagonal = static_cast<int>((std::sqrt(8.0*z+1)-1)/2);
    while (int64_t(diagonal+1)*(diagonal+2)/2 <= z) ++diagonal;
    while (int64_t(diagonal)*(diagonal+1)/2 > z) --diagonal;
    int b = z - int64_t(diagonal)*(diagonal+1)/2;
    return {diagonal-b,b};
}

std::vector<int8_t> classify(int bound) {
    std::vector<int8_t> out(bound+1,0);
    out[0]=1;
    for(int n=1;n<=bound;++n) {
        auto [a,b]=unpair(n/4);
        int tag=n%4;
        if(tag==1 && a==b) out[n]=-1;
        else if(tag==3 && a==b) out[n]=1;
        else if(tag==2 && out[b]==1) out[n]=1;
        else if(tag==0) {
            if(out[b]==1 || out[a]==-1 || a==b) out[n]=1;
            else if(out[a]==1 && out[b]==-1) out[n]=-1;
        }
    }
    return out;
}

bool stack_safe(int z,const std::vector<int8_t>& cls) {
    while(z) {
        auto [a,b]=unpair(z);
        if(a>=int(cls.size()) || cls[a]!=1 || b>=z) return false;
        z=b;
    }
    return true;
}

Result run(const std::vector<std::array<Action,2>>& table,int start,
           int64_t limit,const std::vector<int8_t>& cls) {
    const int origin=static_cast<int>(limit)+4;
    std::vector<uint8_t> tape(2*origin+1,0);
    int state=start,head=0,left=0,right=-1;
    auto cell=[&](int p)->uint8_t& {return tape.at(p+origin);};
    for(int64_t steps=0;steps<=limit;++steps) {
        if(state==254) return {"HALT",steps,head,0,state,{}};
        if(state==96 && right>=left && left==head-1 && cell(left)) {
            int header=head;
            while(header<=right && cell(header)==0) ++header;
            if(header<=right && header-head>=40) {
                std::vector<int> values;
                int cursor=header+1;
                while(cursor<right && cell(cursor)==0 && cell(cursor+1)==1) {
                    int first=++cursor;
                    while(cursor<=right && cell(cursor)==1) ++cursor;
                    values.push_back(cursor-first-1);
                }
                if(cursor>right && values.size()>=10 &&
                   values[2]<int(cls.size()) && cls[values[2]]==1 &&
                   values[7]<int(cls.size()) && cls[values[7]]==1 &&
                   stack_safe(values[0],cls))
                    return {"SAFE_ROOT",steps,head,header,state,values};
            }
        }
        if(steps==limit) return {"FUEL",steps,head,0,state,{}};
        if(state<0 || state>=int(table.size())) return {"MISSING_STATE",steps,head,0,state,{}};
        auto action=table[state][cell(head)];
        if(action.target<0 || (action.move!=1 && action.move!=-1))
            return {"MISSING_ROW",steps,head,0,state,{}};
        cell(head)=action.write;
        if(action.write) {
            if(right<left) left=right=head;
            else {left=std::min(left,head);right=std::max(right,head);}
        } else if(right>=left) {
            if(head==left) while(left<=right && cell(left)==0) ++left;
            if(head==right) while(right>=left && cell(right)==0) --right;
        }
        head+=action.move;
        state=action.target;
    }
    throw std::logic_error("Unreachable loop exit");
}

int main(int argc,char**argv) {
    if(argc!=4) {std::cerr<<"usage: search_blank TABLE LIMIT OUTPUT_JSONL\n";return 2;}
    int64_t limit=std::stoll(argv[2]);
    if(limit<0 || limit>10000000) {std::cerr<<"Unsupported limit\n";return 2;}
    std::ifstream input(argv[1]);
    if(!input) return 2;
    std::vector<std::array<Action,2>> table;
    std::vector<int> states;
    std::string line;
    while(std::getline(input,line)) {
        if(line.empty()||line[0]=='#') continue;
        std::istringstream row(line);
        int q,b,w,t;char direction;
        if(!(row>>q>>b>>w>>direction>>t) || q<0 || b<0 || b>1 || w<0 || w>1 ||
           (direction!='L'&&direction!='R')) return 2;
        if(q>=int(table.size())) table.resize(q+1);
        if(table[q][b].target>=0) return 2;
        table[q][b]={w,direction=='R'?1:-1,t};
        if(b==0) states.push_back(q);
    }
    std::sort(states.begin(),states.end());
    auto cls=classify(static_cast<int>(limit)+1);
    std::ofstream out(argv[3]);
    if(!out) return 2;
    std::array<int,9> physical={6,2,0,4,3,7,8,5,1};
    int successes=0;
    for(int start:states) {
        auto result=run(table,start,limit,cls);
        out<<"{\"start\":"<<start<<",\"outcome\":\""<<result.outcome<<"\",\"steps\":"<<result.steps
           <<",\"head\":"<<result.head<<",\"state\":"<<result.state;
        if(result.outcome=="SAFE_ROOT") {
            ++successes;
            out<<",\"header\":"<<result.header<<",\"distance\":"<<result.header-result.head<<",\"values\":[";
            for(size_t i=0;i<result.values.size();++i) {if(i)out<<',';out<<result.values[i];}
            out<<"],\"logical\":[";
            for(int i=0;i<9;++i) {if(i)out<<',';out<<result.values[physical[i]];}
            out<<']';
            std::cout<<"SAFE_ROOT start="<<start<<" steps="<<result.steps<<" head="<<result.head
                     <<" distance="<<result.header-result.head<<" spares="<<result.values.size()-9<<std::endl;
        }
        out<<"}\n";
    }
    std::cout<<"DONE states="<<states.size()<<" roots="<<successes<<" limit="<<limit<<std::endl;
}
