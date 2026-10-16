#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

// Independent generic literal-table simulator; the initializer algorithm and
// the expected endpoint are not used by the transition loop.
struct Action { int write=-1, move=0, next=-1; };
int main(int argc, char** argv) {
    if(argc!=5) throw std::runtime_error("table target limit output required");
    std::ifstream in(argv[1]); if(!in) throw std::runtime_error("missing table");
    std::vector<Action> table;
    std::string line;
    while(std::getline(in,line)) {
        if(line.empty() || line[0]=='#') continue;
        std::istringstream row(line); int q,b,w,n; char d;
        if(!(row>>q>>b>>w>>d>>n) || q<0 || b<0 || b>1 || w<0 || w>1
           || (d!='L' && d!='R') || n<0)
            throw std::runtime_error("malformed transition");
        if(table.size()<=2*q+b) table.resize(2*q+b+1);
        if(table[2*q+b].write!=-1) throw std::runtime_error("duplicate row");
        table[2*q+b]={w,d=='R'?1:-1,n};
    }
    for(auto a:table) if(a.write<0) throw std::runtime_error("table hole");
    int target=std::stoi(argv[2]); std::uint64_t limit=std::stoull(argv[3]);
    constexpr int origin=1000000;
    std::vector<unsigned char> tape(2*origin+1,0);
    int q=0,h=origin,lo=h,hi=h; std::uint64_t steps=0;
    while(q!=target && steps<limit) {
        if(q<0 || 2*q+1>=int(table.size()))
            throw std::runtime_error("unexpected halt or invalid state");
        if(h<=0 || h>=int(tape.size())-1)
            throw std::runtime_error("finite simulation boundary reached");
        auto a=table[2*q+tape[h]];
        tape[h]=a.write; h+=a.move; q=a.next; ++steps;
        lo=std::min(lo,h); hi=std::max(hi,h);
    }
    if(q!=target) throw std::runtime_error("target not reached within bound");
    std::ofstream out(argv[4]);
    out << "{\"steps\":"<<steps<<",\"state\":"<<q<<",\"head\":"<<h-origin
        <<",\"visited_min\":"<<lo-origin<<",\"visited_max\":"<<hi-origin
        <<",\"ones\":[";
    bool first=true;
    for(int i=0;i<int(tape.size());++i) if(tape[i]) {
        if(!first)out<<',';first=false;out<<i-origin;
    }
    out<<"]}\n";
}
