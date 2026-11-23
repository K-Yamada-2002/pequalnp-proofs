// Independent verifier. Each signal evaluates all 256 assignments in four words.
// Enumerate predecessor pairs in creation order, discard or retain each operand,
// and prune any state that fails a monotone separation requirement.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Word = std::uint64_t;
using Table = std::array<Word,4>;
struct Signal {
    Table values{};
    std::array<Word,2> distinguishes{};
};
struct Problem {
    std::vector<int> positive, negative;
    Table target{};
    std::array<Word,2> required{};
    std::uint64_t visited = 0;

    bool bit(const Table& t, int k) const { return (t[k/64] >> (k%64)) & 1; }

    Signal signal(Table t) const {
        Signal s{t, {}};
        unsigned k=0;
        for (int pos : positive) for (int neg : negative) {
            if (bit(t,pos) && !bit(t,neg)) s.distinguishes[k/64] |= Word(1) << (k%64);
            ++k;
        }
        return s;
    }

    bool search(const std::vector<Signal>& w, int budget) {
        ++visited;
        for (const auto& s : w) if (s.values == target) return true;
        if (!budget || int(w.size()) > budget+1) return false;
        for (unsigned a=0; a<w.size(); ++a) for (unsigned b=0; b<a; ++b) {
            std::vector<Signal> rest;
            std::array<Word,2> outside{};
            for (unsigned i=0; i<w.size(); ++i) if (i!=a && i!=b) {
                rest.push_back(w[i]);
                for (int h=0;h<2;++h) outside[h] |= w[i].distinguishes[h];
            }
            for (bool meet : {false,true}) {
                Table t;
                for (int h=0; h<4; ++h)
                    t[h] = meet ? w[a].values[h] & w[b].values[h] : w[a].values[h] | w[b].values[h];
                if (std::any_of(w.begin(),w.end(),[&](const Signal& s){return s.values==t;})) continue;
                const auto new_wire = signal(t);
                for (unsigned save=0; save<4; ++save) {
                    const int next_size = int(w.size())-1 + (save&1) + ((save>>1)&1);
                    if (next_size > budget) continue;
                    auto covered=outside;
                    for (int h=0;h<2;++h) {
                        covered[h] |= new_wire.distinguishes[h];
                        if (save&1) covered[h] |= w[a].distinguishes[h];
                        if (save&2) covered[h] |= w[b].distinguishes[h];
                    }
                    if (covered != required) continue;
                    auto next=rest;
                    if (save&1) next.push_back(w[a]);
                    if (save&2) next.push_back(w[b]);
                    next.push_back(new_wire);
                    if (search(next,budget-1)) return true;
                }
            }
        }
        return false;
    }
};

int main(int argc, char** argv) {
    if (argc!=3) return 1;
    std::string graph=argv[1];
    int n=graph=="cube" ? 8 : 6;
    std::vector<std::array<int,2>> edges;
    if (graph=="cube") {
        for (int a=0;a<8;++a) for (int direction : {1,2,4})
            if ((a^direction)>a) edges.push_back({a,a^direction});
    } else if (graph=="prism") {
        for (int a=0;a<3;++a) {
            edges.push_back({a,(a+1)%3}); edges.push_back({a+3,(a+1)%3+3}); edges.push_back({a,a+3});
        }
    } else if (graph=="wheel") {
        for (int a=0;a<5;++a) { edges.push_back({a,(a+1)%5}); edges.push_back({a,5}); }
    } else return 1;
    Problem p;
    for (auto e : edges) p.positive.push_back((1<<e[0])|(1<<e[1]));
    for (int m=0;m<(1<<n);++m)
        for (int e : p.positive) if ((m&e)==e) p.target[m/64] |= Word(1)<<(m%64);
    for (int m=0;m<(1<<n);++m) if (!p.bit(p.target,m)) {
        bool maximal=true;
        for (int a=0;a<n;++a) if (!(m&(1<<a)) && !p.bit(p.target,m|(1<<a))) maximal=false;
        if (maximal) p.negative.push_back(m);
    }
    if (p.positive.size()*p.negative.size()>128) throw std::logic_error("separation mask overflow");
    p.required=p.signal(p.target).distinguishes;
    std::vector<Signal> inputs;
    for (int i=0;i<n;++i) {
        Table t{};
        for (int m=0;m<(1<<n);++m) if (m&(1<<i)) t[m/64] |= Word(1)<<(m%64);
        inputs.push_back(p.signal(t));
    }
    bool found=p.search(inputs,std::stoi(argv[2]));
    std::cout << graph << " " << argv[2] << " " << (found?"SAT":"UNSAT")
              << " tree nodes " << p.visited << "\n";
}
