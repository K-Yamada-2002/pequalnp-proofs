// Direct enumeration with a truth table for every live wire.
#include <algorithm>
#include <array>
#include <iostream>
#include <string>
#include <vector>

using Table = __uint128_t;
using Codes = std::array<int, 128>;
using Wires = std::vector<Table>;

constexpr int edges[][2] = {{0,1}, {0,2}, {2,1}, {0,3}, {3,4}, {4,5}, {5,6}, {6,1}};

struct Search {
    Table target = 0;
    Codes truth{};
    // At budget 11 the width check permits at most 12 live wires.
    std::array<int, 1 << 12> labels{};
    int generation = 0;
    unsigned long long visits = 0, distinguished = 0;

    bool separates(const Codes& codes) {
        if (++generation == 1000000000) {
            labels.fill(0);
            generation = 1;
        }
        for (int x = 0; x < 128; ++x) {
            int& label = labels[codes[x]];
            int required = truth[x] ? generation : -generation;
            if (label == -required) return false;
            label = required;
        }
        return true;
    }

    bool visit(const Wires& wires, int left, const Codes& codes) {
        ++visits;
        if (std::find(wires.begin(), wires.end(), target) != wires.end()) return true;
        int n = static_cast<int>(wires.size());
        if (left == 0 || n > left + 1 || !separates(codes)) return false;
        ++distinguished;

        for (int a = 0; a < n; ++a) {
            for (int b = a; b < n; ++b) {
                bool unary = a == b;
                if (unary && n > left) continue;
                for (int op = unary ? 2 : 0; op <= (unary ? 2 : 1); ++op) {
                    Table value = op == 2 ? ~wires[a] :
                                  op == 0 ? wires[a] & wires[b] : wires[a] | wires[b];
                    if (value == 0 || value == ~Table(0)) continue;
                    if (std::find(wires.begin(), wires.end(), value) != wires.end()) continue;
                    for (int save = 0; save < (unary ? 2 : 4); ++save) {
                        int width = n - (unary ? 1 : 2) + 1 + __builtin_popcount(save);
                        if (width > left) continue;
                        Wires next;
                        next.reserve(width);
                        // Delete the bits of spent operands, from highest bit to lowest.
                        std::array<int, 2> spent{};
                        int count = 0;
                        if (!unary && !(save & 2)) spent[count++] = b;
                        if (!(save & 1)) spent[count++] = a;
                        for (int i = 0; i < n; ++i) {
                            if ((i == a && !(save & 1)) || (!unary && i == b && !(save & 2))) continue;
                            next.push_back(wires[i]);
                        }
                        next.push_back(value);
                        Codes child = codes;
                        for (int k = 0; k < count; ++k) {
                            int bit = spent[k], low = (1 << bit) - 1;
                            for (int& word : child) word = (word & low) | ((word >> (bit + 1)) << bit);
                        }
                        for (int x = 0; x < 128; ++x)
                            child[x] |= int((value >> x) & 1) << (width - 1);
                        if (visit(next, left - 1, child)) return true;
                    }
                }
            }
        }
        return false;
    }
};

int main(int argc, char** argv) {
    if (argc != 2) return 2;
    int budget = std::stoi(argv[1]);
    if (budget < 0 || budget > 11) return 2;
    Search search;
    Wires inputs(7);
    Codes codes{};
    for (int x = 0; x < 128; ++x) {
        codes[x] = x;
        for (int i = 0; i < 7; ++i)
            if ((x >> i) & 1) inputs[i] |= Table(1) << x;
        for (auto& edge : edges)
            if (((x >> edge[0]) & 1) && ((x >> edge[1]) & 1)) search.truth[x] = 1;
        search.target |= Table(search.truth[x]) << x;
    }
    bool found = search.visit(inputs, budget, codes);
    std::cout << (found ? "SAT" : "UNSAT") << " budget " << budget << " nodes " << search.visits
              << " distinct-label cuts " << search.distinguished << '\n';
}
