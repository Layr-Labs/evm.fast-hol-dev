#!/usr/bin/env python3
"""Construct an untrusted stack-ranking witness from extracted call edges.

The HOL checkedRanks predicate must accept this data before it proves a bound.
No soundness depends on this generator or the edge extraction.
"""
from __future__ import annotations

import argparse
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("edges", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    graph: dict[int, set[int]] = {}
    for line in args.edges.read_text().splitlines():
        values = [int(value) for value in line.split()]
        if not values:
            continue
        node, *targets = values
        if node in graph or any(value < 0 for value in values):
            raise ValueError(f"invalid or duplicate function {node}")
        graph[node] = set(targets)
    if not graph:
        raise ValueError("empty call graph")
    ranks: dict[int, int] = {}
    visiting: set[int] = set()

    def rank(node: int) -> int:
        if node in ranks:
            return ranks[node]
        if node not in graph:
            raise ValueError(f"missing callee {node}")
        if node in visiting:
            raise ValueError(f"call cycle through {node}")
        visiting.add(node)
        value = max((rank(target) + 1 for target in graph[node]), default=0)
        visiting.remove(node)
        ranks[node] = value
        return value

    for node in sorted(graph):
        rank(node)
    entries = ";\n     ".join(f"({node},{ranks[node]})" for node in sorted(ranks))
    args.output.write_text(
        "(* Generated untrusted ranking data; checked by initStackCertificate. *)\n"
        "Theory initStackRanksData\nAncestors sptree\nLibs preamble\n"
        "Definition optimized_ranks_def:\n"
        "  optimized_ranks : num num_map = fromAList\n"
        f"    [{entries}]\nEnd\n"
    )
    print(f"Wrote {len(ranks)} function ranks; maximum {max(ranks.values())}")


if __name__ == "__main__":
    main()
