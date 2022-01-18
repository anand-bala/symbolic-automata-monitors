import networkx as nx
import numpy as np

from syma.automaton import SymbolicAutomaton


def compute_horizon(sa: SymbolicAutomaton) -> float:
    """
    The horizon of a symbolic automaton is defined as the length of the longest accepting
    trajectory. This is only computable in the case of a symbolic automaton with an
    accepting sink state.
    """
    # First check if there is a unique accepting sink.
    if not sa.has_unique_accepting_sink():
        # Otherwise return inf, i.e., possibly unbounded trajectory lengths.
        return np.inf

    source = sa.initial
    target = sa.accepting_sink()
    sinks = {target}
    rejecting = sa.rejecting_sink()
    if rejecting is not None:
        sinks.add(rejecting)

    # Essentially, for each transition in the automaton graph, we add a -1 edge weight
    # signifying the temporal cost of that transition.
    # First, we copy the underlying graph so as to not tarnish the automaton, and set
    # the edge weight to -1
    graph = nx.DiGraph()
    graph.add_nodes_from(sa._graph)
    for (u, v) in sa._graph.edges:
        # Prevent self loops in the sinks
        if u in sinks:
            continue
        else:
            graph.add_edge(u, v, weight=-1)
    # Then, we want to find the length of the shortest path from the initial state to
    # the final state.
    # If there is a negative weight cycle, the horizon is unbounded. Otherwise, the
    # horizon is finite.
    try:
        hrz = nx.bellman_ford_path_length(graph, source, target)
    except nx.NetworkXUnbounded:
        hrz = np.inf
    return abs(hrz)
