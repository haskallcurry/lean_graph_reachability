This repo formalizes a BFS graph reachability algorithm
and proves correctness and completeness w.r.t. an inductively defined walk.

Main theorem:
  w ∈ reachability g v ↔ Nonempty (Walk g v w)

Build:
  lake build

Demo:
  lake exe reachability_demo