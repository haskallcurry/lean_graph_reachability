import Graph.Reachability
open Graph

-- Demo: cube
def D: Nat := 3
def P: graph (2 ^ D) := by
  intro a
  refine List.filter ?_ (List.finRange (2 ^ D))
  intro b
  have av := BitVec.ofFin a
  have bv := BitVec.ofFin b
  have i := ~~~bv &&& av
  have d := ~~~av &&& bv
  -- equivalent to i == 0 && d.popcount = 1 (if such a function existed)
  exact i == 0 && d != 0 && d &&& (d - 1) == 0

def main: IO Unit :=
  let pairs := [(1, 2), (2, 1), (1, 3), (3, 1)]
  for ⟨a, b⟩ in pairs do
    if b ∈ reachability P a then
      IO.println s!"{a}→{b}"
    else
      IO.println s!"{a}→⃠{b}"
