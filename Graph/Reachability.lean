import Std.Data.HashSet
import Mathlib
open Std

namespace Graph

-- Simple directed grap
def graph(n: Nat): Type := Fin n → List (Fin n)

-- Simple BFS algorithm core
-- s is the stack
-- o is the visited vertices ("observed")
def reachability'
  {n: Nat}
  (g: graph n)
  (s: List (Fin n))
  (o: HashSet (Fin n)): HashSet (Fin n) :=
match s with
| [] => o
| h :: t =>
  if _p: h ∈ o then
    reachability' g t o
  else
    reachability' g (t ++ g h) (o.insert h)
termination_by ((Finset.univ.filter (· ∉ o)).card, s)
decreasing_by
  ·
    right
    simp_wf
  ·
    left
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    ·
      apply Finset.subset_iff.mpr
      intro x hx
      simp_all
    ·
      intro c
      apply congrArg (h ∈ ·) at c
      simp at c
      exact _p c

-- The wrapper
def reachability
  {n: Nat}
  (g: graph n)
  (v: Fin n)
  : HashSet (Fin n)
  := reachability' g [v] HashSet.emptyWithCapacity

-- The rest of the file proves correctness and completeness
-- See mem_reachability_iff at the end of the file

-- A walk
inductive Walk {n: Nat} (g: graph n): (Fin n) -> (Fin n) -> Type
  | loop (a) : Walk g a a
  | step (a b c: Fin n) (hbc: b ∈ g a) (t: Walk g b c): Walk g a c

-- First, correctness
lemma reachability_correct'
  {n: Nat}
  (g: graph n)
  (s: List (Fin n))
  (o: HashSet (Fin n)): (w: Fin n) -> (w ∈ reachability' g s o) -> w ∈ o ∨ ∃ v ∈ s, Nonempty (Walk g v w):= by
  fun_induction reachability' g s o with
  | case1 o =>
    intro w hw
    left
    exact hw
  | case2 o x t hx ih =>
    intro w hw
    specialize ih w hw
    cases ih with
    | inl ih =>
      left
      exact ih
    | inr ih =>
      right
      have ⟨v, vh, ih⟩ := ih
      use v
      constructor
      ·
        exact List.mem_cons_of_mem x vh
      ·
        exact ih
  | case3 o x t hx ih =>
    intro w hw
    specialize ih w hw
    cases ih with
    | inl ih =>
      rw[HashSet.mem_insert] at ih
      cases ih with
      | inl ih =>
        simp at ih
        right
        use w
        constructor
        ·
          rw[ih]
          simp
        ·
          constructor
          exact Walk.loop w
      | inr ih =>
        left
        exact ih
    | inr ih =>
      right
      have ⟨v, vh, ih⟩ := ih
      rw[List.mem_append] at vh
      cases vh with
      | inl vh =>
        use v
        constructor
        ·
          exact List.mem_cons_of_mem x vh
        ·
          exact ih
      | inr vh =>
        use x
        constructor
        ·
          exact List.mem_cons_self
        ·
          refine Nonempty.map ?_ ih
          intro s
          exact Walk.step x v w vh s

theorem reachability_correct
  {n: Nat}
  (g: graph n)
  (v: Fin n)
  :
  (w: Fin n) -> (w ∈ reachability g v) -> Nonempty (Walk g v w) := by
  unfold reachability
  intro w hw
  have h := reachability_correct' g [v] HashSet.emptyWithCapacity w hw
  simp at h
  exact h

-- Now for completeness

-- Very simple lemma about reachability'
-- Basically we never delete nodes from o (visited vertices)
lemma reachability_lemma_o
  {n: Nat}
  {g: graph n}
  {s: List (Fin n)}
  {o: HashSet (Fin n)}
  (v: Fin n)
  (hv: v ∈ o)
  : v ∈ reachability' g s o := by
  fun_induction reachability' with
  | case1 o => exact hv
  | case2 o v' s hv' ih =>
    apply ih
    exact hv
  | case3 o v' s hv' ih =>
    apply ih
    simp_all

-- Also a simple lemma about reachability'
-- If a node is in the stack s
-- then it will be included in the visited vertices
lemma reachability_lemma_s
  {n: Nat}
  {g: graph n}
  {s: List (Fin n)}
  {o: HashSet (Fin n)}
  (v: Fin n)
  (hv: v ∈ s)
  : v ∈ reachability' g s o := by
  fun_induction reachability' with
  | case1 o =>
    simp at hv
  | case2 o v' s hv' ih =>
    by_cases hvv' : v = v'
    ·
      rw[hvv']
      exact reachability_lemma_o v' hv'
    ·
      apply ih
      rw[List.mem_cons] at hv
      simp_all
  | case3 o v' s hv' ih =>
    by_cases hvv' : v = v'
    ·
      rw[hvv']
      apply reachability_lemma_o
      simp
    ·
      apply ih
      simp_all

-- All unvisited vertices adjacent to visited vertices must be in the stack
def condition
  {n: Nat}
  (g: graph n)
  (s: List (Fin n))
  (o: HashSet (Fin n))
  : Prop := ∀v ∉ o, ∀w ∈ o, v ∈ g w → v ∈ s

-- The main workhorse
lemma condition_lemma
  {s: List (Fin n)}
  {o: HashSet (Fin n)}
  (c: condition g s o)
  : condition g [] (reachability' g s o) := by
    fun_induction reachability'
    with
    | case1 => exact c
    | case2 o v s hv ih =>
      apply ih
      unfold condition
      intro v' hv' w hw hv'w
      unfold condition at c
      specialize c v' hv' w hw hv'w
      rw[List.mem_cons] at c
      cases c with
      | inr h => exact h
      | inl h =>
        by_contra
        apply hv'
        rw[h]
        exact hv
    | case3 o v t hv ih =>
      apply ih
      unfold condition
      intro v' hv' w hw hv'w
      by_cases hwv: w = v
      ·
        rw[hwv] at hv'w
        simp_all
      ·
        unfold condition at c
        specialize c v' (by simp_all) w (by grind) hv'w
        rw[List.mem_cons] at c
        cases c with
        | inl h =>
          simp_all
        | inr h =>
          simp_all

-- A walk, defined like a reverse list.
-- so particularly, step looks like a -> ... -> b -> c
inductive RWalk {n: Nat} (g: graph n): (Fin n) -> (Fin n) -> Type
  | loop (a) : RWalk g a a
  | step (a b c: Fin n) (hbc: c ∈ g b) (t: RWalk g a b): RWalk g a c

-- The essential reachability lemma
lemma reachability_complete'
  {n: Nat}
  (g: graph n)
  (a c: Fin n)
  (w: RWalk g a c)
  : c ∈ reachability g a := by
  unfold reachability
  induction w with
  | loop =>
    apply reachability_lemma_s
    simp
  | step b c hbc t ih =>
    have cond : condition g [a] HashSet.emptyWithCapacity := by
      unfold condition
      simp
    apply condition_lemma at cond
    unfold condition at cond
    by_contra hc
    specialize cond c hc b ih hbc
    rw[←List.mem_nil_iff c]
    exact cond

-- And now using a regular walk
def walkToRWalk'
  (q: RWalk g s m)
  (w: Walk g m t)
  : RWalk g s t := match w with
    | Walk.loop _ => q
    | Walk.step m x t h r => walkToRWalk' (RWalk.step s m x h q) r

def walkToRWalk (w: Walk g s t): RWalk g s t := walkToRWalk' (RWalk.loop s) w

theorem reachability_complete
  {n: Nat}
  (g: graph n)
  (a c: Fin n)
  (w: Walk g a c)
  : c ∈ reachability g a := reachability_complete' g a c (walkToRWalk w)

-- Packaged
theorem mem_reachability_iff : w ∈ reachability g v ↔ Nonempty (Walk g v w) := by
  constructor
  ·
    exact reachability_correct g v w
  ·
    intro p
    apply p.elim
    exact reachability_complete g v w
