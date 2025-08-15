import Mathlib

-- number of missionaries and cannibals
abbrev N : ℕ := 3

-- number of missionaries and cannibals on left bank and where the boat is
structure State where
  m_left : Fin (N+1)
  c_left : Fin (N+1)
  boat_on_left : Bool

-- needed to show number of missionaries and cannibals on right bank is also Fin (N+1)
lemma right_fin_n_plus_one : ∀ x : Fin (N+1), N - ↑x < N + 1 := by grind only [cases Or]

-- number of missionaries and cannibals on right bank
def m_right (s: State) : Fin (N+1) := ⟨N - s.m_left, right_fin_n_plus_one s.m_left⟩
def c_right (s: State) : Fin (N+1) := ⟨N - s.c_left, right_fin_n_plus_one s.c_left⟩

-- condition for missionaries to be safe
def bank_safe (m c : Fin (N+1)) : Prop := m = 0 ∨ m ≥ c

-- state is valid if missionaries are safe on both banks
def valid_state (s: State) : Prop :=
  bank_safe s.m_left s.c_left ∧
  bank_safe (m_right s) (c_right s)

-- conditions to move missionaries and cannibals across the river from State s to t
def valid_move (s t: State) : Prop :=
  s.boat_on_left ≠ t.boat_on_left ∧ -- boat must move
  (s.m_left ≠ t.m_left ∨ s.c_left ≠ t.c_left) ∧ -- boat has to have at least one person
  if s.boat_on_left then
    t.m_left ≤ s.m_left ∧ -- missionaries leaving left bank
    t.c_left ≤ s.c_left ∧ -- cannibals leaving left bank
    (s.m_left - t.m_left) + (s.c_left - t.c_left) ≤ 2 -- boat only has two seats
  else
    s.m_left ≤ t.m_left ∧ -- missionaries arriving to left bank
    s.c_left ≤ t.c_left ∧ -- cannibals arriving to left bank
    (t.m_left - s.m_left) + (t.c_left - s.c_left) ≤ 2 -- boat only has two seats

-- stepping from one valid State to another
def step (s t : State) : Prop :=
  valid_state s ∧ valid_state t ∧ valid_move s t

-- a State is reachable to its own state and to any other it can step to
inductive reachable : State → State → Prop
  | refl (s : State) : reachable s s
  | trans {s u t} : step s u → reachable u t → reachable s t

-- initial State, all missionaries and cannibals on the left
def init : State := { m_left := 3, c_left := 3, boat_on_left := true }

def step1 : State := { m_left := 3, c_left := 1, boat_on_left := false }
def step2 : State := { m_left := 3, c_left := 2, boat_on_left := true }
def step3 : State := { m_left := 3, c_left := 0, boat_on_left := false }
def step4 : State := { m_left := 3, c_left := 1, boat_on_left := true }
def step5 : State := { m_left := 1, c_left := 1, boat_on_left := false }
def step6 : State := { m_left := 2, c_left := 2, boat_on_left := true }
def step7 : State := { m_left := 0, c_left := 2, boat_on_left := false }
def step8 : State := { m_left := 0, c_left := 3, boat_on_left := true }
def step9 : State := { m_left := 0, c_left := 1, boat_on_left := false }
def step10 : State := { m_left := 0, c_left := 2, boat_on_left := true }

-- goal State, all missionaries and cannibals on the right
def goal : State := { m_left := 0, c_left := 0, boat_on_left := false }

macro "validateState " state:ident : tactic =>
  `(tactic| try unfold valid_state bank_safe $state m_right c_right N; simp)

macro "validateMove " s:ident t:ident : tactic =>
  `(tactic| try unfold valid_move $s $t; simp)

macro "validateStep " s:ident t:ident : tactic =>
  `(tactic| try unfold step; constructorm* _ ∧ _, _ ∧ _; validateState $s; validateState $t; validateMove $s $t)

theorem init_to_goal : reachable init goal := by
  apply reachable.trans (s := init) (u := step1) (t := goal); validateStep init step1
  apply reachable.trans (s := step1) (u := step2) (t := goal); validateStep step1 step2
  apply reachable.trans (s := step2) (u := step3) (t := goal); validateStep step2 step3
  apply reachable.trans (s := step3) (u := step4) (t := goal); validateStep step3 step4
  apply reachable.trans (s := step4) (u := step5) (t := goal); validateStep step4 step5
  apply reachable.trans (s := step5) (u := step6) (t := goal); validateStep step5 step6
  apply reachable.trans (s := step6) (u := step7) (t := goal); validateStep step6 step7
  apply reachable.trans (s := step7) (u := step8) (t := goal); validateStep step7 step8
  apply reachable.trans (s := step8) (u := step9) (t := goal); validateStep step8 step9
  apply reachable.trans (s := step9) (u := step10) (t := goal); validateStep step9 step10
  apply reachable.trans (s := step10) (u := goal) (t := goal); validateStep step10 goal
  exact reachable.refl goal
