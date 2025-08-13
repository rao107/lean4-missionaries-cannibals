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

lemma init_valid : valid_state init := by unfold valid_state bank_safe init m_right; simp
lemma step1_valid : valid_state step1 := by unfold valid_state bank_safe step1 m_right; simp
lemma step2_valid : valid_state step2 := by unfold valid_state bank_safe step2 m_right; simp
lemma step3_valid : valid_state step3 := by unfold valid_state bank_safe step3 m_right; simp
lemma step4_valid : valid_state step4 := by unfold valid_state bank_safe step4 m_right; simp
lemma step5_valid : valid_state step5 := by unfold valid_state bank_safe step5 m_right c_right; simp
lemma step6_valid : valid_state step6 := by unfold valid_state bank_safe step6 m_right c_right; simp
lemma step7_valid : valid_state step7 := by unfold valid_state bank_safe step7 m_right c_right; simp
lemma step8_valid : valid_state step8 := by unfold valid_state bank_safe step8 m_right c_right; simp
lemma step9_valid : valid_state step9 := by unfold valid_state bank_safe step9 m_right c_right N; simp
lemma step10_valid : valid_state step10 := by unfold valid_state bank_safe step10 m_right c_right; simp
lemma goal_valid : valid_state goal := by unfold valid_state bank_safe goal m_right c_right; simp

lemma prove_step (s_valid : valid_state s) (t_valid : valid_state t) (s_t_move : valid_move s t) : step s t := by
  unfold step
  constructorm* _ ∧ _, _ ∧ _
  · exact s_valid
  · exact t_valid
  · exact s_t_move

theorem init_to_step1 : step init step1 := by
  apply prove_step init_valid step1_valid
  unfold valid_move init step1; simp

theorem step1_to_step2 : step step1 step2 := by
  apply prove_step step1_valid step2_valid
  unfold valid_move step1 step2; simp

theorem step2_to_step3 : step step2 step3 := by
  apply prove_step step2_valid step3_valid
  unfold valid_move step2 step3; simp

theorem step3_to_step4 : step step3 step4 := by
  apply prove_step step3_valid step4_valid
  unfold valid_move step3 step4; simp

theorem step4_to_step5 : step step4 step5 := by
  apply prove_step step4_valid step5_valid
  unfold valid_move step4 step5; simp

theorem step5_to_step6 : step step5 step6 := by
  apply prove_step step5_valid step6_valid
  unfold valid_move step5 step6; simp

theorem step6_to_step7 : step step6 step7 := by
  apply prove_step step6_valid step7_valid
  unfold valid_move step6 step7; simp

theorem step7_to_step8 : step step7 step8 := by
  apply prove_step step7_valid step8_valid
  unfold valid_move step7 step8; simp

theorem step8_to_step9 : step step8 step9 := by
  apply prove_step step8_valid step9_valid
  unfold valid_move step8 step9; simp

theorem step9_to_step10 : step step9 step10 := by
  apply prove_step step9_valid step10_valid
  unfold valid_move step9 step10; simp

theorem step10_to_goal : step step10 goal := by
  apply prove_step step10_valid goal_valid
  unfold valid_move step10 goal; simp

theorem init_to_goal : reachable init goal := by
  apply reachable.trans; exact init_to_step1
  apply reachable.trans; exact step1_to_step2
  apply reachable.trans; exact step2_to_step3
  apply reachable.trans; exact step3_to_step4
  apply reachable.trans; exact step4_to_step5
  apply reachable.trans; exact step5_to_step6
  apply reachable.trans; exact step6_to_step7
  apply reachable.trans; exact step7_to_step8
  apply reachable.trans; exact step8_to_step9
  apply reachable.trans; exact step9_to_step10
  apply reachable.trans; exact step10_to_goal
  exact reachable.refl goal
