import Basicnumbertheory

/-
Syntax:
- def defines a new term (constant, function, or type)
EvenO (n : Nat) : Prop declares EvenO as a property of natural numbers
- ∃ k : Nat, n = 2 * k states that there exists a natural number k
- n = 2 * k means n is equal to twice k, which defines n as even
-/
def EvenO (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

/-
Syntax:
- theorem declares a new theorem named even_squared_is_even
- (n : Nat) introduces a natural number n as a variable
- (h : EvenO n) introduces a hypothesis h that n is even
- EvenO (n * n) states the conclusion that n squared is also even
- by begins the proof
-/
-- theorem name input hypothesis conclusion proof
theorem even_squared_is_even (n : Nat) (h : EvenO n) : EvenO (n * n) := by
    --destructure the hypothesis h to extract k such that n = 2 * k
    rcases h with ⟨k, hk⟩
    -- refine the goal to show there exists a natural number (k * (2 * k)) such that n * n = 2 * (k * (2 * k))
    -- _? is a placeholder
    refine ⟨k * (2 * k), ?_⟩
    -- After rewriting n via hk, (2*k)*(2*k) = 2*(k*(2*k)) by associativity
    -- simp is a tactic that simplifies expressions using known equalities and properties
    simp [hk, Nat.mul_assoc]

    -- So, we're done!
