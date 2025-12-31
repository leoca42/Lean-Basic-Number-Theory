import Mathlib.Tactic.Ring

/-
This is just a list of basic number theory proofs I've been doing to
1. Learn Lean syntax
2. Get familiar with writing proofs in a proof assistant

So far (Dec 31st, 2025)
- Definitions of even and odd natural numbers
        (I know Mathlib has them but wanted to rewrite anyways)
- Proofs for even squared is even, odd squared is odd
- Recursive formulas for triangle numbers and sum of squares
- Proof for triangle numbers formula (INCOMPLETE)
- Proof for sum of squares formula (INCOMPLETE)
-/

/-
Syntax:
- def defines a new term (constant, function, or type)
EvenO (n : Nat) : Prop declares EvenO as a property of natural numbers
- ∃ k : Nat, n = 2 * k states that there exists a natural number k
- n = 2 * k means n is equal to twice k, which defines n as even
-/
def EvenO (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

def OddO (n : Nat) : Prop := ∃ k : Nat, n = 2 * k + 1

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
    -- destructure the hypothesis h to extract k such that n = 2 * k
    rcases h with ⟨k, hk⟩
    -- refine the goal to show there exists a natural number (k * (2 * k))
        -- such that n * n = 2 * (k * (2 * k))
    -- _? is a placeholder
    refine ⟨k * (2 * k), ?_⟩
    -- after rewriting n via hk, (2*k)*(2*k) = 2*(k*(2*k)) by associativity
    -- simp is a tactic that simplifies expressions using known equalities and properties
    simp [hk, Nat.mul_assoc]

    -- So, we're done!


theorem odd_sq_is_odd (n : Nat) (h : OddO n) : OddO (n * n) := by
        rcases h with ⟨k, hk⟩
        refine ⟨k * (2 * k + 2), ?_⟩
        rw [hk]
        ring

/-
Defines a recursive function for the triangle numbers
-/
def triangle : Nat → Nat
 | 0     => 0
 | n + 1 => triangle n + (n + 1)



/-
Proves that the nth triangle number is n * (n + 1) / 2
This is the closed-form formula for triangle numbers
- Uses induction on n
-/
theorem triangle_numbers (n : Nat) : triangle n = n * (n + 1) / 2 := by
        induction n with
        | zero =>
                simp [triangle]
        | succ n ih =>
                /-
                Tactic here is the write multiple smaller hypotheses of precise algebra steps
                then rewrite the main goal step by step using those hypotheses
                -/
                simp [triangle]
                rw [ih]
                have h1 : (n + 1) = ((n + 1) * 2) / 2 := by
                  simp
                conv =>
                        lhs
                        -- move into the second argument of (+)
                        congr
                        · skip
                        · rw [h1]   -- where h : (n+1) = 2 * (n+1) / 2
                have h_add_div : (n * (n + 1) / 2 + (n + 1) * 2 / 2) = (n * (n + 1) + 2 * (n + 1)) / 2 := by
                        sorry --placeholder for figuring out the proper syntax for this later
                rw [h_add_div]
                have h3 : (n * (n + 1) + 2 * (n + 1)) = ((n + 2) * (n + 1)) := by
                        ring -- Lean's pre-built simplifier can solve this
                rw [h3]
                have h4 : (n + 2) = ((n + 1) + 1) := by
                        simp -- Another of Lean's pre-built simplifiers
                rw [h4]
                have h5 : ((n + 1 + 1) * (n + 1)) / 2 = ((n + 1) * (n + 1 + 1)) / 2 := by
                        sorry --placeholder for figuring out the proper syntax for this later
                rw [h5]

/-
Recursive definition for ∑_{k=0}^{n} k^2
-/
def triangle_of_squares : Nat → Nat
 | 0    => 0
 | n + 1 => triangle_of_squares n + (n + 1) * (n + 1)

/-
Proving ∑_{k=0}^{n} k^2 = n(n+1)(2n+1)/6
-/
theorem sum_of_squares_formula (n : Nat) : triangle_of_squares n = n * (n + 1) * (2 * n + 1) / 6 := by
        induction n with
        | zero =>
                simp [triangle_of_squares]
        | succ n ih =>
                sorry -- I love this keyword!
