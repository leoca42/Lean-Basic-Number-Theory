import Basicnumbertheory
import Mathlib.Tactic.Ring
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

/-
theorem odd_squared_is_odd (n : Nat) (h : OddO n) : OddO (n * n) := by
        rcases h with ⟨k, hk⟩
        refine ⟨k * (2 * k + 2), ?_⟩
        /-
        n * n = (2 * k + 1) * (2 * k + 1)
                = 4 * k * k + 4 * k + 1
                = 2 * (2 * k * k + 2 * k) + 1
                = 2 * (k * (2 * k + 2)) + 1
        -/
        calc
        n * n
            = (2 * k + 1) * (2 * k + 1) := by simp [hk]
        _   = (2 * k) * (2 * k + 1) + 1 * (2 * k + 1) := by
                -- (a + b) * c = a*c + b*c
                simp [Nat.add_mul]
        _   = ((2 * k) * (2 * k) + (2 * k) * 1) + (1 * (2 * k) + 1 * 1) := by
                -- a*(b + c) = a*b + a*c
                simp [Nat.mul_add, Nat.add_assoc]
        _   = (2 * k) * (2 * k) + (2 * k) + (2 * k) + 1 := by
                -- simplify 1-multiplications and flatten additions
                simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _   = 2 * (k * (2 * k)) + (2 * k) + (2 * k) + 1 := by
                -- reassociate (2*k)*(2*k) = 2*(k*(2*k))
                have h1 : (2 * k) * (2 * k) = 2 * (k * (2 * k)) := by
                  rw [Nat.mul_assoc, Nat.mul_comm k, Nat.mul_assoc]
                rw [h1]
        _   = 2 * (k * (2 * k)) + 2 * (2 * k) + 1 := by
                -- combine like terms: (2*k) + (2*k) = 2*(2*k)
                have h2 : (2 * k) + (2 * k) = 2 * (2 * k) := by
                  rw [← Nat.two_mul]
                simp [h2, Nat.add_assoc]
        _   = 2 * (k * (2 * k) + 2 * k) + 1 := by
                -- factor out 2
                simp [Nat.mul_add, Nat.add_assoc]
        _   = 2 * (k * (2 * k + 2)) + 1 := by
                -- distribute k over (2*k + 2)
                simp [Nat.mul_add, Nat.add_assoc]
-/


theorem odd_sq_is_odd_alt (n : Nat) (h : OddO n) : OddO (n * n) := by
        rcases h with ⟨k, hk⟩
        refine ⟨k * (2 * k + 2), ?_⟩
        rw [hk]
        ring


def triangle : Nat → Nat
 | 0     => 0
 | n + 1 => triangle n + (n + 1)




theorem triangle_numbers (n : Nat) : triangle n = n * (n + 1) / 2 := by
        induction n with
        | zero =>
                simp [triangle]
        | succ n ih =>
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
                        ring
                rw [h3]
                have h4 : (n + 2) = ((n + 1) + 1) := by
                        simp
                rw [h4]

                /-
                triangle (n + 1) = triangle n + (n + 1)
                                 = n * (n + 1) / 2 + (n + 1) by ih
                                 = (n * (n + 1) + 2 * (n + 1)) / 2
                                 = ((n + 2) * (n + 1)) / 2
                                 = ((n + 1) * ((n + 1) + 1)) / 2
                which is the ih in the succ case
                -/
