def isEven (n : Int) : Prop :=
  ∃ k : Nat, n = 2 * k

def isOdd (n : Int) : Prop :=
  ∃ k : Nat, n = 2 * k + 1

/-
Here, we're using Prop for a propositional definition.
This doesn't allow for computational checking directly,
but it's suitable for formal proofs in Lean.

Below are Boolean versions for computational checks.
-/

def isEvenB (n : Int) : Bool :=
  n % 2 = 0
def isOddB (n : Int) : Bool :=
  n % 2 = 1
