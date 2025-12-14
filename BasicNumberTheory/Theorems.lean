import BasicNumberTheory.Definitions


/-
Format here is ⟨witness, proof⟩
-/
theorem even_two : isEven 2 := ⟨1, rfl⟩

theorem odd_one : isOdd 1 := ⟨0, rfl⟩

theorem every_n_is_even_or_odd (n : Nat) : isEven n ∨ isOdd n :=
  sorry

/-
"sorry" is a placeholder for a proof that hasn't been filled in yet.
Something like this would be good to mark with a TODO comment.
-/
theorem isEven_iff_not_isOdd (n : Int) : isEven n ↔ ¬ isOdd n :=
  sorry
  /-
  Suppose n is even.
  Assume, for contradiction, that n is also odd
  Then there exist k1, k2 : Nat such that
    n = 2 * k1
    n = 2 * k2 + 1
  Thus, 2 * k1 = 2 * k2 + 1
  Rearranging gives 2 * (k1 - k2) = 1
  k1 - k2 is an integer, but 1/2 is not an integer. Contradiction.
  The converse direction is similar.
  -/
theorem isOdd_iff_not_isEven (n : Int) : isOdd n ↔ ¬ isEven n :=
  sorry

theorem even_times_even (m n : Nat)
