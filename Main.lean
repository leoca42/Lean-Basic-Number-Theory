import BasicNumberTheory

def main : IO Unit :=
  IO.println "Hello, World!"

-- simply checks if the propositions are well-formed
#check isEven 4
#check isOdd 5

example : isEven 2 := ⟨1, rfl⟩
