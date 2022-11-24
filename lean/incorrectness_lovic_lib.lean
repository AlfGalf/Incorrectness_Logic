
/-! # Incorrectness logic library -/

/-! ## Language -/

namespace IncLoLib

def state : Type := string -> ℕ

inductive stmt : Type
| skip   : stmt
| assign : string → (state → ℕ) → stmt
| seq    : stmt → stmt → stmt
-- | ite    : (state → Prop) → stmt → stmt → stmt
-- | while  : (state → Prop) → stmt → stmt

def eval : state -> stmt -> state
| st stmt.skip            := st
| st (stmt.assign v s)    := λ x, if x = v then s st else st v
| st (stmt.seq n m)       := λ x, (eval (eval st n) m) x

infixr ` ;; ` : 90 := stmt.seq

#eval eval (λ x, 0) stmt.skip "x"
#eval eval (λ x, if x = "y" then 2 else 0) (stmt.assign "x" (λ s, 1 + s "y")) "x"
#eval eval (λ x, if x = "y" then 2 else 0) 
  ((stmt.assign "x" (λ s, 1 + s "y")) ;; 
   (stmt.assign "x" (λ s, 1 + s "x"))) "x"

end IncLoLib