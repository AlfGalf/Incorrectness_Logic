import algebra
import data.real.basic
import data.vector
import tactic.explode
import tactic.find
import tactic.induction
import tactic.linarith
import tactic.rcases
import tactic.rewrite
import tactic.ring_exp
import tactic.tidy
import tactic.where

namespace IncLoLang

/-! ## State-/

meta def tactic.dec_trivial := `[exact dec_trivial]

def state : Type := string -> ℕ

def state.update : string -> ℕ -> state -> state
| name val s          := (λname', if name' = name then val else s name')

notation s `{` name ` ↦ ` val `}` := state.update name val s

@[simp] lemma update_apply (name : string) (val : ℕ) (s : state) :
  s{name ↦ val} name = val :=
begin
  calc s{name ↦ val} name = (λname', if name' = name then val else s name') name : by refl
       ...                = val : by finish,
end

@[simp] lemma update_apply_ne (name name' : string) (val : ℕ) (s : state) 
  (h : name' ≠ name . tactic.dec_trivial) : 
    s{name ↦ val} name' = s name' :=
begin
  calc s{name ↦ val} name' = (λname', if name' = name then val else s name') name' : by refl
       ...                 = s name' : by finish[h],
end

@[simp] lemma update_override (name : string) (val₁ val₂ : ℕ) (s : state) :
  s{name ↦ val₂}{name ↦ val₁} = s{name ↦ val₁} :=
begin
  apply funext,
  intro name',
  by_cases name' = name; simp [h]
end

/-! ## Language -/

inductive stmt : Type
| skip   : stmt
| assign : string → (state → ℕ) → stmt
| seq    : stmt → stmt → stmt
| error    : stmt
-- | ite    : (state → Prop) → stmt → stmt → stmt
-- | while  : (state → Prop) → stmt → stmt

def eval : option state -> stmt -> option state
| st stmt.skip                  := st
| none (stmt.assign v s)        := none
| (some st) (stmt.assign v s)   := st{v ↦ s st}
| st (stmt.seq n m)             := (eval (eval st n) m)
| st (stmt.error)             := none

infixr ` ;; ` : 90 := stmt.seq

#eval option.bind (eval (some (λ x, 0)) stmt.skip) (λ s, some (s "x"))
#eval option.bind (eval (some (λ x, if x = "y" then 2 else 0)) (stmt.assign "x" (λ s, 1 + s "y"))) 
  (λ s, some (s "x"))
#eval option.bind (eval (some (λ x, if x = "y" then 2 else 0))
  ((stmt.assign "x" (λ s, 1 + s "y")) ;; 
   (stmt.assign "x" (λ s, 1 + s "x")))) (λ s, some (s "x"))

#eval option.bind (eval (none)
  ((stmt.assign "x" (λ s, 1 + s "y")) ;; 
   (stmt.assign "x" (λ s, 1 + s "x")))) (λ s, some (s "x"))
#eval option.bind (eval (some (λ x, 0)) stmt.error) (λ s, some (s "x"))

end IncLoLang